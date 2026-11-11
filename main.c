/* PS2 Browser v0.1 - navegador HTTP en modo texto para PS2 (PS2SDK) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <ctype.h>
#include <unistd.h>
#include <tamtypes.h>
#include <kernel.h>
#include <sifrpc.h>
#include <loadfile.h>
#include <iopcontrol.h>
#include <sbv_patches.h>
#include <debug.h>
#include <libpad.h>
#include <netman.h>
#include <ps2ip.h>

extern unsigned char ps2dev9_irx[]; extern unsigned int size_ps2dev9_irx;
extern unsigned char netman_irx[];  extern unsigned int size_netman_irx;
extern unsigned char smap_irx[];    extern unsigned int size_smap_irx;

#define RAW_MAX    (200 * 1024)
#define TEXT_MAX   (160 * 1024)
#define MAX_LINES  6000
#define MAX_LINKS  128
#define URL_MAX    256
#define HIST_MAX   16
#define COLS       74
#define ROWS       24

/* ---------------- estado global ---------------- */
static char raw[RAW_MAX + 1];
static int  rawlen;
static char errmsg[128];

static char text[TEXT_MAX];
static int  tlen;
static int  line_start[MAX_LINES], line_len[MAX_LINES], nlines;
static char links[MAX_LINKS][URL_MAX];
static int  link_off[MAX_LINKS];
static int  nlinks;

static char cur_url[URL_MAX];
static char hist[HIST_MAX][URL_MAX];
static int  hist_n;
static int  scroll_y, sel = -1;
static char my_ip[32] = "sin red";

/* ---------------- pad ---------------- */
static char padbuf[256] __attribute__((aligned(64)));
static u32 prev_btns, hold_cnt;

static void pad_setup(void)
{
    int i;
    padInit(0);
    padPortOpen(0, 0, padbuf);
    for (i = 0; i < 200; i++) {
        if (padGetState(0, 0) == PAD_STATE_STABLE) break;
        usleep(20000);
    }
}

static u32 pad_poll(void)
{
    struct padButtonStatus b;
    u32 now = 0, pressed, dirs;
    const u32 dmask = PAD_UP | PAD_DOWN | PAD_LEFT | PAD_RIGHT;
    int st = padGetState(0, 0);
    if (st == PAD_STATE_STABLE || st == PAD_STATE_FINDCTP1) {
        if (padRead(0, 0, &b) != 0) now = 0xffff ^ b.btns;
    }
    pressed = now & ~prev_btns;
    dirs = now & dmask;
    if (dirs && dirs == (prev_btns & dmask)) {
        hold_cnt++;
        if (hold_cnt > 12 && (hold_cnt % 3) == 0) pressed |= dirs;
    } else {
        hold_cnt = 0;
    }
    prev_btns = now;
    return pressed;
}

static u32 wait_pad(void)
{
    u32 p;
    while (!(p = pad_poll())) usleep(16000);
    return p;
}

/* ---------------- red ---------------- */
static void init_iop(void)
{
    SifInitRpc(0);
    while (!SifIopReset("", 0)) {}
    while (!SifIopSync()) {}
    SifInitRpc(0);
    sbv_patch_enable_lmb();
    sbv_patch_disable_prefix_check();
    SifLoadModule("rom0:SIO2MAN", 0, NULL);
    SifLoadModule("rom0:PADMAN", 0, NULL);
    SifExecModuleBuffer(ps2dev9_irx, size_ps2dev9_irx, 0, NULL, NULL);
    SifExecModuleBuffer(netman_irx, size_netman_irx, 0, NULL, NULL);
    SifExecModuleBuffer(smap_irx, size_smap_irx, 0, NULL, NULL);
}

static int net_init(void)
{
    struct ip4_addr ip, nm, gw;
    t_ip_info info;
    int i;

    IP4_ADDR(&ip, 0, 0, 0, 0);
    IP4_ADDR(&nm, 0, 0, 0, 0);
    IP4_ADDR(&gw, 0, 0, 0, 0);

    if (NetManInit() < 0) return 0;
    ps2ipInit(&ip, &nm, &gw);

    if (ps2ip_getconfig("sm0", &info) >= 0 && !info.dhcp_enabled) {
        info.dhcp_enabled = 1;
        ps2ip_setconfig(&info);
    }
    for (i = 0; i < 400; i++) {
        if (ps2ip_getconfig("sm0", &info) >= 0 && info.dhcp_status == DHCP_STATE_BOUND) {
            u8 *b = (u8 *)&info.ipaddr.s_addr;
            snprintf(my_ip, sizeof my_ip, "%d.%d.%d.%d", b[0], b[1], b[2], b[3]);
            return 1;
        }
        usleep(50000);
    }
    return 0;
}

static int parse_ip(const char *s, struct in_addr *out)
{
    unsigned char b[4];
    int i, v;
    for (i = 0; i < 4; i++) {
        if (!isdigit((unsigned char)*s)) return 0;
        v = 0;
        while (isdigit((unsigned char)*s)) { v = v * 10 + (*s - '0'); if (v > 255) return 0; s++; }
        b[i] = (unsigned char)v;
        if (i < 3) { if (*s != '.') return 0; s++; }
    }
    if (*s) return 0;
    memcpy(out, b, 4);
    return 1;
}

static int dns_skip_name(const unsigned char *r, int rl, int p)
{
    while (p < rl) {
        int c = r[p];
        if (c == 0) return p + 1;
        if ((c & 0xC0) == 0xC0) return p + 2;
        p += c + 1;
    }
    return rl;
}

static int dns_query(const char *host, const char *server, struct in_addr *out)
{
    unsigned char q[300], r[512];
    struct sockaddr_in sa;
    const char *p;
    int n = 12, s, rl, to = 3000, qd, an, i, type, rdlen, pos;

    memset(q, 0, sizeof q);
    q[0] = 0x12; q[1] = 0x34; q[2] = 0x01; q[5] = 1;
    p = host;
    while (*p) {
        const char *d = strchr(p, '.');
        int l = d ? (int)(d - p) : (int)strlen(p);
        if (l <= 0 || l > 63) return 0;
        q[n++] = (unsigned char)l;
        memcpy(q + n, p, l); n += l;
        p += l;
        if (*p == '.') p++;
    }
    q[n++] = 0; q[n++] = 0; q[n++] = 1; q[n++] = 0; q[n++] = 1;

    memset(&sa, 0, sizeof sa);
    sa.sin_family = AF_INET;
    sa.sin_port = htons(53);
    if (!parse_ip(server, &sa.sin_addr)) return 0;

    s = lwip_socket(AF_INET, SOCK_DGRAM, 0);
    if (s < 0) return 0;
    lwip_setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &to, sizeof to);
    lwip_sendto(s, q, n, 0, (struct sockaddr *)&sa, sizeof sa);
    rl = lwip_recv(s, r, sizeof r, 0);
    lwip_close(s);

    if (rl < 12 || r[0] != 0x12 || r[1] != 0x34 || (r[3] & 15) != 0) return 0;
    qd = (r[4] << 8) | r[5];
    an = (r[6] << 8) | r[7];
    pos = 12;
    for (i = 0; i < qd; i++) pos = dns_skip_name(r, rl, pos) + 4;
    for (i = 0; i < an && pos + 10 <= rl; i++) {
        pos = dns_skip_name(r, rl, pos);
        if (pos + 10 > rl) break;
        type = (r[pos] << 8) | r[pos + 1];
        rdlen = (r[pos + 8] << 8) | r[pos + 9];
        pos += 10;
        if (type == 1 && rdlen == 4 && pos + 4 <= rl) { memcpy(out, r + pos, 4); return 1; }
        pos += rdlen;
    }
    return 0;
}

static int resolve_host(const char *host, struct in_addr *out)
{
    if (parse_ip(host, out)) return 1;
    if (dns_query(host, "8.8.8.8", out)) return 1;
    if (dns_query(host, "1.1.1.1", out)) return 1;
    return 0;
}

static int http_get(const char *url)
{
    char host[128], path[200], req[512];
    int port = 80, hn = 0, s, n;
    const char *p;
    struct sockaddr_in sa;
    int to = 10000;

    if (strncasecmp(url, "http://", 7)) {
        snprintf(errmsg, sizeof errmsg, "Solo HTTP por ahora (sin HTTPS)");
        return -1;
    }
    p = url + 7;
    while (*p && *p != '/' && *p != ':' && hn < 127) host[hn++] = *p++;
    host[hn] = 0;
    if (*p == ':') { port = atoi(p + 1); while (*p && *p != '/') p++; }
    if (*p == '/') snprintf(path, sizeof path, "%s", p); else strcpy(path, "/");
    if (!hn) { snprintf(errmsg, sizeof errmsg, "URL invalida"); return -1; }

    memset(&sa, 0, sizeof sa);
    sa.sin_family = AF_INET;
    sa.sin_port = htons(port);
    if (!resolve_host(host, &sa.sin_addr)) {
        snprintf(errmsg, sizeof errmsg, "No se pudo resolver %s", host);
        return -1;
    }
    s = lwip_socket(AF_INET, SOCK_STREAM, 0);
    if (s < 0) { snprintf(errmsg, sizeof errmsg, "Error de socket"); return -1; }
    lwip_setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &to, sizeof to);
    if (lwip_connect(s, (struct sockaddr *)&sa, sizeof sa) < 0) {
        lwip_close(s);
        snprintf(errmsg, sizeof errmsg, "No conecta con %s", host);
        return -1;
    }
    snprintf(req, sizeof req,
             "GET %s HTTP/1.0\r\nHost: %s\r\nUser-Agent: PS2Browser/0.1\r\n"
             "Accept: text/html,text/plain\r\nConnection: close\r\n\r\n", path, host);
    lwip_send(s, req, strlen(req), 0);

    rawlen = 0;
    while (rawlen < RAW_MAX) {
        n = lwip_recv(s, raw + rawlen, RAW_MAX - rawlen, 0);
        if (n <= 0) break;
        rawlen += n;
    }
    lwip_close(s);
    raw[rawlen] = 0;
    if (rawlen == 0) { snprintf(errmsg, sizeof errmsg, "Respuesta vacia"); return -1; }
    return rawlen;
}

/* ---------------- URLs ---------------- */
static void resolve_url(const char *base, const char *href, char *out)
{
    const char *p, *q;
    char tmp[URL_MAX];
    int olen;

    if (!strncasecmp(href, "http://", 7) || !strncasecmp(href, "https://", 8)) {
        snprintf(out, URL_MAX, "%s", href); return;
    }
    if (href[0] == '/' && href[1] == '/') { snprintf(out, URL_MAX, "http:%s", href); return; }
    p = base + (!strncasecmp(base, "https://", 8) ? 8 : 7);
    q = strchr(p, '/');
    olen = q ? (int)(q - base) : (int)strlen(base);
    if (href[0] == '/') { snprintf(out, URL_MAX, "%.*s%s", olen, base, href); return; }
    snprintf(tmp, sizeof tmp, "%s", base);
    q = strchr(tmp + olen, '?');
    if (q) tmp[q - tmp] = 0;
    q = strrchr(tmp + olen, '/');
    if (!q) snprintf(out, URL_MAX, "%.*s/%s", olen, base, href);
    else snprintf(out, URL_MAX, "%.*s%s", (int)(q - tmp) + 1, tmp, href);
}

/* ---------------- HTML -> texto ---------------- */
static int pending_space, at_line_start, nlcount, pend_link;

static void put(char c)
{
    if (tlen < TEXT_MAX - 2) text[tlen++] = c;
}

static void emit_char(char c)
{
    if (c == ' ' || c == '\n' || c == '\r' || c == '\t') { pending_space = 1; return; }
    if (pending_space && !at_line_start) put(' ');
    pending_space = 0;
    put(c);
    at_line_start = 0;
    nlcount = 0;
}

static void emit_str(const char *s) { while (*s) emit_char(*s++); }

static void emit_nl(int n)
{
    pending_space = 0;
    if (tlen == 0) return;
    if (!at_line_start) { put('\n'); at_line_start = 1; nlcount = 1; }
    if (n > 1 && nlcount < 2) { put('\n'); nlcount = 2; }
}

static int get_attr(const char *s, int len, const char *name, char *out, int osz)
{
    int nlen = strlen(name), i, p, o;
    char q, d;
    for (i = 0; i + nlen < len; i++) {
        if ((i == 0 || isspace((unsigned char)s[i - 1])) && !strncasecmp(s + i, name, nlen)) {
            p = i + nlen;
            while (p < len && isspace((unsigned char)s[p])) p++;
            if (p >= len || s[p] != '=') continue;
            p++;
            while (p < len && isspace((unsigned char)s[p])) p++;
            q = 0;
            if (p < len && (s[p] == '"' || s[p] == '\'')) { q = s[p]; p++; }
            o = 0;
            while (p < len && o < osz - 1) {
                d = s[p];
                if (q) { if (d == q) break; } else if (isspace((unsigned char)d)) break;
                out[o++] = d; p++;
            }
            out[o] = 0;
            return 1;
        }
    }
    return 0;
}

static int skip_until_ci(const char *h, int from, int hl, const char *pat)
{
    int pl = strlen(pat), i;
    for (i = from; i + pl <= hl; i++)
        if (!strncasecmp(h + i, pat, pl)) return i;
    return hl;
}

static void entity(const char *h, int *pi, int hl)
{
    int i = *pi, j = i + 1, code = -1;
    char name[10];
    int n = 0;
    while (j < hl && h[j] != ';' && n < 9 && h[j] != ' ' && h[j] != '<') name[n++] = h[j++];
    name[n] = 0;
    if (j < hl && h[j] == ';') {
        if (!strcmp(name, "amp")) code = '&';
        else if (!strcmp(name, "lt")) code = '<';
        else if (!strcmp(name, "gt")) code = '>';
        else if (!strcmp(name, "quot")) code = '"';
        else if (!strcmp(name, "apos")) code = '\'';
        else if (!strcmp(name, "nbsp")) code = ' ';
        else if (name[0] == '#') {
            long v = (name[1] == 'x' || name[1] == 'X') ? strtol(name + 2, NULL, 16) : strtol(name + 1, NULL, 10);
            code = (v > 0 && v < 128) ? (int)v : '?';
        }
    }
    if (code >= 0) { emit_char((char)code); *pi = j + 1; }
    else { emit_char('&'); *pi = i + 1; }
}

static void html_to_text(const char *h, int hl, int is_html)
{
    int i = 0;
    tlen = 0; nlinks = 0;
    pending_space = 0; at_line_start = 1; nlcount = 0; pend_link = 0;

    if (!is_html) {
        for (i = 0; i < hl && tlen < TEXT_MAX - 2; i++) {
            unsigned char c = h[i];
            if (c == '\r') continue;
            if (c == '\t') c = ' ';
            if (c != '\n' && (c < 32 || c > 126)) c = '?';
            text[tlen++] = c;
        }
        return;
    }

    while (i < hl && tlen < TEXT_MAX - 8) {
        unsigned char c = h[i];
        if (c == '<') {
            int j, k, closing = 0, nl = 0;
            char name[16], q = 0;
            if (!strncmp(h + i, "<!--", 4)) {
                const char *e = strstr(h + i + 4, "-->");
                i = e ? (int)(e - h) + 3 : hl;
                continue;
            }
            j = i + 1;
            if (j < hl && h[j] == '/') { closing = 1; j++; }
            while (j < hl && isalnum((unsigned char)h[j]) && nl < 15) name[nl++] = tolower((unsigned char)h[j++]);
            name[nl] = 0;
            if (nl == 0 && !(i + 1 < hl && (h[i + 1] == '!' || h[i + 1] == '?'))) {
                emit_char('<'); i++; continue;
            }
            k = j;
            while (k < hl) {
                char d = h[k];
                if (q) { if (d == q) q = 0; }
                else if (d == '"' || d == '\'') q = d;
                else if (d == '>') break;
                k++;
            }
            if (!closing && (!strcmp(name, "script") || !strcmp(name, "style"))) {
                i = skip_until_ci(h, k, hl, strcmp(name, "script") ? "</style" : "</script");
                continue;
            }
            if (!strcmp(name, "a")) {
                if (!closing) {
                    char href[URL_MAX];
                    if (get_attr(h + j, k - j, "href", href, sizeof href) && nlinks < MAX_LINKS &&
                        href[0] && href[0] != '#' && strncasecmp(href, "javascript:", 11) &&
                        strncasecmp(href, "mailto:", 7)) {
                        snprintf(links[nlinks], URL_MAX, "%s", href);
                        nlinks++;
                        pend_link = nlinks;
                    }
                } else if (pend_link) {
                    char mk[12];
                    snprintf(mk, sizeof mk, "[%d]", pend_link);
                    emit_str(mk);
                    link_off[pend_link - 1] = tlen;
                    pend_link = 0;
                }
            } else if (!strcmp(name, "br") || !strcmp(name, "div") || !strcmp(name, "tr") ||
                       !strcmp(name, "section") || !strcmp(name, "article") || !strcmp(name, "header") ||
                       !strcmp(name, "footer") || !strcmp(name, "nav") || !strcmp(name, "form")) {
                emit_nl(1);
            } else if (!strcmp(name, "p") || !strcmp(name, "table") || !strcmp(name, "ul") ||
                       !strcmp(name, "ol") || !strcmp(name, "blockquote") || !strcmp(name, "pre") ||
                       (name[0] == 'h' && name[1] >= '1' && name[1] <= '6' && !name[2])) {
                emit_nl(2);
            } else if (!strcmp(name, "li")) {
                if (!closing) { emit_nl(1); emit_char('*'); pending_space = 1; }
            } else if (!strcmp(name, "hr")) {
                emit_nl(1); emit_str("----------------"); emit_nl(1);
            } else if (!strcmp(name, "td") || !strcmp(name, "th")) {
                pending_space = 1;
            }
            i = k + 1;
            continue;
        }
        if (c == '&') { entity(h, &i, hl); continue; }
        if (c >= 0xC0) { emit_char('?'); i++; continue; }
        if (c >= 0x80) { i++; continue; }
        emit_char(c);
        i++;
    }
    if (tlen > 0 && text[tlen - 1] != '\n') put('\n');
}

static void layout(void)
{
    int i = 0, s, col, lastsp;
    nlines = 0;
    while (i < tlen && nlines < MAX_LINES) {
        s = i; col = 0; lastsp = -1;
        while (i < tlen && text[i] != '\n') {
            if (text[i] == ' ') lastsp = i;
            col++; i++;
            if (col >= COLS && i < tlen && text[i] != '\n') {
                if (lastsp > s) i = lastsp;
                break;
            }
        }
        line_start[nlines] = s;
        line_len[nlines] = i - s;
        nlines++;
        if (i < tlen && (text[i] == '\n' || text[i] == ' ')) i++;
    }
    if (nlines == 0) { line_start[0] = 0; line_len[0] = 0; nlines = 1; }
}

/* ---------------- carga de pagina ---------------- */
static int header_value(const char *name, char *out, int osz)
{
    int nl = strlen(name);
    char *he = strstr(raw, "\r\n\r\n");
    char *p = raw, *e;
    int o = 0;
    if (!he) he = raw + rawlen;
    while (p < he) {
        p = strchr(p, '\n');
        if (!p || p >= he) break;
        p++;
        if (!strncasecmp(p, name, nl) && p[nl] == ':') {
            p += nl + 1;
            while (*p == ' ') p++;
            e = p;
            while (*e && *e != '\r' && *e != '\n' && o < osz - 1) out[o++] = *e++;
            out[o] = 0;
            return 1;
        }
    }
    return 0;
}

static void show_loading(const char *url)
{
    scr_setXY(0, 1);
    scr_printf("  %-74.74s\n", "Cargando...");
    scr_printf("  %-74.74s\n", url);
}

static int load_page(const char *url)
{
    char u[URL_MAX], loc[URL_MAX], absu[URL_MAX];
    int redir, code, is_html;
    char *body;

    snprintf(u, sizeof u, "%s", url);
    for (redir = 0; redir < 5; redir++) {
        show_loading(u);
        if (http_get(u) < 0) return -1;
        code = 0;
        if (!strncmp(raw, "HTTP/", 5) && raw[8] == ' ') code = atoi(raw + 9);
        if (code >= 300 && code < 400) {
            if (!header_value("location", loc, sizeof loc)) {
                snprintf(errmsg, sizeof errmsg, "Redireccion sin destino");
                return -1;
            }
            resolve_url(u, loc, absu);
            snprintf(u, sizeof u, "%s", absu);
            continue;
        }
        body = strstr(raw, "\r\n\r\n");
        if (body) body += 4;
        else if ((body = strstr(raw, "\n\n"))) body += 2;
        else body = raw;
        is_html = 0;
        {
            int bl = raw + rawlen - body, scan = bl > 1024 ? 1024 : bl, k;
            for (k = 0; k < scan; k++)
                if (body[k] == '<' && (!strncasecmp(body + k, "<html", 5) || !strncasecmp(body + k, "<!doctype", 9) ||
                                       !strncasecmp(body + k, "<head", 5) || !strncasecmp(body + k, "<body", 5) ||
                                       !strncasecmp(body + k, "<title", 6) || !strncasecmp(body + k, "<p", 2) ||
                                       !strncasecmp(body + k, "<h1", 3))) { is_html = 1; break; }
            html_to_text(body, bl, is_html);
        }
        layout();
        snprintf(cur_url, sizeof cur_url, "%s", u);
        if (redir == 5) return -1;
        return 0;
    }
    snprintf(errmsg, sizeof errmsg, "Demasiadas redirecciones");
    return -1;
}

static void show_error(void)
{
    scr_setXY(0, 1);
    scr_printf("  %-74.74s\n", "Error:");
    scr_printf("  %-74.74s\n", errmsg);
    scr_printf("  %-74.74s\n", "Pulsa X para continuar");
    while (!(wait_pad() & PAD_CROSS)) {}
}

static int navigate(const char *url, int push)
{
    char prev[URL_MAX], target[URL_MAX];
    snprintf(prev, sizeof prev, "%s", cur_url);
    snprintf(target, sizeof target, "%s", url);
    if (load_page(target) == 0) {
        if (push && prev[0]) {
            if (hist_n == HIST_MAX) { memmove(hist[0], hist[1], (HIST_MAX - 1) * URL_MAX); hist_n--; }
            snprintf(hist[hist_n++], URL_MAX, "%s", prev);
        }
        scroll_y = 0; sel = -1;
        return 1;
    }
    show_error();
    return 0;
}

/* ---------------- pantallas ---------------- */
static void blank_rows(int n)
{
    while (n-- > 0) scr_printf("  %-74.74s\n", "");
}

static void draw_page(void)
{
    char buf[256], st[256];
    int r, li, n, last;
    scr_setXY(0, 1);
    scr_printf("  %-74.74s\n", cur_url);
    for (r = 0; r < ROWS; r++) {
        li = scroll_y + r;
        if (li < nlines) {
            n = line_len[li]; if (n > COLS) n = COLS;
            memcpy(buf, text + line_start[li], n);
            buf[n] = 0;
        } else buf[0] = 0;
        scr_printf("  %-74.74s\n", buf);
    }
    last = scroll_y + ROWS; if (last > nlines) last = nlines;
    if (sel >= 0) {
        char ab[URL_MAX];
        resolve_url(cur_url, links[sel], ab);
        snprintf(st, sizeof st, "L%d-%d/%d  [%d/%d] %s", scroll_y + 1, last, nlines, sel + 1, nlinks, ab);
    } else {
        snprintf(st, sizeof st, "L%d-%d/%d  enlaces: %d", scroll_y + 1, last, nlines, nlinks);
    }
    scr_printf("  %-74.74s\n", st);
    scr_printf("  %-74.74s\n", "^v scroll  <> enlace  X abrir  O atras  L1/R1 pag  START menu  SELECT recargar");
}

static const char *bm_name[] = { "Example.com", "CERN (primera web)", "NeverSSL", "Escribir URL..." };
static const char *bm_url[]  = { "http://example.com/", "http://info.cern.ch/", "http://neverssl.com/", NULL };
#define BM_N 4

static void draw_menu(int msel)
{
    int i;
    scr_setXY(0, 1);
    scr_printf("  %-74.74s\n", "PS2 Browser v0.1");
    {
        char b[64];
        snprintf(b, sizeof b, "IP: %s", my_ip);
        scr_printf("  %-74.74s\n", b);
    }
    blank_rows(1);
    for (i = 0; i < BM_N; i++) {
        char b[96];
        snprintf(b, sizeof b, "%c %s", i == msel ? '>' : ' ', bm_name[i]);
        scr_printf("  %-74.74s\n", b);
    }
    blank_rows(2);
    scr_printf("  %-74.74s\n", "^v elegir   X abrir   O volver a la pagina");
    scr_printf("  %-74.74s\n", "Solo webs HTTP (sin HTTPS todavia).");
    blank_rows(ROWS - 6);
}

static int url_editor(char *out)
{
    static const char cs[] = "abcdefghijklmnopqrstuvwxyz0123456789./:-_?=&%#~+@!ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    int ci = 0, n = (int)strlen(cs), len;
    char buf[URL_MAX];
    u32 p;

    snprintf(buf, sizeof buf, "http://");
    len = strlen(buf);
    for (;;) {
        char line[URL_MAX + 4];
        scr_setXY(0, 1);
        scr_printf("  %-74.74s\n", "Escribir URL");
        snprintf(line, sizeof line, "%s%c", buf, cs[ci]);
        scr_printf("  %-74.74s\n", line);
        blank_rows(1);
        scr_printf("  %-74.74s\n", "^v letra   L1/R1 +-10   > anadir   < borrar   X ir   O cancelar");
        blank_rows(ROWS - 2);
        p = wait_pad();
        if (p & PAD_UP) ci = (ci + 1) % n;
        if (p & PAD_DOWN) ci = (ci + n - 1) % n;
        if (p & PAD_R1) ci = (ci + 10) % n;
        if (p & PAD_L1) ci = (ci + n - 10) % n;
        if ((p & PAD_RIGHT) && len < URL_MAX - 2) { buf[len++] = cs[ci]; buf[len] = 0; }
        if ((p & PAD_LEFT) && len > 7) buf[--len] = 0;
        if (p & PAD_CROSS) { snprintf(out, URL_MAX, "%s", buf); return 1; }
        if (p & PAD_CIRCLE) return 0;
    }
}

static void select_link(int s)
{
    int i, ln = 0, off;
    if (s < 0 || s >= nlinks) return;
    sel = s;
    off = link_off[s];
    for (i = 0; i < nlines; i++) {
        if (off <= line_start[i] + line_len[i]) { ln = i; break; }
    }
    if (ln < scroll_y || ln >= scroll_y + ROWS) {
        scroll_y = ln - ROWS / 2;
        if (scroll_y < 0) scroll_y = 0;
    }
}

enum { M_MENU, M_PAGE };

int main(void)
{
    int mode = M_MENU, msel = 0, redraw = 1, max_scroll;
    u32 p;

    init_iop();
    init_scr();
    scr_printf("\n  PS2 Browser v0.1\n  Iniciando red (DHCP)...\n");
    pad_setup();
    if (!net_init()) scr_printf("  Sin red. Conecta el adaptador de red y reinicia.\n");

    for (;;) {
        p = pad_poll();
        if (mode == M_MENU) {
            if (redraw) { draw_menu(msel); redraw = 0; }
            if (p & PAD_UP)   { msel = (msel + BM_N - 1) % BM_N; redraw = 1; }
            if (p & PAD_DOWN) { msel = (msel + 1) % BM_N; redraw = 1; }
            if (p & PAD_CIRCLE) { if (cur_url[0]) { mode = M_PAGE; redraw = 1; } }
            if (p & PAD_CROSS) {
                char url[URL_MAX];
                if (bm_url[msel]) {
                    if (navigate(bm_url[msel], 1)) mode = M_PAGE;
                } else if (url_editor(url)) {
                    if (navigate(url, 1)) mode = M_PAGE;
                }
                redraw = 1;
            }
        } else {
            max_scroll = nlines - ROWS; if (max_scroll < 0) max_scroll = 0;
            if (redraw) { draw_page(); redraw = 0; }
            if (p & PAD_DOWN) { if (scroll_y < max_scroll) { scroll_y++; redraw = 1; } }
            if (p & PAD_UP)   { if (scroll_y > 0) { scroll_y--; redraw = 1; } }
            if (p & PAD_R1)   { scroll_y += ROWS - 2; if (scroll_y > max_scroll) scroll_y = max_scroll; redraw = 1; }
            if (p & PAD_L1)   { scroll_y -= ROWS - 2; if (scroll_y < 0) scroll_y = 0; redraw = 1; }
            if (p & PAD_RIGHT) { select_link(sel < 0 ? 0 : (sel + 1 < nlinks ? sel + 1 : sel)); redraw = 1; }
            if (p & PAD_LEFT)  { select_link(sel <= 0 ? 0 : sel - 1); redraw = 1; }
            if ((p & PAD_CROSS) && sel >= 0) {
                char ab[URL_MAX];
                resolve_url(cur_url, links[sel], ab);
                navigate(ab, 1);
                redraw = 1;
            }
            if (p & PAD_CIRCLE) {
                if (hist_n > 0) { navigate(hist[--hist_n], 0); }
                else mode = M_MENU;
                redraw = 1;
            }
            if (p & PAD_SELECT) { char c[URL_MAX]; snprintf(c, sizeof c, "%s", cur_url); navigate(c, 0); redraw = 1; }
            if (p & PAD_START) { mode = M_MENU; redraw = 1; }
        }
        usleep(16000);
    }
    return 0;
}
