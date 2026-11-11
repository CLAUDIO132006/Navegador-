/*
 * PS2 Browser v2 - gsKit + imagenes + video en RAM
 *
 * Todo pasa por proxy.py (corre en tu PC/Raspberry):
 *   /p?u=URL      pagina simplificada (HTML liviano, HTTPS resuelto por el proxy)
 *   /img?u=URL    imagen JPEG 256x192
 *   /vid?u=URL    video MJPEG 256x192 en streaming (sin audio)
 *   /search /isearch /vsearch   buscar web / fotos / videos
 *
 * - Paginas HTML se guardan en la USB: mass:/DVD/<hash>.html
 * - Imagenes y video viven SOLO en RAM (nada se escribe en la USB)
 * - Video: buffer circular de 6 MB, se decodifica frame a frame
 *
 * Controles (navegador):
 *   Arriba/Abajo scroll | L1/R1 link | X abrir | Circulo atras
 *   Triangulo URL | Cuadrado buscar web | L2 fotos | R2 videos
 *   Start recargar | Select inicio
 * Imagen/Video: Circulo para salir
 */
#include <kernel.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <malloc.h>
#include <setjmp.h>
#include <errno.h>
#include <ctype.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sifrpc.h>
#include <loadfile.h>
#include <iopcontrol.h>
#include <sbv_patches.h>
#include <libpad.h>
#include <netman.h>
#include <ps2ip.h>
#include <netdb.h>
#include <gsKit.h>
#include <dmaKit.h>
#include <gsFontM.h>
#include <jpeglib.h>

/* ======== CONFIGURACION: cambia esto ======== */
#define PROXY       "http://192.168.1.50:8080"
/* ============================================ */

#define HOME_URL    PROXY "/"
#define CACHE_DIR   "mass:/DVD"
#define MAX_PAGE    (256 * 1024)
#define MAX_IMG     (400 * 1024)
#define VBUF_SIZE   (6 * 1024 * 1024)
#define VBUF_PRE    (512 * 1024)
#define MAX_FRAME   (120 * 1024)
#define TEX_W       256
#define TEX_H       192
#define MAX_LINES   3000
#define COLS        78
#define MAX_LINKS   200
#define URL_LEN     320
#define MAX_HIST    16
#define DHCP_BOUND_STATE 10

/* Ajusta si el texto sale muy grande/chico */
#define FONT_SCALE  0.5f
#define LINE_H      14
#define CHAR_W      8

#define RGBA(r,g,b) GS_SETREG_RGBAQ(r,g,b,0x80,0x00)
#define C_WHITE  RGBA(0xE8,0xE8,0xE8)
#define C_YELLOW RGBA(0xFF,0xE0,0x30)
#define C_CYAN   RGBA(0x40,0xD0,0xFF)
#define C_GRAY   RGBA(0x90,0x90,0x90)
#define C_BG     GS_SETREG_RGBAQ(0x10,0x10,0x20,0x00,0x00)

#define IRX(n) extern unsigned char n##_irx[]; extern unsigned int size_##n##_irx;
IRX(ps2dev9) IRX(netman) IRX(smap) IRX(usbd) IRX(bdm) IRX(bdmfs_fatfs) IRX(usbmass_bd)

static void load_irx(void *buf, unsigned int size)
{
    int ret;
    SifExecModuleBuffer(buf, size, 0, NULL, &ret);
}

/* ================= graficos ================= */
static GSGLOBAL *gs;
static GSFONTM  *font;
static GSTEXTURE tex;
static int hz = 60;

static void gfx_init(void)
{
    gs = gsKit_init_global();
    gs->PSM = GS_PSM_CT24;
    gs->PSMZ = GS_PSMZ_16S;
    gs->ZBuffering = GS_SETTING_OFF;
    gs->DoubleBuffering = GS_SETTING_ON;
    gs->PrimAlphaEnable = GS_SETTING_ON;

    dmaKit_init(D_CTRL_RELE_OFF, D_CTRL_MFD_OFF, D_CTRL_STS_UNSPEC,
                D_CTRL_STD_OFF, D_CTRL_RCYC_8, 1 << DMA_CHANNEL_GIF);
    dmaKit_chan_init(DMA_CHANNEL_GIF);

    gsKit_init_screen(gs);
    gsKit_mode_switch(gs, GS_ONESHOT);
    hz = (gs->Mode == GS_MODE_PAL) ? 50 : 60;

    font = gsKit_init_fontm();
    gsKit_fontm_upload(gs, font);

    memset(&tex, 0, sizeof(tex));
    tex.Width = TEX_W;
    tex.Height = TEX_H;
    tex.PSM = GS_PSM_CT32;
    tex.Filter = GS_FILTER_LINEAR;
    tex.Mem = memalign(128, gsKit_texture_size_ee(TEX_W, TEX_H, GS_PSM_CT32));
    tex.Vram = gsKit_vram_alloc(gs, gsKit_texture_size(TEX_W, TEX_H, GS_PSM_CT32),
                                GSKIT_ALLOC_USERBUFFER);
    memset(tex.Mem, 0, TEX_W * TEX_H * 4);
}

static void begin_frame(void) { gsKit_clear(gs, C_BG); }
static void end_frame(void)   { gsKit_queue_exec(gs); gsKit_sync_flip(gs); }

static void text(float x, float y, u64 color, const char *s)
{
    gsKit_fontm_print_scaled(gs, font, x, y, 3, FONT_SCALE, color, s);
}

static void draw_msg(const char *m)
{
    begin_frame();
    text(16, 40, C_WHITE, m);
    end_frame();
}

static void draw_tex_fullscreen(void)
{
    float h = (float)gs->Height - 40;
    float w = h * 4.0f / 3.0f;
    float x = ((float)gs->Width - w) / 2.0f;
    gsKit_prim_sprite_texture(gs, &tex, x, 20, 0, 0, x + w, 20 + h, TEX_W, TEX_H,
                              2, GS_SETREG_RGBAQ(0x80, 0x80, 0x80, 0x80, 0x00));
}

/* ================= pad ================= */
static char padbuf[256] __attribute__((aligned(64)));
static unsigned int btn_old;
static int hold;

static unsigned int input(void)
{
    struct padButtonStatus b;
    unsigned int n = 0;
    if (padRead(0, 0, &b)) n = 0xffff ^ b.btns;
    unsigned int p = n & ~btn_old;
    if (n && n == btn_old) {
        if (++hold > 20 && (hold % 4) == 0)
            p = n & (PAD_UP | PAD_DOWN | PAD_LEFT | PAD_RIGHT);
    } else hold = 0;
    btn_old = n;
    return p;
}

/* ================= teclado en pantalla ================= */
static const char CHARSET[] =
    "abcdefghijklmnopqrstuvwxyz0123456789:/.-_?=&%+#~@ ABCDEFGHIJKLMNOPQRSTUVWXYZ";

static int text_input(const char *prompt, char *out, int max)
{
    int len = strlen(out), ci = 0, n = sizeof(CHARSET) - 1;
    for (;;) {
        unsigned int p = input();
        if (p & PAD_RIGHT) ci = (ci + 1) % n;
        if (p & PAD_LEFT)  ci = (ci + n - 1) % n;
        if (p & PAD_R1)    ci = (ci + 10) % n;
        if (p & PAD_L1)    ci = (ci + n - 10) % n;
        if ((p & PAD_CROSS) && len < max - 1) { out[len++] = CHARSET[ci]; out[len] = 0; }
        if ((p & PAD_SQUARE) && len > 0) out[--len] = 0;
        if (p & PAD_START)  return 1;
        if (p & PAD_CIRCLE) return 0;

        char cur[8] = { '[', CHARSET[ci], ']', 0 };
        begin_frame();
        text(16, 20, C_CYAN, prompt);
        for (int i = 0; i < len; i += 70) {
            char seg[72]; int l = len - i > 70 ? 70 : len - i;
            memcpy(seg, out + i, l); seg[l] = 0;
            text(16, 50 + (i / 70) * LINE_H, C_WHITE, seg);
        }
        text(16, 150, C_YELLOW, cur);
        text(16, 200, C_GRAY, "Izq/Der letra | L1/R1 salto de 10 | X agregar");
        text(16, 214, C_GRAY, "Cuadrado borrar | Start aceptar | Circulo cancelar");
        end_frame();
    }
}

/* ================= red ================= */
static void network_init(void)
{
    ip4_addr_t ip, nm, gw;
    t_ip_info info;
    IP4_ADDR(&ip, 0, 0, 0, 0);
    IP4_ADDR(&nm, 0, 0, 0, 0);
    IP4_ADDR(&gw, 0, 0, 0, 0);

    NetManInit();
    ps2ipInit(&ip, &nm, &gw);

    if (ps2ip_getconfig("sm0", &info) > 0 && !info.dhcp_enabled) {
        info.dhcp_enabled = 1;
        ps2ip_setconfig(&info);
    }
    for (int i = 0; i < 300; i++) {
        draw_msg("Esperando DHCP (cable de red conectado?)...");
        if (ps2ip_getconfig("sm0", &info) > 0 && info.dhcp_status == DHCP_BOUND_STATE)
            return;
        usleep(100000);
    }
}

/* ================= utilidades URL ================= */
static char status[80];
static void set_status(const char *s) { snprintf(status, sizeof(status), "%s", s); }

static int parse_url(const char *u, char *host, int *port, char *path)
{
    if (strncmp(u, "http://", 7) != 0) return -1;
    u += 7;
    const char *s = strchr(u, '/');
    int hl = s ? (int)(s - u) : (int)strlen(u);
    char hp[128];
    if (hl <= 0 || hl > 127) return -1;
    memcpy(hp, u, hl); hp[hl] = 0;
    *port = 80;
    char *c = strchr(hp, ':');
    if (c) { *c = 0; *port = atoi(c + 1); }
    strcpy(host, hp);
    if (s && strlen(s) < 600) strcpy(path, s); else strcpy(path, "/");
    return 0;
}

static void url_encode(const char *s, char *out, int max)
{
    static const char *hex = "0123456789ABCDEF";
    int j = 0;
    for (; *s && j < max - 4; s++) {
        unsigned char c = (unsigned char)*s;
        if (isalnum(c) || c == '-' || c == '_' || c == '.' || c == '~') out[j++] = c;
        else { out[j++] = '%'; out[j++] = hex[c >> 4]; out[j++] = hex[c & 15]; }
    }
    out[j] = 0;
}

static void resolve_url(const char *base, const char *href, char *out)
{
    out[0] = 0;
    if (!strncmp(href, "http://", 7)) { snprintf(out, URL_LEN, "%s", href); return; }
    if (href[0] == '#' || !strncmp(href, "javascript:", 11)) return;
    char host[128], path[640]; int port;
    if (parse_url(base, host, &port, path) < 0) return;
    if (href[0] == '/') snprintf(out, URL_LEN, "http://%s:%d%s", host, port, href);
    else {
        char *q = strchr(path, '?'); if (q) *q = 0;
        char *sl = strrchr(path, '/'); if (sl) sl[1] = 0;
        snprintf(out, URL_LEN, "http://%s:%d%s%s", host, port, path, href);
    }
}

static void cache_name(const char *url, char *out)
{
    unsigned long h = 5381;
    for (const char *p = url; *p; p++) h = h * 33 + (unsigned char)*p;
    snprintf(out, 96, CACHE_DIR "/%08lx.html", h);
}

static int ci_prefix(const char *s, const char *pre)
{
    while (*pre) { if ((*s | 32) != (*pre | 32)) return 0; s++; pre++; }
    return 1;
}
static const char *ci_find(const char *h, const char *n)
{
    for (; *h; h++) if (ci_prefix(h, n)) return h;
    return NULL;
}

/* ================= HTTP ================= */
enum { CT_OTHER, CT_HTML, CT_JPEG, CT_VIDEO };
typedef struct { int fd, code, ctype, leftlen; char left[2048]; } http_t;

static int http_open(const char *url, http_t *h)
{
    char host[128], path[640]; int port;
    if (parse_url(url, host, &port, path) < 0) { set_status("URL invalida"); return -1; }
    struct hostent *he = gethostbyname(host);
    if (!he) { set_status("DNS fallo"); return -2; }

    int s = socket(AF_INET, SOCK_STREAM, 0);
    struct sockaddr_in sa;
    memset(&sa, 0, sizeof(sa));
    sa.sin_family = AF_INET;
    sa.sin_port = htons(port);
    memcpy(&sa.sin_addr, he->h_addr_list[0], 4);
    if (connect(s, (struct sockaddr *)&sa, sizeof(sa)) < 0) {
        lwip_close(s); set_status("No conecta al proxy"); return -3;
    }
    char req[900];
    int rl = snprintf(req, sizeof(req),
        "GET %s HTTP/1.0\r\nHost: %s:%d\r\nUser-Agent: PS2Browser/2.0\r\n"
        "Connection: close\r\n\r\n", path, host, port);
    send(s, req, rl, 0);

    char hdr[2048]; int hl = 0, body = -1, n;
    while (hl < (int)sizeof(hdr) - 1 &&
           (n = recv(s, hdr + hl, sizeof(hdr) - 1 - hl, 0)) > 0) {
        hl += n; hdr[hl] = 0;
        char *e = strstr(hdr, "\r\n\r\n");
        if (e) { body = (int)(e - hdr) + 4; break; }
    }
    if (body < 0) { lwip_close(s); set_status("Respuesta invalida"); return -4; }

    h->fd = s;
    h->code = atoi(hdr + 9);
    char ctl[80] = "";
    const char *ct = ci_find(hdr, "\r\nContent-Type:");
    if (ct) {
        ct += 15; while (*ct == ' ') ct++;
        int i = 0; while (*ct && *ct != '\r' && i < 79) ctl[i++] = *ct++;
        ctl[i] = 0;
    }
    if (!ct || ci_prefix(ctl, "text/")) h->ctype = CT_HTML;
    else if (ci_prefix(ctl, "image/jpeg")) h->ctype = CT_JPEG;
    else if (ci_prefix(ctl, "application/x-ps2vid")) h->ctype = CT_VIDEO;
    else h->ctype = CT_OTHER;
    h->leftlen = hl - body;
    memcpy(h->left, hdr + body, h->leftlen);
    return 0;
}

static char *read_body(http_t *h, int maxlen, int *outlen)
{
    char *buf = malloc(maxlen + 1);
    if (!buf) return NULL;
    int len = h->leftlen > maxlen ? maxlen : h->leftlen, n;
    memcpy(buf, h->left, len);
    while (len < maxlen && (n = recv(h->fd, buf + len, maxlen - len, 0)) > 0) len += n;
    buf[len] = 0;
    *outlen = len;
    return buf;
}

/* ================= JPEG -> textura ================= */
struct my_err { struct jpeg_error_mgr pub; jmp_buf jb; };
static void my_exit(j_common_ptr c) { longjmp(((struct my_err *)c->err)->jb, 1); }
static void my_out(j_common_ptr c) { (void)c; }

static int decode_jpeg(const unsigned char *src, unsigned long len)
{
    static unsigned char row[TEX_W * 3];
    struct jpeg_decompress_struct ci;
    struct my_err je;

    ci.err = jpeg_std_error(&je.pub);
    je.pub.error_exit = my_exit;
    je.pub.output_message = my_out;
    if (setjmp(je.jb)) { jpeg_destroy_decompress(&ci); return -1; }

    jpeg_create_decompress(&ci);
    jpeg_mem_src(&ci, (unsigned char *)src, len);
    jpeg_read_header(&ci, TRUE);
    ci.dct_method = JDCT_IFAST;
    ci.do_fancy_upsampling = FALSE;
    ci.out_color_space = JCS_RGB;
    int d = 1;
    while (d < 8 && (int)(ci.image_width / d) > TEX_W) d *= 2;
    ci.scale_num = 1; ci.scale_denom = d;
    jpeg_start_decompress(&ci);

    if (ci.output_width > TEX_W || ci.output_components != 3) {
        jpeg_abort_decompress(&ci); jpeg_destroy_decompress(&ci); return -1;
    }
    unsigned int *dst = (unsigned int *)tex.Mem;
    if (ci.output_width < TEX_W || ci.output_height < TEX_H)
        for (int i = 0; i < TEX_W * TEX_H; i++) dst[i] = 0x80000000;

    while (ci.output_scanline < ci.output_height && ci.output_scanline < TEX_H) {
        JSAMPROW rp = row;
        int y = ci.output_scanline;
        jpeg_read_scanlines(&ci, &rp, 1);
        unsigned int *line = dst + y * TEX_W;
        for (unsigned int x = 0; x < ci.output_width; x++)
            line[x] = row[x*3] | (row[x*3+1] << 8) | (row[x*3+2] << 16) | 0x80000000;
    }
    if (ci.output_scanline < ci.output_height) jpeg_abort_decompress(&ci);
    else jpeg_finish_decompress(&ci);
    jpeg_destroy_decompress(&ci);
    FlushCache(0);
    return 0;
}

/* ================= visor de imagen (RAM) ================= */
static void view_image(http_t *h)
{
    int len = 0;
    draw_msg("Cargando imagen...");
    unsigned char *buf = (unsigned char *)read_body(h, MAX_IMG, &len);
    lwip_close(h->fd);
    if (!buf) { set_status("Sin memoria"); return; }
    int ok = decode_jpeg(buf, len);
    free(buf);                                  /* el JPEG ya no hace falta */
    if (ok < 0) { set_status("Imagen invalida"); return; }

    int first = 1;
    for (;;) {
        if (input() & PAD_CIRCLE) break;
        begin_frame();
        if (first) { gsKit_texture_upload(gs, &tex); first = 0; }
        draw_tex_fullscreen();
        text(8, 4, C_GRAY, "Circulo: volver");
        end_frame();
    }
}

/* ================= reproductor de video (buffer circular en RAM) ================= */
static unsigned char *vb;
static int vhead, vcount;

static void vb_peek(int off, unsigned char *dst, int n)
{
    int pos = (vhead + off) % VBUF_SIZE;
    int first = VBUF_SIZE - pos; if (first > n) first = n;
    memcpy(dst, vb + pos, first);
    if (first < n) memcpy(dst + first, vb, n - first);
}
static void vb_drop(int n) { vhead = (vhead + n) % VBUF_SIZE; vcount -= n; }

/* devuelve 0 si el servidor cerro la conexion */
static int vb_fill(int fd)
{
    int room = VBUF_SIZE - vcount;
    if (room <= 0) return 1;
    int tail = (vhead + vcount) % VBUF_SIZE;
    int chunk = VBUF_SIZE - tail;
    if (chunk > room) chunk = room;
    if (chunk > 32768) chunk = 32768;
    int n = recv(fd, vb + tail, chunk, MSG_DONTWAIT);
    if (n > 0) { vcount += n; return 1; }
    if (n == 0) return 0;
    if (errno == EWOULDBLOCK || errno == EAGAIN) return 1;
    return 0;
}

static void play_video(http_t *h)
{
    vb = malloc(VBUF_SIZE);
    unsigned char *fr = malloc(MAX_FRAME);
    if (!vb || !fr) { free(vb); free(fr); lwip_close(h->fd); set_status("Sin memoria"); return; }
    vhead = 0; vcount = h->leftlen;
    memcpy(vb, h->left, h->leftlen);

    int started = 0, eof = 0, interval = 6, tick = 0, fps = 10, newf = 0, have = 0;

    for (;;) {
        if (input() & PAD_CIRCLE) break;

        for (int k = 0; k < 4 && !eof; k++) {
            int before = vcount;
            if (!vb_fill(h->fd)) eof = 1;
            if (vcount == before) break;
        }

        if (!started) {
            if (vcount >= VBUF_PRE || (eof && vcount > 0)) {
                unsigned char b; vb_peek(0, &b, 1); vb_drop(1);
                fps = b ? b : 10;
                interval = hz / fps; if (interval < 1) interval = 1;
                started = 1;
            } else if (eof) break;
        } else {
            tick++;
            if (vcount >= 4) {
                if (tick >= interval) {
                    unsigned char lb[4]; vb_peek(0, lb, 4);
                    int len = (lb[0] << 24) | (lb[1] << 16) | (lb[2] << 8) | lb[3];
                    if (len <= 0 || len > MAX_FRAME) break;
                    if (vcount >= 4 + len) {
                        vb_peek(4, fr, len);
                        vb_drop(4 + len);
                        if (decode_jpeg(fr, len) == 0) { newf = 1; have = 1; }
                        tick = 0;
                    } else if (eof) break;
                }
            } else if (eof) break;
        }

        begin_frame();
        if (have) {
            if (newf) { gsKit_texture_upload(gs, &tex); newf = 0; }
            draw_tex_fullscreen();
        }
        char hud[64];
        snprintf(hud, sizeof(hud), started ? "Buffer %d%%  %dfps  Circulo: salir"
                                           : "Buffering %d%%...  Circulo: salir",
                 (int)((long long)vcount * 100 / (started ? VBUF_SIZE : VBUF_PRE)),
                 fps);
        text(8, 4, C_GRAY, hud);
        end_frame();
    }
    lwip_close(h->fd);
    free(vb); vb = NULL;                        /* libera los 6 MB */
    free(fr);
}

/* ================= HTML -> texto ================= */
static char lines[MAX_LINES][COLS + 1];
static int  nlines, curcol;
static char links[MAX_LINKS][URL_LEN];
static int  link_line[MAX_LINKS];
static int  nlinks;

static void put_ch(char c)
{
    if (nlines >= MAX_LINES - 1) return;
    if (c == '\n') {
        if (curcol > 0 || (nlines > 0 && lines[nlines - 1][0])) {
            lines[nlines][curcol] = 0;
            nlines++; curcol = 0; lines[nlines][0] = 0;
        }
        return;
    }
    if (curcol >= COLS) { lines[nlines][curcol] = 0; nlines++; curcol = 0; }
    lines[nlines][curcol++] = c;
    lines[nlines][curcol] = 0;
}
static void put_str(const char *s) { while (*s) put_ch(*s++); }

static void render_html(const char *html, int len, const char *base)
{
    nlines = 0; curcol = 0; lines[0][0] = 0; nlinks = 0;
    int lastsp = 1;
    const char *p = html, *end = html + len;

    while (p < end && nlines < MAX_LINES - 2) {
        if (*p == '<') {
            const char *e = memchr(p, '>', end - p);
            if (!e) break;
            char tag[500]; int tl = (int)(e - p - 1); if (tl > 499) tl = 499;
            memcpy(tag, p + 1, tl); tag[tl] = 0;
            p = e + 1;

            if (ci_prefix(tag, "script") || ci_prefix(tag, "style")) {
                const char *c = ci_find(p, ci_prefix(tag, "script") ? "</script" : "</style");
                if (!c) break;
                p = c; continue;
            }
            if (!strncmp(tag, "!--", 3)) { const char *c = strstr(p - 1, "-->"); if (c) p = c + 3; continue; }

            if (ci_prefix(tag, "br") || ci_prefix(tag, "p") || ci_prefix(tag, "/p") ||
                ci_prefix(tag, "div") || ci_prefix(tag, "/div") || ci_prefix(tag, "li") ||
                ci_prefix(tag, "tr") || ci_prefix(tag, "h1") || ci_prefix(tag, "h2") ||
                ci_prefix(tag, "h3") || ci_prefix(tag, "/h")) { put_ch('\n'); lastsp = 1; }
            if (ci_prefix(tag, "li")) put_str("* ");

            if ((tag[0] == 'a' || tag[0] == 'A') && tag[1] == ' ' && nlinks < MAX_LINKS) {
                const char *hh = ci_find(tag, "href=");
                if (hh) {
                    hh += 5;
                    char q = (*hh == '"' || *hh == '\'') ? *hh++ : ' ';
                    char raw[URL_LEN]; int i = 0;
                    while (*hh && *hh != q && i < URL_LEN - 1) raw[i++] = *hh++;
                    raw[i] = 0;
                    resolve_url(base, raw, links[nlinks]);
                    if (links[nlinks][0]) {
                        char m[24];
                        const char *kind = strstr(links[nlinks], "/img?") ? "foto" :
                                           strstr(links[nlinks], "/vid?") ? "video" : "";
                        if (kind[0]) snprintf(m, sizeof(m), "[%d %s]", nlinks, kind);
                        else snprintf(m, sizeof(m), "[%d]", nlinks);
                        link_line[nlinks] = nlines;
                        put_str(m); nlinks++; lastsp = 0;
                    }
                }
            }
            continue;
        }
        unsigned char c = (unsigned char)*p++;
        if (c == '&') {
            if (!strncmp(p, "amp;", 4)) { put_ch('&'); p += 4; }
            else if (!strncmp(p, "lt;", 3)) { put_ch('<'); p += 3; }
            else if (!strncmp(p, "gt;", 3)) { put_ch('>'); p += 3; }
            else if (!strncmp(p, "quot;", 5)) { put_ch('"'); p += 5; }
            else if (!strncmp(p, "nbsp;", 5)) { put_ch(' '); p += 5; }
            else if (!strncmp(p, "#39;", 4)) { put_ch('\''); p += 4; }
            else put_ch('&');
            lastsp = 0; continue;
        }
        if (c >= 0x80) { if (c >= 0xC0) { put_ch('?'); lastsp = 0; } continue; }
        if (c == ' ' || c == '\n' || c == '\r' || c == '\t') {
            if (!lastsp) { put_ch(' '); lastsp = 1; }
        } else { put_ch((char)c); lastsp = 0; }
    }
    nlines++;
}

/* ================= navegador ================= */
static char cur_url[URL_LEN];
static char hist[MAX_HIST][URL_LEN];
static int  nhist, scroll_pos, sel_link;

static int view_rows(void) { return (gs->Height - 44) / LINE_H; }

static void ensure_visible(void)
{
    if (nlinks == 0) return;
    int l = link_line[sel_link], r = view_rows();
    if (l < scroll_pos) scroll_pos = l;
    if (l >= scroll_pos + r) scroll_pos = l - r + 1;
}

static void draw_browser(void)
{
    begin_frame();
    char top[COLS + 1];
    snprintf(top, sizeof(top), "%.*s", COLS, cur_url);
    text(8, 4, C_CYAN, top);

    int r = view_rows();
    for (int i = 0; i < r; i++) {
        int l = scroll_pos + i;
        if (l >= nlines) break;
        u64 col = C_WHITE;
        if (nlinks > 0 && link_line[sel_link] == l) col = C_YELLOW;
        text(8, 20 + i * LINE_H, col, lines[l]);
    }
    char bot[100];
    snprintf(bot, sizeof(bot), "Link %d/%d  %s", sel_link, nlinks ? nlinks - 1 : 0, status);
    text(8, gs->Height - 18, C_GRAY, bot);
    end_frame();
}

static void load_page(const char *url, int push)
{
    http_t h;
    char shown[COLS + 1];
    snprintf(shown, sizeof(shown), "Cargando %.*s", COLS - 10, url);
    draw_msg(shown);
    status[0] = 0;

    if (http_open(url, &h) == 0) {
        if (h.ctype == CT_JPEG) { view_image(&h); return; }
        if (h.ctype == CT_VIDEO) { play_video(&h); return; }
        if (h.ctype == CT_HTML) {
            int len = 0;
            char *buf = read_body(&h, MAX_PAGE, &len);
            lwip_close(h.fd);
            if (!buf) { set_status("Sin memoria"); return; }

            char fn[96]; cache_name(url, fn);
            int fd = open(fn, O_WRONLY | O_CREAT | O_TRUNC);   /* cache en USB */
            if (fd >= 0) { write(fd, buf, len); close(fd); set_status("Guardado en USB"); }
            else set_status("Sin USB (sin cache)");

            if (push && cur_url[0] && nhist < MAX_HIST) strcpy(hist[nhist++], cur_url);
            strcpy(cur_url, url);
            render_html(buf, len, url);
            free(buf);                                         /* libera la RAM */
            scroll_pos = 0; sel_link = 0;
            return;
        }
        lwip_close(h.fd);
        set_status("Tipo no soportado");
        return;
    }

    /* sin red: intenta la copia guardada en la USB */
    char fn[96]; cache_name(url, fn);
    int fd = open(fn, O_RDONLY);
    if (fd >= 0) {
        char *buf = malloc(MAX_PAGE + 1);
        if (buf) {
            int len = read(fd, buf, MAX_PAGE);
            if (len < 0) len = 0;
            buf[len] = 0;
            strcpy(cur_url, url);
            render_html(buf, len, url);
            free(buf);
            scroll_pos = 0; sel_link = 0;
            set_status("(copia de la USB)");
        }
        close(fd);
    }
}

static void do_search(const char *prompt, const char *endpoint)
{
    char q[96] = "";
    if (!text_input(prompt, q, sizeof(q))) return;
    char enc[300], u[URL_LEN + 64];
    url_encode(q, enc, sizeof(enc));
    snprintf(u, sizeof(u), PROXY "/%s?q=%s", endpoint, enc);
    load_page(u, 1);
}

int main(void)
{
    SifInitRpc(0);
    while (!SifIopReset("", 0)) {}
    while (!SifIopSync()) {}
    SifInitRpc(0);
    sbv_patch_enable_lmb();
    sbv_patch_disable_prefix_check();

    load_irx(ps2dev9_irx, size_ps2dev9_irx);
    load_irx(netman_irx, size_netman_irx);
    load_irx(smap_irx, size_smap_irx);
    load_irx(usbd_irx, size_usbd_irx);
    load_irx(bdm_irx, size_bdm_irx);
    load_irx(bdmfs_fatfs_irx, size_bdmfs_fatfs_irx);
    load_irx(usbmass_bd_irx, size_usbmass_bd_irx);

    gfx_init();
    draw_msg("Esperando USB...");
    sleep(4);
    mkdir(CACHE_DIR, 0777);                    /* mass:/DVD */

    padInit(0);
    padPortOpen(0, 0, padbuf);
    while (padGetState(0, 0) != PAD_STATE_STABLE &&
           padGetState(0, 0) != PAD_STATE_FINDCTP1) usleep(10000);

    network_init();
    load_page(HOME_URL, 0);

    for (;;) {
        unsigned int p = input();
        int maxscroll = nlines > view_rows() ? nlines - view_rows() : 0;

        if (p & PAD_DOWN) { scroll_pos += 1; if (scroll_pos > maxscroll) scroll_pos = maxscroll; }
        if (p & PAD_UP)   { scroll_pos -= 1; if (scroll_pos < 0) scroll_pos = 0; }
        if ((p & PAD_R1) && sel_link < nlinks - 1) { sel_link++; ensure_visible(); }
        if ((p & PAD_L1) && sel_link > 0)          { sel_link--; ensure_visible(); }

        if ((p & PAD_CROSS) && nlinks > 0) {
            char t[URL_LEN]; strcpy(t, links[sel_link]);
            load_page(t, 1);
        }
        if ((p & PAD_CIRCLE) && nhist > 0) {
            char b[URL_LEN]; strcpy(b, hist[--nhist]);
            load_page(b, 0);
        }
        if (p & PAD_START)  { char u[URL_LEN]; strcpy(u, cur_url); load_page(u, 0); }
        if (p & PAD_SELECT) load_page(HOME_URL, 1);
        if (p & PAD_TRIANGLE) {
            char typed[200] = "https://", enc[400], u[URL_LEN + 100];
            if (text_input("URL:", typed, sizeof(typed))) {
                url_encode(typed, enc, sizeof(enc));
                snprintf(u, sizeof(u), PROXY "/p?u=%s", enc);
                load_page(u, 1);
            }
        }
        if (p & PAD_SQUARE) do_search("Buscar en la web:", "search");
        if (p & PAD_L2)     do_search("Buscar fotos:", "isearch");
        if (p & PAD_R2)     do_search("Buscar videos:", "vsearch");

        draw_browser();
    }
    return 0;
}
