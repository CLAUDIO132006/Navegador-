EE_BIN = psbrowser.elf
EE_OBJS = main.o ps2dev9_irx.o netman_irx.o smap_irx.o
EE_LIBS = -lps2ip_nm -lnetman -lpad -ldebug -lpatches -lc -lkernel
EE_CFLAGS += -O2 -Wall

.RECIPEPREFIX = >

all: $(EE_BIN)

ps2dev9_irx.c: $(PS2SDK)/iop/irx/ps2dev9.irx
> bin2c $< $@ ps2dev9_irx

netman_irx.c: $(PS2SDK)/iop/irx/netman.irx
> bin2c $< $@ netman_irx

smap_irx.c: $(PS2SDK)/iop/irx/smap.irx
> bin2c $< $@ smap_irx

clean:
> rm -f $(EE_BIN) $(EE_OBJS) *_irx.c

.RECIPEPREFIX =

include $(PS2SDK)/Defs.make
include $(PS2SDK)/ee/Rules.make
