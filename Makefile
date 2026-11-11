EE_BIN = ps2browser.elf

IRX_LIST = ps2dev9 netman smap usbd bdm bdmfs_fatfs usbmass_bd
IRX_OBJS = $(addsuffix _irx.o, $(IRX_LIST))

EE_OBJS = main.o $(IRX_OBJS)

# gsKit (graficos) y libjpeg (de ps2sdk-ports) tienen que estar instalados
GSKIT ?= $(PS2DEV)/gsKit

EE_INCS  += -I$(GSKIT)/include -I$(PS2SDK)/ports/include
EE_LDFLAGS += -L$(GSKIT)/lib -L$(PS2SDK)/ports/lib

EE_LIBS = -lgskit -ldmakit -ljpeg -lnetman -lps2ip -lpad -lpatches -lc -lm
EE_CFLAGS += -O2 -Wall

# Convierte cada .irx del SDK en un .c embebido dentro del ELF
%_irx.c: $(PS2SDK)/iop/irx/%.irx
	$(PS2SDK)/bin/bin2c $< $@ $*_irx

all: $(EE_BIN)

clean:
	rm -f $(EE_BIN) $(EE_OBJS) *_irx.c

include $(PS2SDK)/samples/Makefile.pref
include $(PS2SDK)/samples/Makefile.eeglobal
