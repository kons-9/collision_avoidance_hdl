#
# Makefile for c code
#

# 共通初期設定ファイルをインクルード
include ../software_tools/Makefile.inc

# C言語ソースコードファイルを指定
SRC = test.c
INCLUDES = $(INCLUDE_ROOT)/poyoio.c $(INCLUDE_ROOT)/poyolib.c

SRCS = $(SRC) $(INCLUDES)
OBJS = $(SRCS:.c=.o)


all: code.hex data.hex

# オブジェクトファイル生成
%.o: %.c Makefile
	$(CC) $(CFLAGS) -o $@ -c $<

# 下記はアセンブリコードを入力する場合の例
#%.o: %.s Makefile
#	$(CC) $(CFLAGS) -o $@ -c $<

# ELFファイル生成
app.elf: $(OBJS) $(CRTOBJ) Makefile
	$(LD) $(CRTOBJ) $(OBJS) $(LIBC) $(LIBGCC) -T$(LDSCRIPT) $(LDFLAGS) -o app.elf

# バイナリファイル生成
app.bin: app.elf
	$(OBJDUMP) -D $< > app.dump
	$(OBJCOPY) -O binary $< $@

# バイナリファイルから.hex形式ファイルを生成
app.hex: app.bin
	hexdump -v -e '1/4 "%08x" "\n"' $< > $@

# .hex形式ファイルを命令メモリ用ファイルとデータメモリ用ファイルへと分割
code.hex data.hex: app.hex
	$(HEX_CONVERTER) $<


.PHONY: clean
clean:
	rm $(OBJS) code.hex data.hex app.hex app.dump app.bin app.elf crt0.o -f
