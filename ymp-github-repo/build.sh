#!/bin/sh
# Сборка под Windows Mobile 6 (ARM) через cegcc
# Нужны рядом: ymp.c, minimp3.h, stb_image.h, mbedtls_config.h, папка mbedtls-2.28
# Для значка ymp.exe: ymp.rc и ymp.ico (если windres не найден - значок просто пропускается)
CC=arm-mingw32ce-gcc
RC=arm-mingw32ce-windres
MBED=mbedtls-2.28

RES=""
if [ -f ymp.rc ] && [ -f ymp.ico ] && command -v $RC >/dev/null 2>&1; then
    if $RC -i ymp.rc -o ymp_rc.o 2>/dev/null; then RES=ymp_rc.o; echo "значок: подключён"; else echo "значок: windres не справился, пропускаю"; fi
else
    echo "значок: windres не найден, пропускаю"
fi

$CC -Os -std=gnu99 -ffunction-sections -fdata-sections -Wl,--gc-sections -s \
    -DMBEDTLS_CONFIG_FILE='"mbedtls_config.h"' \
    -I. -I$MBED/include \
    ymp.c $MBED/library/*.c $RES \
    -o ymp.exe -lws2
