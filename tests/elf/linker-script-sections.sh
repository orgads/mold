#!/usr/bin/env bash
. $(dirname $0)/common.inc

# A SECTIONS command that only moves the default layout is accepted, and
# its base address is used.
cat <<EOF | $CC -o $t/a.o -c -xc -
#include <stdio.h>
int main() {
  printf("Hello world\n");
}
EOF

cat <<EOF > $t/script
OUTPUT_ARCH(foo)
ENTRY(_start)
SEARCH_DIR("=/foo")
SECTIONS
{
  PROVIDE (__executable_start = 0x40000000); . = 0x40000000 + SIZEOF_HEADERS;
  .text : { *(.text .text.*) } =0
  . = ALIGN(16);
  _gp = ALIGN(16) + 0x7ff0;
  .data : { *(.data .data.*) }
  .bss : { *(.bss) . = ALIGN(. != 0 ? 64 / 8 : 1); }
  .comment 0 : { *(.comment) }
  /DISCARD/ : { *(.note.GNU-stack) }
}
EOF

$CC -B. -no-pie -o $t/exe1 $t/a.o -Wl,-T,$t/script
$QEMU $t/exe1 | grep 'Hello world'
readelf -lW $t/exe1 | grep -m1 LOAD | grep -E ' 0x0*40000000 '

# --image-base overrides the script.
$CC -B. -no-pie -o $t/exe2 $t/a.o -Wl,-T,$t/script,--image-base=0x50000000
readelf -lW $t/exe2 | grep -m1 LOAD | grep -E ' 0x0*50000000 '

# Placing sections at specific addresses is not supported.
cat <<EOF > $t/script2
SECTIONS { .text 0x1000 : { *(.text) } }
EOF

not $CC -B. -no-pie -o $t/exe3 $t/a.o -Wl,-T,$t/script2 |&
  grep 'unsupported: address of an output section'
