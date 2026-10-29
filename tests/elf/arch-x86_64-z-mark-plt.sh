#!/usr/bin/env bash
. $(dirname $0)/common.inc

cat <<EOF | $CC -fPIC -fsemantic-interposition -o $t/a.o -c -xc -
#include <stdio.h>
void world() { printf("world\n"); }
void hello() { printf("Hello "); world(); }
EOF

$CC -B. -o $t/b.so -shared $t/a.o -Wl,-z,now
readelf -d $t/b.so > $t/log1
not grep -E '0x0*7000000[013] ' $t/log1

$CC -B. -o $t/c.so -shared $t/a.o -Wl,-z,now,-z,mark-plt
readelf -d $t/c.so > $t/log2
grep -E '0x0*70000000 ' $t/log2
grep -E '0x0*70000001 ' $t/log2
grep -E '0x0*70000003 .* (0x10|16)$' $t/log2

cat <<EOF | $CC -o $t/d.o -c -xc -
void hello();
int main() { hello(); }
EOF

$CC -B. -o $t/exe $t/d.o $t/c.so -Wl,-z,now
$QEMU $t/exe | grep 'Hello world'

# Check that glibc rewrites the PLT entry if it can.
/lib64/ld-linux-x86-64.so.2 --list-tunables 2>/dev/null | grep -q plt_rewrite || skip

GLIBC_TUNABLES=glibc.cpu.plt_rewrite=1 LD_DEBUG=bindings $t/exe 2> $t/log3 |
  grep 'Hello world'
grep -E "changing 'world' PLT entry in .*/c.so' to direct branch" $t/log3
