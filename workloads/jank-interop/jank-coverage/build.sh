#!/bin/bash
# SPDX-License-Identifier: MIT
# jank with determinismo's coverage: jank's LLVM (its fork, bin/build-clang) and jank at a pinned
# commit, its C and C++ compiled with -fsanitize-coverage=trace-pc-guard and linked against
# libvoidstar.so (the guest has determinismo's at /usr/lib; the install carries a copy there for
# runs outside a guest, the image's build among them), installed and packed into
# jank-install.tar beside this script, which the workload's Dockerfile unpacks (ARG JANK=coverage).
# The PPA's jank has no coverage: the explorer saw no new behavior after its first generation
# (phoenixNAP run 1908, 0 new of 45 known for 170 generations). On the host that builds the image
# (glibc: build on the image's Debian 13). One to two hours for LLVM on 12 threads, minutes for jank.
#   workloads/jank-interop/jank-coverage/build.sh <platform tree> [work directory, default ~/build]
# (the platform's tree after `zig build guest`: its zig-out/bin/libvoidstar.so and sdk/c/determinismo.h)
# assertions.patch beside this script: the SDK's assertions in jank's own source (assertions only),
# the C SDK's implementation compiled as C and linked whole into jank (without its coverage part:
# libvoidstar's callbacks are the coverage).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
platform=$(cd "${1:?usage: build.sh <platform tree> [work directory]}" && pwd)
work=${2:-$HOME/build}
voidstar=$platform/zig-out/bin/libvoidstar.so
header=$platform/sdk/c/determinismo.h
test -f "$header" || { echo "error: $header missing" >&2; exit 1; }
jank_commit=44eea86f7   # jank main, 2026-11-11
test -f "$voidstar" || { echo "error: $voidstar missing: the platform's zig build guest first" >&2; exit 1; }
mkdir -p "$work" && cd "$work"
[ -d jank ] || git clone -q --recurse-submodules --jobs 8 https://github.com/jank-lang/jank.git
cd jank && git fetch -q && git checkout -q "$jank_commit" && git submodule update -q --init --recursive --jobs 8
# The assertions, on the commit's own files (a rerun's earlier application undone first).
git checkout -q -- compiler+runtime/src && git apply "$here/assertions.patch"
cd compiler+runtime
[ -x build/llvm-install/usr/local/bin/clang++ ] || CC=clang CXX=clang++ ./bin/build-clang
export CC=$PWD/build/llvm-install/usr/local/bin/clang CXX=$PWD/build/llvm-install/usr/local/bin/clang++
mkdir -p "$work/voidstar" && cp "$voidstar" "$work/voidstar/"
# The C SDK's assertions: its header for the patched files, its implementation an archive.
mkdir -p "$work/det" && cp "$header" "$work/det/"
printf '#define DETERMINISMO_IMPLEMENTATION\n#include "determinismo.h"\n' > "$work/det/det.c"
"$CC" -O2 -fPIC -I"$work/det" -c "$work/det/det.c" -o "$work/det/det.o"
ar rcs "$work/det/libdeterminismo-assert.a" "$work/det/det.o"
cov="-fsanitize-coverage=trace-pc-guard -I$work/det"
# -fno-sanitize-link-runtime: with -fsanitize-coverage on the link, Clang's driver links compiler-rt's
# ubsan_standalone, whose own trace-pc-guard callbacks, in the executable, win over libvoidstar's:
# the edges went nowhere (phoenixNAP run 1917: no coverage event, 44 behaviors).
# The build runs jank itself (jank-phase-1 compiles its core libraries): the build's copy first.
link="-fno-sanitize-link-runtime -L$work/voidstar -lvoidstar -Wl,-rpath,/usr/lib -Wl,-rpath,$work/voidstar \
  -Wl,--whole-archive $work/det/libdeterminismo-assert.a -Wl,--no-whole-archive"
./bin/configure -GNinja -DCMAKE_BUILD_TYPE=Release -Djank_local_clang=on \
  -DCMAKE_C_FLAGS="$cov" -DCMAKE_CXX_FLAGS="$cov" \
  -DCMAKE_EXE_LINKER_FLAGS="$link" -DCMAKE_SHARED_LINKER_FLAGS="$link"
./bin/compile
install=$work/jank-install
rm -rf "$install" && DESTDIR=$install cmake --install build > /dev/null
mkdir -p "$install/usr/lib" && cp "$voidstar" "$install/usr/lib/libvoidstar.so"
tar -cf "$here/jank-install.tar" -C "$install" .
echo "jank-coverage: $here/jank-install.tar ($(du -h "$here/jank-install.tar" | cut -f1))"
