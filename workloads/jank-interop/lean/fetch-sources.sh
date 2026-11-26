#!/bin/sh
# fetch-sources.sh: the sources this replica translates, at the commits it was written against, into
# upstream/ (jank f3d82d654, round 1), upstream-main/ (jank main 7135b7708, rounds 2-4), upstream-r5/
# (jank main 94d32623, round 5; its compiler+runtime tree is 7135b7708's) and deps/
# (the libraries jank pins), all git-ignored. Only jank3-boost's header check reads one of them at
# run time (deps/boost-multiprecision); the rest are there to follow the reports' line numbers.
# Run it again any time: what is already at its commit is left alone.
set -eu
cd "$(dirname "$0")"

pin() { # pin <dir> <url> <commit>
  dir=$1 url=$2 commit=$3
  if [ -d "$dir/.git" ] && [ "$(git -C "$dir" rev-parse HEAD)" = "$commit" ]; then
    echo "$dir: at $commit"
    return 0
  fi
  [ -n "$dir" ] && rm -rf "./$dir"
  mkdir -p "$dir"
  git -C "$dir" init -q
  git -C "$dir" remote add origin "$url"
  git -C "$dir" fetch -q --depth 1 origin "$commit"
  git -C "$dir" checkout -q FETCH_HEAD
  echo "$dir: fetched $commit"
}

pin upstream https://github.com/jank-lang/jank.git f3d82d65499920f81216e9235bd5d3a34a968e3f
pin upstream-main https://github.com/jank-lang/jank.git 7135b770857d625630ab6f9abe5861c618d67b82
pin upstream-r5 https://github.com/jank-lang/jank.git 94d32623e3e6f0f40c412d41802fe02693aec094
pin deps/bdwgc https://github.com/jank-lang/bdwgc.git 327ef1f8c80a611b2f8b915850c8b2fd38e6595e
pin deps/boost-multiprecision https://github.com/jank-lang/boost-multiprecision.git 2b3ab082fac41c0d4bdb5a1c3daf7411be6fd679
pin deps/cppinterop https://github.com/jank-lang/CppInterOp.git 28b0830da72dfc52728bb58ba0b55d802d95c7eb
pin deps/folly https://github.com/jank-lang/folly.git e54ca53d2d57dc8dd205873f93b5a2715b0fee5e
pin deps/immer https://github.com/jank-lang/immer.git 282629d01917d4c7d0aba2322de700c6d1111276
# Round 4: jank.shell's boost.process, clojure.data.json's nlohmann json, uuid's stduuid.
pin deps/boost-process https://github.com/jank-lang/boost-process.git e4d0d405a12f13ebe7d894382d3a98830ae1c7bd
pin deps/json https://github.com/jank-lang/json 02dfbea39d94b8d19ddcd0eabfdc943a65bf3368
pin deps/stduuid https://github.com/jank-lang/stduuid.git 3afe7193facd5d674de709fccc44d5055e144d7a

# libstdc++ 15.3.0's regex sources (GCC's release tag, the GCC jank's nixpkgs pins), copied flat
# as the regex replica cites them.
regex=deps/libstdcxx-15.3.0
if [ -f "$regex/regex_executor.tcc" ]; then
  echo "$regex: present"
else
  gcc=deps/.gcc-15.3.0
  [ -d "$gcc/.git" ] || git -c advice.detachedHead=false clone -q --depth 1 --branch releases/gcc-15.3.0 --filter=blob:none --sparse \
    https://github.com/gcc-mirror/gcc.git "$gcc"
  git -C "$gcc" sparse-checkout set libstdc++-v3/include/bits libstdc++-v3/src/c++11 \
    libstdc++-v3/src/c++98 libstdc++-v3/config/os/gnu-linux
  mkdir -p "$regex"
  for name in regex.h regex.tcc regex_automaton.h regex_automaton.tcc regex_compiler.h \
      regex_compiler.tcc regex_constants.h regex_error.h regex_executor.h regex_executor.tcc \
      regex_scanner.h regex_scanner.tcc regex.cc localename.cc ctype_base.h ctype_configure_char.cc; do
    found=$(find "$gcc/libstdc++-v3" -name "$name" -type f | head -1)
    [ -n "$found" ] || { echo "fetch-sources.sh: $name not found in GCC 15.3.0" >&2; exit 1; }
    cp "$found" "$regex/$name"
  done
  echo "$regex: fetched (GCC releases/gcc-15.3.0)"
fi

# Round 5: libstdc++ 15.3.0's <chrono> parser (the #inst replica), from the same GCC tag.
if [ -f "$regex/chrono_io.h" ]; then
  echo "$regex (chrono): present"
else
  gcc=deps/.gcc-15.3.0
  [ -d "$gcc/.git" ] || git -c advice.detachedHead=false clone -q --depth 1 --branch releases/gcc-15.3.0 --filter=blob:none --sparse \
    https://github.com/gcc-mirror/gcc.git "$gcc"
  git -C "$gcc" sparse-checkout add libstdc++-v3/include/bits libstdc++-v3/include/std
  cp "$gcc/libstdc++-v3/include/bits/chrono_io.h" "$gcc/libstdc++-v3/include/bits/chrono.h" \
    "$gcc/libstdc++-v3/include/bits/istream.tcc" "$regex/"
  cp "$gcc/libstdc++-v3/include/std/chrono" "$regex/chrono.std"
  echo "$regex (chrono): fetched (GCC releases/gcc-15.3.0)"
fi

# Round 6: libstdc++ 15.3.0's UTF-8 conversion (wstring_convert<codecvt_utf8<wchar_t>>, which jank's
# upper-case/lower-case use), from the same GCC tag.
cvt=deps/libstdcxx-15.3.0-codecvt
if [ -f "$cvt/codecvt.cc" ]; then
  echo "$cvt: present"
else
  gcc=deps/.gcc-15.3.0
  [ -d "$gcc/.git" ] || git -c advice.detachedHead=false clone -q --depth 1 --branch releases/gcc-15.3.0 --filter=blob:none --sparse \
    https://github.com/gcc-mirror/gcc.git "$gcc"
  git -C "$gcc" sparse-checkout add libstdc++-v3/include/bits libstdc++-v3/src/c++11
  mkdir -p "$cvt"
  cp "$gcc/libstdc++-v3/include/bits/locale_conv.h" "$gcc/libstdc++-v3/src/c++11/codecvt.cc" "$cvt/"
  echo "$cvt: fetched (GCC releases/gcc-15.3.0)"
fi

# Round 5: GNU ld 2.45's script grammar and docs (the spec of the ld-script replica), flat.
ld=deps/binutils-ld
if [ -f "$ld/ldgram.y" ]; then
  echo "$ld: present"
else
  bu=deps/.binutils-2_45
  [ -d "$bu/.git" ] || git -c advice.detachedHead=false clone -q --depth 1 --branch binutils-2_45 --filter=blob:none --sparse \
    https://sourceware.org/git/binutils-gdb.git "$bu"
  git -C "$bu" sparse-checkout set ld
  mkdir -p "$ld"
  for name in ldgram.y ldlex.l ld.texi ldfile.c ldlang.c; do cp "$bu/ld/$name" "$ld/$name"; done
  echo "$ld: fetched (binutils-2_45)"
fi

echo "The LLVM 23.1.0 files CppInterOp reaches (deps/llvm-23.1.0*) are read only: llvm-project at llvmorg-23.1.0."
