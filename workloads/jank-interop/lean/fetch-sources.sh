#!/bin/sh
# fetch-sources.sh: the sources this replica translates, at the commits it was written against, into
# upstream/ (jank f3d82d654, round 1), upstream-main/ (jank main 7135b7708, rounds 2-3) and deps/
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
pin deps/bdwgc https://github.com/jank-lang/bdwgc.git 327ef1f8c80a611b2f8b915850c8b2fd38e6595e
pin deps/boost-multiprecision https://github.com/jank-lang/boost-multiprecision.git 2b3ab082fac41c0d4bdb5a1c3daf7411be6fd679
pin deps/cppinterop https://github.com/jank-lang/CppInterOp.git 28b0830da72dfc52728bb58ba0b55d802d95c7eb
pin deps/folly https://github.com/jank-lang/folly.git e54ca53d2d57dc8dd205873f93b5a2715b0fee5e
pin deps/immer https://github.com/jank-lang/immer.git 282629d01917d4c7d0aba2322de700c6d1111276

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

echo "The LLVM 23.1.0 files CppInterOp reaches (deps/llvm-23.1.0*) are read only: llvm-project at llvmorg-23.1.0."
