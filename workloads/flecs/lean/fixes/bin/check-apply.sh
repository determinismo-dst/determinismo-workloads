#!/bin/bash
# usage: check-apply.sh fixes/F<n>.diff...  -- git apply --check against a clean v4.2.0 copy
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
C=$R/build/applycheck.$$; rm -rf "$C"; mkdir -p "$C"; cp -R "$R/orig/flecs-4.2.0/src" "$R/orig/flecs-4.2.0/include" "$C/"; chmod -R u+w "$C"
cd "$C"
for p in "$@"; do case $p in /*) ;; *) p=$R/$p;; esac; if git apply --check "$p" 2>$R/build/ga.$$; then echo "$(basename $p): applies"; else echo "$(basename $p): FAILS: $(cat $R/build/ga.$$)"; fi; rm -f $R/build/ga.$$; done
cd "$R"; rm -rf "$C"
