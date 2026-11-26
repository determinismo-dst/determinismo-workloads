#!/usr/bin/env python3
"""Replace each fixed section's Suites bullet with the result of the final
per-patch check (build/verify/F<n>/summary.txt), keeping a note per finding."""
import os, re
R = os.environ['FLECS_FIXES_ROOT']
patch_of = {'F2': 'F1', 'F19': 'F18', 'F34': 'F29'}
notes = {
 'F5': ' The cpp suite covers `ecs_cpp_set`.',
 'F7': ' core includes OnDelete.',
 'F8': ' core\'s Entity, New_w_Count, Pairs and World suites and addons\' Memory suite use ranges.',
 'F11': ' core includes Commands.', 'F12': ' core includes Commands, Hierarchies and OnDelete.',
 'F17': ' addons includes Pipeline, SystemMisc and MultiThread.',
 'F21': ' core includes Prefab\'s `*_offset_id*` tests, which pin the child id to instance + offset and its generation.',
 'F22': ' core includes Commands.',
 'F25': ' addons includes `SystemMisc_system_readeactivate*` and the Pipeline activation tests.',
 'F26': ' addons includes MultiThread and MultiThreadStaging, with thread and task workers.',
 'F31': ' addons includes Pipeline.',
 'F32': ' query includes the DontFragment and Sparse suites.',
 'F33': ' Also `fixes/checks/F33_mt_change_detection.c`: with 4 threads, a multi-threaded `[inout] Position` system still makes another change-detecting query report the change after every frame, on both builds.',
 'F36': ' query includes ChangeDetection.',
 'F39': ' The suite objects were compiled against the unpatched flecs.h; the only suite source that names the spawner, NonFragmentingChildOf.c, only calls `ecs_has(..., EcsTreeSpawner)`, so the struct change does not affect it.',
 'F40': ' query includes the Sorting suites.',
}
def result(p):
    s = open(os.path.join(R, 'build/verify', p, 'summary.txt')).read()
    if 'NEW FAIL' in s or 'LINK-FAILED' in s:
        return None
    want = ['(core.all)', '(query.all)', '(addons.all)', '(collections.all)', '(cpp.all)']
    if not all(w in s for w in want):
        return None
    return True
for name in sorted(os.listdir(os.path.join(R, 'build/sections'))):
    f = name[:-3]
    path = os.path.join(R, 'build/sections', name)
    s = open(path).read()
    if '**No fix.**' in s:
        continue
    p = patch_of.get(f, f)
    ok = result(p)
    if not ok:
        print('CHECK BY HAND:', f); continue
    same = '' if p == f else ' (`%s.diff`, the same patch)' % p
    line = ('- **Suites:** core, query, addons, collections and cpp with this patch%s: '
            'unchanged from v4.2.0 (core 3870 / 0, query 4798 / 6, addons 643 / 0, '
            'collections 97 / 0, cpp 1919 / 0; see "flecs\'s suites").%s' % (same, notes.get(f, '')))
    s2, n = re.subn(r'^- \*\*Suites:\*\*.*$', lambda m: line, s, flags=re.M)
    if n != 1:
        print('NO SUITES LINE:', f); continue
    open(path, 'w').write(s2)
    print('updated', f)
