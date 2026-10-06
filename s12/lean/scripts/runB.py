#!/usr/bin/env python3
"""Phase B: the kernel checks of the root modules, with a bounded number of `lean` processes (the
kernel needs ~8 GB per process on top of the shared imports; `lake` has no job limit).

For each root (`Sqpack/V7/R?????.lean` and its directory, from `emit_v7.py --chunk`): the leaf
modules, then their row groups, then the root module, each `lean -o … -i …` into `.lake/build`.
Prints one JSON line per root (`ok`, seconds, the failing modules).

    runB.py --lo I --hi J [--jobs N] [--mod M --rem R]     (run from s12/lean after `lake build` of the common modules)
"""
import argparse, glob, json, os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
LIB = os.path.join(ROOT, '.lake', 'build', 'lib', 'lean')


def lean_path():
    out = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, capture_output=True, text=True)
    return out.stdout.strip()


def compile_mod(src, env):
    """`lean -o` one module; returns (ok, seconds, tail of the log)"""
    rel = os.path.relpath(src, ROOT)[:-5]
    olean = os.path.join(LIB, rel + '.olean'); ilean = os.path.join(LIB, rel + '.ilean')
    os.makedirs(os.path.dirname(olean), exist_ok=True)
    if os.path.exists(ilean) and os.path.getmtime(ilean) >= os.path.getmtime(src):
        return True, 0.0, ''     # done by an earlier run (the .ilean is written after the .olean)
    t = time.time()
    p = subprocess.run(['lean', '-o', olean, '-i', ilean, src], cwd=ROOT, env=env, capture_output=True, text=True)
    ok = p.returncode == 0
    return ok, time.time() - t, '' if ok else (p.stdout + p.stderr)[-2000:]


def root_job(idx, pool, env):
    """the modules of one root, in dependency order; the futures of each stage run on the pool"""
    t0 = time.time()
    d = os.path.join(ROOT, 'Sqpack', 'V7', f'R{idx:05d}')
    leaves = sorted(f for f in glob.glob(os.path.join(d, '*.lean')) if not re.search(r'_g\d+\.lean$', f))
    groups = sorted(glob.glob(os.path.join(d, '*_g*.lean')))
    fails = []
    for stage in (leaves, groups, [os.path.join(ROOT, 'Sqpack', 'V7', f'R{idx:05d}.lean')]):
        res = list(pool.map(lambda f: (f, compile_mod(f, env)), stage))
        fails += [(os.path.basename(f), r[2]) for f, r in res if not r[0]]
        if fails:
            break
    return dict(root=idx, ok=not fails, sec=round(time.time() - t0, 1), fails=[f for f, _ in fails],
                log=fails[0][1] if fails else '')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lo', type=int, required=True)
    ap.add_argument('--hi', type=int, required=True)
    ap.add_argument('--jobs', type=int, default=8)
    ap.add_argument('--mod', type=int, default=1, help='only the roots with index %% MOD == REM')
    ap.add_argument('--rem', type=int, default=0)
    ap.add_argument('--roots', type=int, default=4, help='roots in flight at once')
    a = ap.parse_args()
    env = dict(os.environ, LEAN_PATH=lean_path())
    idxs = [i for i in range(a.lo, a.hi) if i % a.mod == a.rem and os.path.exists(os.path.join(ROOT, 'Sqpack', 'V7', f'R{i:05d}.lean'))
            and not os.path.exists(os.path.join(LIB, 'Sqpack', 'V7', f'R{i:05d}.olean'))]
    print(json.dumps(dict(todo=len(idxs))), flush=True)
    with ThreadPoolExecutor(a.jobs) as pool, ThreadPoolExecutor(a.roots) as outer:
        for r in outer.map(lambda i: root_job(i, pool, env), idxs):
            print(json.dumps(r), flush=True)


if __name__ == '__main__':
    main()
