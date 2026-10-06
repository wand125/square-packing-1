#!/usr/bin/env python3
"""Phase B: the kernel checks of the root modules, with a bounded number of `lean` processes (the
kernel needs ~8 GB per process on top of the shared imports; `lake` has no job limit).

For each root (`Sqpack/V7/R?????.lean` and its directory, from `emit_v7.py --chunk`): the leaf
modules, then their row groups, then the root module, each `lean -o … -i …` into `.lake/build`.
Prints one JSON line per root (`ok`, seconds, the failing modules).

    runB.py --lo I --hi J [--jobs N] [--mod M --rem R]     (run from s12/lean after `lake build` of the common modules)
"""
import argparse, glob, json, os, re, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
LIB = os.path.join(ROOT, '.lake', 'build', 'lib', 'lean')


def lean_path():
    out = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, capture_output=True, text=True)
    return out.stdout.strip()


class MemBudget:
    """a budget of GB over the running `lean`s (each charged its estimate `cost`), and a floor on the
    free memory (`MemAvailable`) below which no new `lean` starts"""
    def __init__(self, gb, floor):
        self.left, self.floor, self.cv = gb, floor, threading.Condition()

    def avail(self):
        for line in open('/proc/meminfo'):
            if line.startswith('MemAvailable:'):
                return int(line.split()[1]) / 2 ** 20
        return 1e9

    def acquire(self, c):
        with self.cv:
            while c > self.left or self.avail() < self.floor:
                self.cv.wait(5)
            self.left -= c

    def release(self, c):
        with self.cv:
            self.left += c
            self.cv.notify_all()


BUDGET = None
COST = dict(base=10.0, per_mb=3.0, root=36.0)


def cost(src):
    """the estimated peak GB of `lean` on one module (calibrated on the largest modules)"""
    if re.search(r'/R\d{5}\.lean$', src):
        return COST['root']
    return COST['base'] + COST['per_mb'] * os.path.getsize(src) / 2 ** 20


def compile_mod(src, env):
    """`lean -o` one module within the memory budget; returns (ok, seconds, tail of the log)"""
    rel = os.path.relpath(src, ROOT)[:-5]
    olean = os.path.join(LIB, rel + '.olean'); ilean = os.path.join(LIB, rel + '.ilean')
    os.makedirs(os.path.dirname(olean), exist_ok=True)
    if os.path.exists(ilean) and os.path.getmtime(ilean) >= os.path.getmtime(src):
        return True, 0.0, ''     # done by an earlier run (the .ilean is written after the .olean)
    c = cost(src)
    BUDGET.acquire(c)
    t = time.time()
    try:
        p = subprocess.run(['lean', '-o', olean, '-i', ilean, src], cwd=ROOT, env=env, capture_output=True, text=True)
    finally:
        BUDGET.release(c)
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
    ap.add_argument('--mem', type=float, default=400, help='GB budget over the estimated peaks')
    ap.add_argument('--floor', type=float, default=60, help='GB of MemAvailable below which no lean starts')
    ap.add_argument('--cost', default='', help='base,per_mb,root (GB)')
    ap.add_argument('--roots', type=int, default=4, help='roots in flight at once')
    a = ap.parse_args()
    global BUDGET
    BUDGET = MemBudget(a.mem, a.floor)
    if a.cost:
        COST.update(zip(('base', 'per_mb', 'root'), map(float, a.cost.split(','))))
    env = dict(os.environ, LEAN_PATH=lean_path())
    idxs = [i for i in range(a.lo, a.hi) if i % a.mod == a.rem and os.path.exists(os.path.join(ROOT, 'Sqpack', 'V7', f'R{i:05d}.lean'))
            and not os.path.exists(os.path.join(LIB, 'Sqpack', 'V7', f'R{i:05d}.olean'))]
    print(json.dumps(dict(todo=len(idxs))), flush=True)
    with ThreadPoolExecutor(a.jobs) as pool, ThreadPoolExecutor(a.roots) as outer:
        for r in outer.map(lambda i: root_job(i, pool, env), idxs):
            print(json.dumps(r), flush=True)


if __name__ == '__main__':
    main()
