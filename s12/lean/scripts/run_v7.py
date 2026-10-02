#!/usr/bin/env python3
"""Generate the Lean certificate of Valid7's pose trees (run V3 of qx2_zm), one module per root.

    run_v7.py --lo I --hi J [--nproc N] [--out DIR]

For every root in [I, J): rebuild its tree (tree_rebuild.py), certify every EXACT-type leaf (EXACT,
EXACT0, EXACT45, PIECE, CAP) with gen_exact.Leaf at the leaf's own scale (retrying with the high
McCormick anchor, then without the corner kinds), and write `DIR/R%05d.lean`: the leaves' ExLeaf
data and pair theorems, and the root theorem `root_%05d : CovT ...` at the global scale.  A status
line per root goes to stdout (JSON).  Nothing here is trusted.
"""
import argparse, json, os, pickle, signal, sys, time
from fractions import Fraction as F
from math import lcm
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from tree_rebuild import load, build, count  # noqa: E402
from gen_tree import Glue  # noqa: E402
from gen_axis import read_cover  # noqa: E402
import gen_exact as G  # noqa: E402

COVER = os.path.join(HERE, '..', '..', 'certificates', 'k2m3', 'L4_k02_box7.txt')
LEAVES = os.path.join(HERE, '..', '..', 'certificates', 'k2m3', 'qx2_zm', 'runV3_6294052a_leaves.jsonl.gz')
SG, RG, MQ = 128, 1 << 72, 35
SIMPLE = ('EMPTY', 'SYM', 'AXIS', 'LEB')
LIMIT = int(os.environ.get('V7_LIMIT', '1200'))   # seconds per attempt


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()

_cov = None


def leaves_of(t):
    if t[0] == 'L':
        yield t
    elif t[0] == 'C':
        yield from leaves_of(t[2])
    else:
        yield from leaves_of(t[2])
        yield from leaves_of(t[3])


def scales(b):
    dx = lcm(*[x.denominator for x in b[:4]])
    Sl = 1
    while (5 * Sl) % dx:
        Sl *= 2
    du = lcm(*[x.denominator for x in b[4:]])
    return Sl, max(1 << 16, du << 10)


def certify(b):
    Sl, Rl = scales(b)
    ib = [int(x * 5 * Sl) for x in b[:4]] + [int(x * Rl) for x in b[4:]]
    # the last flag keeps the Lebesgue rectangles; without them the bound is weaker but never negative
    # (the rectangle term `1 - U_x - U_y` goes below 0 where the square barely meets the rectangle)
    tries = [('hi', True, True, True), ('hi', True, True, False), ('lo', True, True, True),
             ('hi', False, True, True), ('hi', False, False, True)]
    log = []
    timed_out = False
    for anchor, corner, tan, rect in tries:
        if timed_out and rect:
            # the other modes only help where a check fails; a slow leaf needs a longer limit (V7_LIMIT)
            continue
        G.Leaf.ANCHOR, G.Leaf.USE_CORNER, G.Leaf.USE_TAN = anchor, corner, tan
        lf = G.Leaf(_cov, Sl, Rl, *ib)
        if not lf.ok:
            return None, 'wall', Sl, Rl
        if not rect:
            if not lf.crs:
                continue
            lf.crs = []
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(LIMIT)
        try:
            c = lf.run()
        except Timeout:
            c = None
            lf.stat['timeout'] = LIMIT
        finally:
            signal.alarm(0)
        tag = f'{anchor}/{int(corner)}{int(tan)}' + ('' if rect else '/norect')
        log.append(f"{tag}:{'timeout' if 'timeout' in lf.stat else 'fail' + str(lf.stat['fail'])}")
        timed_out = timed_out or 'timeout' in lf.stat
        if c:
            return lf, f'{anchor}/{int(corner)}{int(tan)}' + ('' if rect else '/norect'), Sl, Rl
    return None, ('timeout ' if timed_out else 'fail ') + ' '.join(log), Sl, Rl


def work(args):
    idx, root, leaves, outdir = args
    global _cov
    if _cov is None:
        _cov = sorted_cover()
    _, D, W, pts, segs, rects = _cov
    t0 = time.time()
    tree = build(root, leaves, F(7))
    g = Glue(D, SG, RG, W, MQ)
    body, fails, how = [], [], []
    cert = {}
    for n, (_, b, k) in enumerate(leaves_of(tree)):
        if b[4] == b[5]:
            continue
        if k == 'LEB' and g.lebOk(b, rects[0]):
            continue
        if k in SIMPLE and k != 'LEB':
            continue
        lf, why, Sl, Rl = certify(b)
        how.append(why)
        if lf is None:
            fails.append([n, k, [str(x) for x in b], why])
            continue
        name = f"r{idx:05d}l{n}"
        g.leaf_names[b] = (f"{name}_ok", Sl, Rl)
        cert[b] = dict(name=name, S=Sl, R=Rl, D=lf.D, W=lf.W, Q=lf.Q, box=lf.box, wx=lf.wx, wy=lf.wy,
                       ex=lf.ex, ey=lf.ey, chs=lf.chs, cvs=lf.cvs, crs=lf.crs, Ls=lf.Ls, side=lf.side,
                       hbx=lf.hbx, vbx=lf.vbx, certs=lf.certs)
    status = dict(root=idx, kinds=count(tree), fails=fails, how=how, sec=round(time.time() - t0, 1))
    if not fails:
        path = os.path.join(outdir, f"R{idx:05d}.pkl")
        with open(path + ".tmp", 'wb') as f:
            pickle.dump(dict(idx=idx, root=root, tree=tree, leaves=cert), f)
        os.replace(path + ".tmp", path)
    return status


def sorted_cover():
    """The cover with its segments normalised (`segNorm`) and sorted by key (`STree.chainB`)."""
    side, D, W, pts, segs, rects = read_cover(COVER)
    segs = sorted(segs, key=lambda e: e[:4])
    return side, D, W, pts, segs, rects


def stree(segs):
    if not segs:
        return "STree.leaf"
    m = len(segs) // 2
    return f"(STree.node {stree(segs[:m])} {G.ltup(segs[m])} {stree(segs[m + 1:])})"


def data_module(outdir):
    _, D, W, pts, segs, rects = sorted_cover()
    txt = "\n".join([
        "import Sqpack.ExTree",
        "/-! The cover `L4_k02_box7.txt`: segments normalised (`segNorm`) and sorted by key, as a list",
        "(`tsegs`, used by the leaves) and as a search tree (`segsT`); the Lebesgue square (`trects`). -/",
        "namespace SquarePacking.LemmaELeaf", "open ZMTreeM",
        f"def tsegs : List SegE := [{', '.join(G.ltup(e) for e in segs)}]",
        f"def trects : List RectE := [{', '.join(G.ltup(r) for r in rects)}]",
        f"def segsT : STree := {stree(segs)}",
        "set_option maxRecDepth 100000 in",
        "theorem segsT_toList : segsT.toList = tsegs := by decide +kernel",
        "end SquarePacking.LemmaELeaf"]) + "\n"
    with open(os.path.join(outdir, "Data.lean"), 'w') as f:
        f.write(txt)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lo', type=int, default=0)
    ap.add_argument('--hi', type=int, default=10 ** 9)
    ap.add_argument('--nproc', type=int, default=1)
    ap.add_argument('--out', default=os.path.join(HERE, '..', 'v7cert'))
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    jobs = [(i, r, l, a.out) for i, (r, l, u) in enumerate(load(LEAVES)) if a.lo <= i < a.hi
            and not os.path.exists(os.path.join(a.out, f"R{i:05d}.pkl"))]
    print(json.dumps(dict(todo=len(jobs))), flush=True)
    with Pool(a.nproc) as p:
        for st in p.imap_unordered(work, jobs):
            print(json.dumps(st), flush=True)


if __name__ == '__main__':
    main()
