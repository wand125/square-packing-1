#!/usr/bin/env python3
"""Lean modules from the pickled certificates of run_v7.py: one module per root, the pair
certificates encoded (`LemmaEDec.decPC`, `enc_cert.py`).

    emit_v7.py --cert DIR --out DIR [--lo I --hi J] [--nproc N]
"""
import argparse, glob, os, pickle, sys
sys.set_int_max_str_digits(0)
from multiprocessing import Pool
from types import SimpleNamespace

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_exact as G  # noqa: E402
from gen_tree import Glue  # noqa: E402
from enc_cert import enc_pc  # noqa: E402
from run_v7 import SG, RG, MQ, sorted_cover  # noqa: E402


def to_lean_enc(lf, name):
    rows = ",\n    ".join("[" + ", ".join("decPC [" + ",".join(map(str, enc_pc(c))) + "]" for c in row) + "]"
                           for row in lf.certs)
    return (f"def {name} : ExLeaf where\n"
            f"  wx := {'true' if lf.wx else 'false'}\n  wy := {'true' if lf.wy else 'false'}\n"
            f"  chs := [{', '.join(G.ltup(e) for e in lf.chs)}]\n"
            f"  cvs := [{', '.join(G.ltup(e) for e in lf.cvs)}]\n"
            f"  crs := [{', '.join(G.lrm(r) for r in lf.crs)}]\n"
            f"  Ls := [{', '.join(G.lPL(P) for P in lf.Ls)}]\n"
            f"  hbx := [{', '.join(G.lbx(b) for b in lf.hbx)}]\n"
            f"  vbx := [{', '.join(G.lbx(b) for b in lf.vbx)}]\n"
            f"  certs := [\n    {rows}]\n"
            + ("  ex := true\n" if lf.ex else "") + ("  ey := true\n" if lf.ey else ""))


G.to_lean = to_lean_enc
_rects = None


def emit(path, outdir):
    global _rects
    if _rects is None:
        _rects = sorted_cover()[5]
    d = pickle.load(open(path, 'rb'))
    idx, root, tree = d['idx'], d['root'], d['tree']
    g = Glue(5, SG, RG, 10 ** 12, MQ)
    body = []
    for b, c in d['leaves'].items():
        lf = SimpleNamespace(**c)
        body.append(G.to_lean_split(lf, c['name']))
        g.leaf_names[b] = (f"{c['name']}_ok", c['S'], c['R'])
    hdr = ["import Sqpack.V7.Data", "import Sqpack.LemmaEDec", "namespace SquarePacking.LemmaELeaf",
           "open ZMTreeM LemmaEVert LemmaEPoly ZMTree", "set_option maxRecDepth 100000",
           "set_option maxHeartbeats 0"]
    txt = "\n".join(hdr + body + [g.root_thm(f"root_{idx:05d}", root, tree, _rects),
                                  "end SquarePacking.LemmaELeaf"]) + "\n"
    out = os.path.join(outdir, f"R{idx:05d}.lean")
    with open(out + ".tmp", 'w') as f:
        f.write(txt)
    os.replace(out + ".tmp", out)
    return idx, len(txt)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cert', default=os.path.join(HERE, '..', 'v7cert'))
    ap.add_argument('--out', default=os.path.join(HERE, '..', 'Sqpack', 'V7'))
    ap.add_argument('--lo', type=int, default=0)
    ap.add_argument('--hi', type=int, default=10 ** 9)
    ap.add_argument('--nproc', type=int, default=1)
    a = ap.parse_args()
    paths = sorted(p for p in glob.glob(os.path.join(a.cert, 'R*.pkl'))
                   if a.lo <= int(os.path.basename(p)[1:6]) < a.hi)
    with Pool(a.nproc) as pool:
        tot = 0
        for idx, n in pool.starmap(emit, [(p, a.out) for p in paths]):
            tot += n
    print(len(paths), "modules", tot, "bytes")


if __name__ == '__main__':
    main()
