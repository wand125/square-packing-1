#!/usr/bin/env python3
"""EXACT leaves (Lemma E, `LemmaELeaf.lean`): build an `ExLeaf` certificate for a pose box.

    gen_exact.py COVER S R x0 x1 y0 y1 U0 U1 [--lean NAME]

Box: centres [x0, x1] x [y0, y1] over Q = D*S, angles u in (U0/R, U1/R].  The search uses floats
only to choose; every decision is re-checked with the exact mirror `lemmae_mirror.py`, which computes
what the kernel computes.
"""
import sys, time, argparse
from fractions import Fraction as Fr
from lemmae_mirror import *
from gen_axis import read_cover


def ev(p, u):
    s = 0.0
    for a in reversed(p):
        s = s * u + a
    return s


def lowdeg(p):
    m = 0
    while m < len(p) and p[m] == 0:
        m += 1
    return m


def svals(L, u, v):
    """float value of a scaled line at the point v and angle u"""
    P, i, j, k, d = L
    den = (1 - u * u) ** i * (2 * u) ** j * (1 + u * u) ** k * d
    return (ev(P[0], u) * v[0] + ev(P[1], u) * v[1] + ev(P[2], u)) / den


class Leaf:
    def __init__(self, cover, S, R, x0, x1, y0, y1, U0, U1, maxdepth=8):
        side_, D, W, pts, segs, rects = cover
        self.D, self.W, self.S, self.R = D, W, S, R
        self.Q = Q = D * S
        self.box = (x0, x1, y0, y1, U0, U1)
        self.maxdepth = maxdepth
        reach = 0.7072
        cx0, cx1, cy0, cy1 = x0 / Q, x1 / Q, y0 / Q, y1 / Q
        self.chs = [e for e in segs if e[1] == e[3] and e[0] < e[2]
                    and cy0 - reach <= e[1] / D <= cy1 + reach
                    and e[2] / D >= cx0 - reach and e[0] / D <= cx1 + reach]
        self.cvs = [e for e in segs if e[0] == e[2] and e[1] < e[3]
                    and cx0 - reach <= e[0] / D <= cx1 + reach
                    and e[3] / D >= cy0 - reach and e[1] / D <= cy1 + reach]
        wN, wD = widN(R, U0, U1), widD(R, U0)
        self.crs = [r for r in rects
                    if 2 * x1 * wD + D * S * wN <= 2 * r[2] * S * wD
                    and 2 * y1 * wD + D * S * wN <= 2 * r[3] * S * wD
                    and r[0] / D <= cx1 + reach and r[1] / D <= cy1 + reach]
        # lower sides: the wall where it is above the box side on the whole bin
        def wall(x):
            w0 = (1 - (U0 / R) ** 2 + 2 * U0 / R) / (1 + (U0 / R) ** 2) / 2
            w1 = (1 - (U1 / R) ** 2 + 2 * U1 / R) / (1 + (U1 / R) ** 2) / 2
            if w1 <= x / Q: return False
            if w0 >= x / Q: return True
            return None
        self.wx, self.wy = wall(x0), wall(y0)
        self.ok = self.wx is not None and self.wy is not None

    def pins(self):
        D, Q, R = self.D, self.Q, self.R
        x0, x1, y0, y1, U0, U1 = self.box
        Ls = []
        forms = [L for e in self.chs for L in hFormsSLs(D, e)] + \
            [L for e in self.cvs for L in vFormsSLs(D, e)] + [L for r in self.crs for L in lebSLs(D, r)]
        for L in forms:
            P = L[0]
            if P in Ls: continue
            if cornersOk(Q, x0, x1, y0, y1, U0, U1, R, self.wx, self.wy, False, P): continue
            if cornersOk(Q, x0, x1, y0, y1, U0, U1, R, self.wx, self.wy, True, P): continue
            Ls.append(P)
        self.Ls = Ls
        self.side = sideL(Q, x0, x1, y0, y1, self.wx, self.wy)
        import itertools
        def boxalts(ups, los):
            for k in (1, 2, 3):
                for Ua in itertools.combinations(range(3), k):
                    for kk in (1, 2, 3):
                        for La in itertools.combinations(range(3), kk):
                            if boxDomOk(Q, x0, x1, y0, y1, U0, U1, R, self.wx, self.wy, ups, los,
                                        (list(Ua), list(La))):
                                return (list(Ua), list(La))
        self.hbx = [boxalts(hUps(D, e), hLos(D, e)) for e in self.chs]
        self.vbx = [boxalts(vUps(D, e), vLos(D, e)) for e in self.cvs]
        return Ls

    # -------------------------------------------------------------- one sub-bin of a pair
    def choose(self, Dp, X, Y, b0, b1, lam=(1, 1)):
        """float-guided choices at the vertex: per segment ('drop',) / ('box',) / ('alt', Ua, La),
        per rectangle the cap modes"""
        R = self.R
        ts = (0.0, 0.25, 0.5, 0.75, 1.0)
        us = [max(b0 / R + (b1 - b0) / R * t, 1e-9) for t in ts]
        pts = []
        for u in us:
            dv = ev(Dp, u)
            pts.append((u, (ev(X, u) / dv, ev(Y, u) / dv)))
        tol = 1e-9
        def pick(ups, los, bx):
            Ua, La, pos = set(), set(), False
            for u, v in pts:
                uv = [svals(L, u, v) for L in ups]; lv = [svals(L, u, v) for L in los]
                mu = min(uv); ml = max(lv)
                Ua |= {i for i in range(3) if uv[i] <= mu + tol}
                La |= {i for i in range(3) if lv[i] >= ml - tol}
                if mu - ml > 1e-12: pos = True
            if not pos: return ('drop',)
            if len(bx[0]) * len(bx[1]) <= len(Ua) * len(La): return ('box',)
            return ('alt', sorted(Ua), sorted(La))
        hc = [pick(hUps(self.D, e), hLos(self.D, e), bx) for e, bx in zip(self.chs, self.hbx)]
        vc = [pick(vUps(self.D, e), vLos(self.D, e), bx) for e, bx in zip(self.cvs, self.vbx)]
        lc = []
        for r in self.crs:
            modes = []
            for cap in (capX(self.D, r[0]), capY(self.D, r[1])):
                ds = [svals(cap, u, v) for u, v in pts]
                ss = [2 * u / (1 + u * u) for u, _ in pts]
                if all(d <= 0 for d in ds): modes.append(('zero',))
                elif all(d >= s for d, s in zip(ds, ss)): modes.append(('lin',))
                elif all(0 <= d <= s for d, s in zip(ds, ss)): modes.append(('par',))
                elif any(d < 0 for d in ds): modes.append(('zp', 0, 1, lam[0], lam[1]))
                else: modes.append(('pl', lam[0], lam[1], 0, 1))
            lc.append(tuple(modes))
        ncomb = 1
        for o, bx in zip(hc + vc, self.hbx + self.vbx):
            if o[0] == 'box': ncomb *= len(bx[0]) * len(bx[1])
            elif o[0] == 'alt': ncomb *= len(o[1]) * len(o[2])
        for mx, my in lc:
            ncomb *= (2 if mx[0] in ('zp', 'pl') else 1) * (2 if my[0] in ('zp', 'pl') else 1)
        return hc, vc, lc, ncomb

    def sub(self, P, Qp, b0, b1, depth):
        """certificates for [b0, b1] (list of sub-bins), or None"""
        R = self.R
        Dp = detP(P, Qp); X = xP(P, Qp); Y = yP(P, Qp)
        m = lowdeg(Dp) if b0 == 0 else 0
        q = Dp[m:]
        sig = ev(q, (b0 + b1) / 2 / R) > 0
        ok = signOk(sig, Dp, m, b0, b1, R)
        if ok:
            for k, Sd in enumerate(self.side):
                nm = atV((Sd, 0, 0, 0, 1), Dp, X, Y)[0]
                mm = lowdeg(nm) if b0 == 0 else 0
                q2 = nm[mm:]
                q2 = q2 if (not sig) else psmul(-1, q2)
                if checkPos(q2, nat_sub(len(nm[mm:]), 1), b0, b1, R):
                    self.stat['out'] += 1
                    return [(b1, sig, m, ('out', k, mm))]
            for lam in ((1, 1), (1, 8), (1, 64)):
                hc, vc, lc, ncomb = self.choose(Dp, X, Y, b0, b1, lam)
                if ncomb <= 128 and vertOk(self.D, self.W, sig, Dp, X, Y, b0, b1, R, self.chs, self.cvs,
                                           self.crs, self.hbx, self.vbx, hc, vc, lc):
                    self.stat['val'] += 1
                    return [(b1, sig, m, ('val', hc, vc, lc))]
                if not any(mx[0] in ('zp', 'pl') or my[0] in ('zp', 'pl') for mx, my in lc):
                    break
        if depth >= self.maxdepth or b1 - b0 < 2:
            return None
        mid = (b0 + b1) // 2
        a = self.sub(P, Qp, b0, mid, depth + 1)
        if a is None: return None
        b = self.sub(P, Qp, mid, b1, depth + 1)
        if b is None: return None
        self.stat['split'] += 1
        return a + b

    def run(self):
        self.stat = dict(par=0, out=0, val=0, split=0, fail=0)
        self.pins()
        allL = self.side + self.Ls
        U0, U1 = self.box[4], self.box[5]
        certs = []
        for i in range(len(allL)):
            row = []
            for j in range(i + 1, len(allL)):
                Dp = detP(allL[i], allL[j])
                if all(c == 0 for c in Dp):
                    self.stat['par'] += 1; row.append('par'); continue
                c = self.sub(allL[i], allL[j], U0, U1, 0)
                if c is None:
                    self.stat['fail'] += 1
                    return None
                row.append(c)
            certs.append(row)
        self.certs = certs
        return certs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cover'); ap.add_argument('S', type=int); ap.add_argument('R', type=int)
    ap.add_argument('box', nargs=6, type=int)
    ap.add_argument('--maxdepth', type=int, default=8)
    a = ap.parse_args()
    cov = read_cover(a.cover)
    t = time.process_time()
    lf = Leaf(cov, a.S, a.R, *a.box, maxdepth=a.maxdepth)
    if not lf.ok:
        print("wall crosses the box side within the bin"); return
    c = lf.run()
    print(f"claims {len(lf.chs)}+{len(lf.cvs)} segs, {len(lf.crs)} rects; Ls {len(lf.Ls)}; "
          f"{'OK' if c else 'FAIL'} {lf.stat} {time.process_time() - t:.1f}s")


if __name__ == '__main__':
    main()


# ---------------------------------------------------------------- Lean output
def lpoly(p):
    return "[" + ", ".join(str(c) for c in p) + "]"


def lPL(P):
    return f"({lpoly(P[0])}, {lpoly(P[1])}, {lpoly(P[2])})"


def ltup(t):
    return "(" + ", ".join(str(x) for x in t) + ")"


def lnat(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def lsegc(o):
    if o[0] == 'drop': return ".drop"
    if o[0] == 'box': return ".box"
    return f".alt {lnat(o[1])} {lnat(o[2])}"


def lcap(m):
    if m[0] in ('zero', 'par', 'lin'): return "." + m[0]
    return f"(.{m[0]} {m[1]} {m[2]} {m[3]} {m[4]})"


def lbx(b):
    return f"({lnat(b[0])}, {lnat(b[1])})"


def lsub(sb):
    b1, sig, m, kind = sb
    if kind[0] == 'out':
        k = f".out {kind[1]} {kind[2]}"
    else:
        _, hc, vc, lc = kind
        k = (".val ⟨[" + ", ".join(lsegc(o) for o in hc) + "], [" + ", ".join(lsegc(o) for o in vc) +
             "], [" + ", ".join(f"({lcap(a)}, {lcap(b)})" for a, b in lc) + "]⟩")
    return f"⟨{b1}, {'true' if sig else 'false'}, {m}, {k}⟩"


def lcert(c):
    if c == 'par':
        return ".par"
    return ".bins [" + ", ".join(lsub(sb) for sb in c) + "]"


def to_lean(lf, name):
    rows = ",\n    ".join("[" + ", ".join(lcert(c) for c in row) + "]" for row in lf.certs)
    return (f"def {name} : ExLeaf where\n"
            f"  wx := {'true' if lf.wx else 'false'}\n  wy := {'true' if lf.wy else 'false'}\n"
            f"  chs := [{', '.join(ltup(e) for e in lf.chs)}]\n"
            f"  cvs := [{', '.join(ltup(e) for e in lf.cvs)}]\n"
            f"  crs := [{', '.join(ltup(r) for r in lf.crs)}]\n"
            f"  Ls := [{', '.join(lPL(P) for P in lf.Ls)}]\n"
            f"  hbx := [{', '.join(lbx(b) for b in lf.hbx)}]\n"
            f"  vbx := [{', '.join(lbx(b) for b in lf.vbx)}]\n"
            f"  certs := [\n    {rows}]\n")
