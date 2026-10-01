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
    USE_TAN = True

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
        self.use_tan = Leaf.USE_TAN
        if self.ok:
            self.crs = [self.modes(r) for r in self.crs]

    def modes(self, r):
        """the cap modes of a rectangle (QUADRANT_EXACT.md 4.4, qx2_zm.Exact.u_regime): 'tan' at
        d* = min(1, (dmin + dmax)/2) when d >= cos on the whole box, else std; re-checked by tanAx."""
        D, Q, R = self.D, self.Q, self.R
        x0, x1, y0, y1, U0, U1 = self.box
        u0, u1 = Fr(U0, R), Fr(U1, R)
        c0, s0 = (1 - u0 * u0) / (1 + u0 * u0), 2 * u0 / (1 + u0 * u0)
        if u1 * u1 + 2 * u1 - 1 <= 0:
            c1, s1 = (1 - u1 * u1) / (1 + u1 * u1), 2 * u1 / (1 + u1 * u1)
            w1 = c1 + s1
        else:
            w1 = Fr(14143, 10000)
        w0 = c0 + s0
        out = [r]
        for a, lo, hi, cap, w in ((Fr(r[0], D), Fr(x0, Q), Fr(x1, Q), capX(D, r[0]), self.wx),
                                  (Fr(r[1], D), Fr(y0, Q), Fr(y1, Q), capY(D, r[1]), self.wy)):
            mo = None
            dmax = a - lo + w1 / 2
            dmin = a - hi + w0 / 2
            if self.use_tan and dmax > 0 and dmin >= c0:
                ds = min(Fr(1), (dmin + dmax) / 2)
                cand = (ds.numerator, ds.denominator)
                if tanAx(Q, x0, x1, y0, y1, U0, U1, R, self.wx, self.wy, cap, cand):
                    mo = cand
            out.append(mo)
        return tuple(out)

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
    def choose(self, Dp, X, Y, b0, b1):
        """float-guided certificate at the vertex: (splits, fcs, hc, vc, lc)"""
        R = self.R
        ts = (0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0)
        us = [max(b0 / R + (b1 - b0) / R * t, 1e-9) for t in ts]
        pts = []
        for u in us:
            dv = ev(Dp, u)
            pts.append((u, (ev(X, u) / dv, ev(Y, u) / dv)))
        splits, lc = [], []
        m0 = lowdeg(Dp) if b0 == 0 else 0
        sig = ev(Dp[m0:], (b0 + b1) / 2 / R) > 0
        def qsign(q):
            return [svals(q, u, v) >= 0 for u, v in pts]
        for r in self.crs:
            pair = []
            for cap in (capXm(self.D, r), capYm(self.D, r)):
                ds = [svals(cap, u, v) for u, v in pts]
                ss = [2 * u / (1 + u * u) for u, _ in pts]
                if all(d <= 0 for d in ds): pair.append([('zeroC',)])
                elif all(d >= s for d, s in zip(ds, ss)): pair.append([('linC',)])
                elif all(0 <= d <= s for d, s in zip(ds, ss)): pair.append([('par',)])
                elif any(d < 0 for d in ds):
                    k = len(splits); splits.append((cap, 0, 1, 0, 1))
                    pair.append([('zeroT', k), ('parT', k, True)])
                else:
                    k = len(splits); splits.append((sl_sub(cap, sSL(1)), 0, 1, 0, 1))
                    pair.append([('parT', k, False), ('linT', k)])
            lc.append(tuple(pair))
        tol = 1e-9
        def pick(ups, los, bx):
            Ua, La, posl = set(), set(), []
            for u, v in pts:
                uv = [svals(L, u, v) for L in ups]; lv = [svals(L, u, v) for L in los]
                mu = min(uv); ml = max(lv)
                posl.append(mu - ml > 1e-12)
                if mu - ml > -1e-9:
                    Ua |= {i for i in range(3) if uv[i] <= mu + tol}
                    La |= {i for i in range(3) if lv[i] >= ml - tol}
            if not any(posl): return [(('drop',), None)]
            ch = ('box',) if len(bx[0]) * len(bx[1]) == 1 or len(bx[0]) * len(bx[1]) <= len(Ua) * len(La) \
                else ('alt', sorted(Ua), sorted(La))
            if ch[0] == 'alt' and not segOkA(sig, Dp, X, Y, b0, b1, R, ups, los, ch[1], ch[2]):
                # options crossing inside the sub-bin: widen by float closeness, else the box choice
                ch = ('box',)
                for wtol in (1e-6, 1e-3, 1e-2, 1e-1):
                    Ub, Lb = set(Ua), set(La)
                    for u, v in pts:
                        uv = [svals(L, u, v) for L in ups]; lv = [svals(L, u, v) for L in los]
                        Ub |= {i for i in range(3) if uv[i] <= min(uv) + wtol}
                        Lb |= {i for i in range(3) if lv[i] >= max(lv) - wtol}
                    if len(Ub) * len(Lb) >= len(bx[0]) * len(bx[1]): break
                    if segOkA(sig, Dp, X, Y, b0, b1, R, ups, los, sorted(Ub), sorted(Lb)):
                        ch = ('alt', sorted(Ub), sorted(Lb)); break
            if all(posl): return [(ch, None)]
            # mixed: tag by a split whose sign pattern matches
            for k, sp in enumerate(splits):
                sg = qsign(sp[0])
                if sg == posl: return [(('drop',), (k, False)), (ch, (k, True))]
                if [not x for x in sg] == posl: return [(('drop',), (k, True)), (ch, (k, False))]
            return [(('drop',), None), (ch, None)]
        hc = [pick(hUps(self.D, e), hLos(self.D, e), bx) for e, bx in zip(self.chs, self.hbx)]
        vc = [pick(vUps(self.D, e), vLos(self.D, e), bx) for e, bx in zip(self.cvs, self.vbx)]
        return [splits, [], hc, vc, lc]

    def factor_certs(self, sig, Dp, X, Y, b0, b1, cert):
        """common-factor certificates for the failing combinations (sympy gcd)"""
        import sympy
        splits, fcs, hc, vc, lc = cert
        uu = sympy.Symbol('u')
        def topoly(p): return sympy.Poly(list(reversed(p)) or [0], uu)
        def tolist(P):
            c = P.all_coeffs(); return [int(x) for x in reversed(c)]
        out = []
        for k, sp in enumerate(splits):
            sq = snum(sig, atV(sp[0], Dp, X, Y))
            Pq = topoly(sq)
            if Pq.is_zero: continue
            # gcd with a few failing totals: use the full sum with each pattern's first combination
            for pat in pats(len(splits)):
                alts = []
                for e, bx, l in zip(self.chs, self.hbx, hc):
                    alts.append([t for x in l if tagOk(pat, x[1]) for t in segCAlts(Dp, X, Y, e[4], self.D, nat_sub(e[2], e[0]), hUps(self.D, e), hLos(self.D, e), bx, x[0])])
                for e, bx, l in zip(self.cvs, self.vbx, vc):
                    alts.append([t for x in l if tagOk(pat, x[1]) for t in segCAlts(Dp, X, Y, e[4], self.D, nat_sub(e[3], e[1]), vUps(self.D, e), vLos(self.D, e), bx, x[0])])
                for r, (xs, ys) in zip(self.crs, lc):
                    alts.append([lebRF(Dp, X, Y, self.D, r, ax, ay) for ax in xs if tagOk(pat, capTag(ax)) for ay in ys if tagOk(pat, capTag(ay))])
                sps = [sproc(Dp, X, Y, s_, b) for s_, b in zip(splits, pat)]
                for comb in cprod(alts):
                    T = sumRF(Dp, comb + sps + [rf_const(-self.W, 1)])
                    if ckRF(sig, T, b0, b1, self.R): continue
                    G = sympy.gcd(topoly(snum(sig, T)), Pq)
                    if G.degree() < 1: continue
                    G = sympy.Poly(sympy.primitive(G.as_expr())[1], uu)
                    Gl = tolist(G)
                    g1P, rem = sympy.div(Pq, G)
                    if not rem.is_zero: continue
                    g1 = tolist(g1P)
                    if not all(isinstance(x, int) for x in g1): continue
                    m = 0
                    while m < len(g1) and g1[m] == 0: m += 1
                    for sgn in (1, -1):
                        gg = [sgn * x for x in g1]; GG = [sgn * x for x in Gl]
                        if checkPos(gg[m:], nat_sub(len(gg[m:]), 1), b0, b1, self.R):
                            f = (k, GG, gg, m)
                            if f not in out: out.append(f)
        return out

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
            cert = self.choose(Dp, X, Y, b0, b1)
            args = (self.D, self.W, sig, Dp, X, Y, b0, b1, R, self.chs, self.cvs, self.crs, self.hbx, self.vbx)
            nc = 1
            for l, bx in list(zip(cert[2], self.hbx)) + list(zip(cert[3], self.vbx)):
                nc *= sum(len(bx[0]) * len(bx[1]) if x[0][0] == 'box' else
                          (len(x[0][1]) * len(x[0][2]) if x[0][0] == 'alt' else 1) for x in l)
            if nc > 16 and depth < self.maxdepth and b1 - b0 >= 2:
                pass
            elif vertOk(*args, cert):
                self.stat['val'] += 1
                return [(b1, sig, m, ('val', cert))]
            if cert[0]:
                fcs = self.factor_certs(sig, Dp, X, Y, b0, b1, cert)
                if fcs:
                    cert[1] = fcs
                    if vertOk(*args, cert):
                        self.stat['val'] += 1; self.stat['fc'] = self.stat.get('fc', 0) + 1
                        return [(b1, sig, m, ('val', cert))]
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


def lmode(mo):
    return "none" if mo is None else f"some ({mo[0]}, {mo[1]})"


def lrm(rm):
    return f"({ltup(rm[0])}, {lmode(rm[1])}, {lmode(rm[2])})"


def ltup(t):
    return "(" + ", ".join(str(x) for x in t) + ")"


def lnat(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def lsegc(o):
    if o[0] == 'drop': return ".drop"
    if o[0] == 'box': return ".box"
    return f"(.alt {lnat(o[1])} {lnat(o[2])})"


def ltag(t):
    return "none" if t is None else f"some ({t[0]}, {'true' if t[1] else 'false'})"


def lcapa(a):
    if a[0] in ('zeroC', 'par', 'linC'): return "." + a[0]
    if a[0] == 'parT': return f"(.parT {a[1]} {'true' if a[2] else 'false'})"
    return f"(.{a[0]} {a[1]})"


def lSL(L):
    return f"⟨{lPL(L[0])}, {L[1]}, {L[2]}, {L[3]}, {L[4]}⟩"


def lbx(b):
    return f"({lnat(b[0])}, {lnat(b[1])})"


def lvcert(c):
    splits, fcs, hc, vc, lc = c
    sp = ", ".join(f"⟨{lSL(q)}, {nm}, {dm}, {np_}, {dp}⟩" for q, nm, dm, np_, dp in splits)
    fc = ", ".join(f"⟨{k}, {lpoly(G)}, {lpoly(g1)}, {m}⟩" for k, G, g1, m in fcs)
    h = ", ".join("[" + ", ".join(f"({lsegc(x[0])}, {ltag(x[1])})" for x in l) + "]" for l in hc)
    v = ", ".join("[" + ", ".join(f"({lsegc(x[0])}, {ltag(x[1])})" for x in l) + "]" for l in vc)
    l_ = ", ".join(f"([{', '.join(lcapa(a) for a in xs)}], [{', '.join(lcapa(a) for a in ys)}])" for xs, ys in lc)
    return f"⟨[{sp}], [{fc}], [{h}], [{v}], [{l_}]⟩"


def lsub(sb):
    b1, sig, m, kind = sb
    if kind[0] == 'out':
        k = f".out {kind[1]} {kind[2]}"
    else:
        k = f"(.val {lvcert(kind[1])})"
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
            f"  crs := [{', '.join(lrm(r) for r in lf.crs)}]\n"
            f"  Ls := [{', '.join(lPL(P) for P in lf.Ls)}]\n"
            f"  hbx := [{', '.join(lbx(b) for b in lf.hbx)}]\n"
            f"  vbx := [{', '.join(lbx(b) for b in lf.vbx)}]\n"
            f"  certs := [\n    {rows}]\n")



def to_lean_split(lf, name, segs="tsegs", rects="trects", rows_only=False):
    """The leaf and its `exOk` theorem, the pair certificates checked one `decide` per pair
    (or per row) and glued along `List.drop`."""
    x0, x1, y0, y1, U0, U1 = lf.box
    D, S, R, W, Q = lf.D, lf.S, lf.R, lf.W, lf.Q
    side = f"(sideL {Q} {x0} {x1} {y0} {y1} {name}.wx {name}.wy)"
    ctx = f"{D} {W} {R} {U0} {U1} {side} {name}.chs {name}.cvs {name}.crs {name}.hbx {name}.vbx"
    d0 = "(([0], [0], [0]) : PL)"
    q0 = "((([0], [0], [0]) : PL), PairCert.par)"
    n = len(lf.side) + len(lf.Ls)
    out = [to_lean(lf, name)]
    out.append(f"def {name}_L : List PL := {side} ++ {name}.Ls\n")
    out.append(f"def {name}_Z (i : ℕ) : List (PL × PairCert) := ({name}_L.drop (i + 1)).zip ({name}.certs.getD i [])\n")
    out.append(f"def {name}_p (i : ℕ) : PL × PairCert → Bool := fun q => pairOk {ctx} ({name}_L.getD i {d0}) q.1 q.2\n")
    dk = "by decide +kernel"
    for i in range(n):
        m = len(lf.certs[i]) if i < len(lf.certs) else 0
        if rows_only:
            body = f"rowOk_of ({dk}) ({dk})"
        else:
            for j in range(m):
                out.append(f"theorem {name}_{i}_{j} : {name}_p {i} (({name}_Z {i}).getD {j} {q0}) = true := {dk}\n")
            t = f"all_drop_end ({name}_p {i}) ({name}_Z {i}) {m} ({dk})"
            for j in reversed(range(m)):
                t = f"all_drop_step ({name}_p {i}) ({name}_Z {i}) {j} {q0} ({dk}) {name}_{i}_{j}\n    ({t})"
            body = f"rowOk_of ({dk})\n    ({t})"
        out.append(f"theorem {name}_r{i} : rowOk {ctx} ({name}_L.getD {i} {d0}) ({name}_L.drop {i + 1}) "
                   f"({name}.certs.getD {i} []) = true :=\n  {body}\n")
    t = f"allPairsOk_drop_end {name}_L ({name}.certs.drop {n}) {n} ({dk})"
    for i in reversed(range(n)):
        t = f"allPairsOk_drop_step {name}_L {name}.certs {i} {d0} ({dk}) ({dk}) {name}_r{i}\n    ({t})"
    args = f"{D} {S} {R} {W} {x0} {x1} {y0} {y1} {U0} {U1} {segs} {rects} {name}"
    out.append(f"theorem {name}_head : exHead {args} = true := {dk}\n")
    out.append(f"theorem {name}_ok : exOk {args} = true :=\n  exOk_of {name}_head\n    ({t})\n")
    return "\n".join(out)
