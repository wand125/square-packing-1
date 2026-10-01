"""Exact mirror of the kernel computations of Lemma E (`BernsteinZ`, `RatU`, `LemmaEPoly`,
`LemmaEVert`, `LemmaELeaf`).

Every function here computes exactly what the Lean definition of the same name computes (same list
shapes, since `List.contains` compares polynomial triples syntactically).  Integers only.
"""
from math import comb, gcd


# ---------------------------------------------------------------- BernsteinZ
def padd(p, q):
    out = []
    for i in range(max(len(p), len(q))):
        if i < len(p) and i < len(q):
            out.append(p[i] + q[i])
        elif i < len(p):
            out.append(p[i])
        else:
            out.append(q[i])
    return out


def psmul(c, p):
    return [c * a for a in p]


def pmul(p, q):
    # mul [] _ = []; mul (a :: p) q = add (smul a q) (0 :: mul p q)
    if not p:
        return []
    return padd(psmul(p[0], q), [0] + pmul(p[1:], q))


def hom(U0, H, R, n, p):
    if not p:
        return []
    if len(p) == 1:
        return [p[0] * R ** n]
    return padd([p[0] * R ** n], pmul([U0, H], hom(U0, H, R, max(n - 1, 0), p[1:])))


def chooseF(n, k):
    return comb(n, k) if k <= n else 0


def gamK(n, b, i):
    return sum(chooseF(n - k, i - k) * (b[k] if k < len(b) else 0) for k in range(i + 1))


def tpoly(p, n, U0, U1, R):
    return hom(U0, U1 - U0, R, n, p)


def check(p, n, U0, U1, R):
    if len(p) > n + 1:
        return False
    t = tpoly(p, n, U0, U1, R)
    if len(t) > n + 1:
        return False
    return all(gamK(n, t, i) >= 0 for i in range(n + 1))


def checkPos(p, n, U0, U1, R):
    if not check(p, n, U0, U1, R):
        return False
    t = tpoly(p, n, U0, U1, R)
    return gamK(n, t, 0) > 0 and gamK(n, t, n) > 0


def nat_sub(a, b):
    return a - b if a > b else 0


# ---------------------------------------------------------------- RatU
Cp = [1, 0, -1]
Sp = [0, 2]
Np = [1, 0, 1]


def ppow(p, n):
    out = [1]
    for _ in range(n):
        out = pmul(p, out)
    return out


# RF = (num, e, i, j, k, d)
def rf_const(n, d):
    return ([n], 0, 0, 0, 0, d)


def raise_(D, r, a, b, c, g, m):
    num, e, i, j, k, d = r
    num2 = pmul(psmul(m, num), pmul(ppow(D, a), pmul(ppow(Cp, b), pmul(ppow(Sp, c), ppow(Np, g)))))
    return (num2, e + a, i + b, j + c, k + g, d * m)


def lcm(a, b):
    return a * b // gcd(a, b) if a and b else 0


def rf_add(D, r, s):
    e = max(r[1], s[1]); i = max(r[2], s[2]); j = max(r[3], s[3]); k = max(r[4], s[4])
    l = lcm(r[5], s[5])
    r2 = raise_(D, r, e - r[1], i - r[2], j - r[3], k - r[4], l // r[5])
    s2 = raise_(D, s, e - s[1], i - s[2], j - s[3], k - s[4], l // s[5])
    return (padd(r2[0], s2[0]), e, i, j, k, l)


def rf_mul(r, s):
    return (pmul(r[0], s[0]), r[1] + s[1], r[2] + s[2], r[3] + s[3], r[4] + s[4], r[5] * s[5])


def rf_neg(r):
    return (psmul(-1, r[0]),) + tuple(r[1:])


def checkRF(sigma, r, n, U0, U1, R):
    num = r[0] if (sigma or r[1] % 2 == 0) else psmul(-1, r[0])
    return check(num, n, U0, U1, R)


def ckRF(sigma, r, b0, b1, R):
    return checkRF(sigma, r, nat_sub(len(r[0]), 1), b0, b1, R)


# ---------------------------------------------------------------- LemmaEPoly
# PL = (a, b, k) polynomials;  SL = (P, i, j, k, d)
def addPL(P, Q):
    return (padd(P[0], Q[0]), padd(P[1], Q[1]), padd(P[2], Q[2]))


def mulPL(p, P):
    return (pmul(p, P[0]), pmul(p, P[1]), pmul(p, P[2]))


def negPL(P):
    return (psmul(-1, P[0]), psmul(-1, P[1]), psmul(-1, P[2]))


def sdenP(L):
    return pmul(ppow(Cp, L[1]), pmul(ppow(Sp, L[2]), pmul(ppow(Np, L[3]), [L[4]])))


def sl_sub(L, M):
    return (addPL(mulPL(sdenP(M), L[0]), negPL(mulPL(sdenP(L), M[0]))),
            L[1] + M[1], L[2] + M[2], L[3] + M[3], L[4] * M[4])


def sl_cst(n, d):
    return (([0], [0], [n]), 0, 0, 0, d)


def atV(L, D, X, Y):
    P = L[0]
    return (padd(padd(pmul(P[0], X), pmul(P[1], Y)), pmul(P[2], D)), 1, L[1], L[2], L[3], L[4])


def tw(Dn, p):
    return psmul(2 * Dn, p)


def hTA(Dn, Y): return ((tw(Dn, Cp), tw(Dn, Sp), padd(psmul(-Dn, Np), psmul(-2 * Y, Sp))), 1, 0, 0, 2 * Dn)
def hTB(Dn, Y): return ((tw(Dn, Sp), psmul(-1, tw(Dn, Cp)), padd(psmul(2 * Y, Cp), psmul(-Dn, Np))), 0, 1, 0, 2 * Dn)
def hTC(Dn, Y): return ((tw(Dn, Cp), tw(Dn, Sp), padd(psmul(Dn, Np), psmul(-2 * Y, Sp))), 1, 0, 0, 2 * Dn)
def hTD(Dn, Y): return ((tw(Dn, Sp), psmul(-1, tw(Dn, Cp)), padd(psmul(2 * Y, Cp), psmul(Dn, Np))), 0, 1, 0, 2 * Dn)
def vLXs(Dn, X): return ((tw(Dn, Cp), tw(Dn, Sp), padd(psmul(-Dn, Np), psmul(-2 * X, Cp))), 0, 1, 0, 2 * Dn)
def vUXs(Dn, X): return ((tw(Dn, Cp), tw(Dn, Sp), padd(psmul(Dn, Np), psmul(-2 * X, Cp))), 0, 1, 0, 2 * Dn)
def vLYs(Dn, X): return ((psmul(-1, tw(Dn, Sp)), tw(Dn, Cp), padd(psmul(2 * X, Sp), psmul(-Dn, Np))), 1, 0, 0, 2 * Dn)
def vUYs(Dn, X): return ((psmul(-1, tw(Dn, Sp)), tw(Dn, Cp), padd(psmul(2 * X, Sp), psmul(Dn, Np))), 1, 0, 0, 2 * Dn)
def capX(Dn, X0): return ((psmul(-2 * Dn, Np), [0], padd(psmul(2 * X0, Np), psmul(Dn, padd(Cp, Sp)))), 0, 0, 1, 2 * Dn)
def capY(Dn, Y0): return (([0], psmul(-2 * Dn, Np), padd(psmul(2 * Y0, Np), psmul(Dn, padd(Cp, Sp)))), 0, 0, 1, 2 * Dn)
def sSL(h): return (([0], [0], Sp), 0, 0, 1, h)


# ---------------------------------------------------------------- LemmaEVert
def hUps(Dn, e): return [sl_cst(e[2], Dn), hTC(Dn, e[1]), hTD(Dn, e[1])]
def hLos(Dn, e): return [sl_cst(e[0], Dn), hTA(Dn, e[1]), hTB(Dn, e[1])]
def vUps(Dn, e): return [sl_cst(e[3], Dn), vUXs(Dn, e[0]), vUYs(Dn, e[0])]
def vLos(Dn, e): return [sl_cst(e[1], Dn), vLXs(Dn, e[0]), vLYs(Dn, e[0])]


def signOk(sigma, D, m, b0, b1, R):
    if any(c != 0 for c in D[:m]):
        return False
    q = D[m:]
    return checkPos(q if sigma else psmul(-1, q), nat_sub(len(q), 1), b0, b1, R)


def segOkA(sigma, D, X, Y, b0, b1, R, ups, los, Ua, La):
    if not Ua or not La or not all(a < len(ups) for a in Ua) or not all(b < len(los) for b in La):
        return False
    return all(any(ckRF(sigma, atV(sl_sub(U, ups[a]), D, X, Y), b0, b1, R) for a in Ua) for U in ups) and \
        all(any(ckRF(sigma, atV(sl_sub(los[b], L), D, X, Y), b0, b1, R) for b in La) for L in los)


def segVal(D, X, Y, w, Dn, ln, ups, los, iu, il):
    return rf_mul(rf_const(w * Dn, ln), atV(sl_sub(ups[iu], los[il]), D, X, Y))


def ghOk(sigma, D, X, Y, b0, b1, R, cap, mode):
    if mode == 0:
        return ckRF(sigma, atV(sl_sub(sl_cst(0, 1), cap), D, X, Y), b0, b1, R)
    if mode == 1:
        return True
    return ckRF(sigma, atV(sl_sub(cap, sSL(1)), D, X, Y), b0, b1, R)


def ghU(D, X, Y, cap, mode):
    if mode == 0:
        return rf_const(0, 1)
    if mode == 1:
        a = atV(cap, D, X, Y)
        return rf_mul(rf_mul(a, a), (pmul(Np, Np), 0, 1, 1, 0, 2))
    return rf_mul(atV(sl_sub(cap, sSL(2)), D, X, Y), (Np, 0, 1, 0, 0, 1))


def lebVal(D, X, Y, Dn, r, mx, my):
    return rf_mul(rf_const(r[4], 1),
                  rf_add(D, rf_add(D, rf_const(1, 1), rf_neg(ghU(D, X, Y, capX(Dn, r[0]), mx))),
                         rf_neg(ghU(D, X, Y, capY(Dn, r[1]), my))))


def sumRF(D, rs):
    out = rf_const(0, 1)
    for r in reversed(rs):
        out = rf_add(D, r, out)
    return out


def segAlts(D, X, Y, w, Dn, ln, ups, los, Ua, La):
    return [segVal(D, X, Y, w, Dn, ln, ups, los, a, b) for a in Ua for b in La]


def hAlts(D, X, Y, Dn, e, o):
    if o is None:
        return [rf_const(0, 1)]
    return segAlts(D, X, Y, e[4], Dn, nat_sub(e[2], e[0]), hUps(Dn, e), hLos(Dn, e), o[0], o[1])


def vAlts(D, X, Y, Dn, e, o):
    if o is None:
        return [rf_const(0, 1)]
    return segAlts(D, X, Y, e[4], Dn, nat_sub(e[3], e[1]), vUps(Dn, e), vLos(Dn, e), o[0], o[1])


def cprod(Ls):
    out = [[]]
    for l in reversed(Ls):
        out = [[a] + c for a in l for c in out]
    return out


def vertOk(Dn, W, sigma, D, X, Y, b0, b1, R, chs, cvs, crs, hc, vc, lc):
    if len(hc) != len(chs) or len(vc) != len(cvs) or len(lc) != len(crs):
        return False
    for e, o in zip(chs, hc):
        if o is not None and not segOkA(sigma, D, X, Y, b0, b1, R, hUps(Dn, e), hLos(Dn, e), o[0], o[1]):
            return False
    for e, o in zip(cvs, vc):
        if o is not None and not segOkA(sigma, D, X, Y, b0, b1, R, vUps(Dn, e), vLos(Dn, e), o[0], o[1]):
            return False
    for r, (mx, my) in zip(crs, lc):
        if not (ghOk(sigma, D, X, Y, b0, b1, R, capX(Dn, r[0]), mx) and
                ghOk(sigma, D, X, Y, b0, b1, R, capY(Dn, r[1]), my)):
            return False
    lebs = [lebVal(D, X, Y, Dn, r, mx, my) for r, (mx, my) in zip(crs, lc)]
    alts = [hAlts(D, X, Y, Dn, e, o) for e, o in zip(chs, hc)] + [vAlts(D, X, Y, Dn, e, o) for e, o in zip(cvs, vc)]
    for comb in cprod(alts):
        if not ckRF(sigma, sumRF(D, comb + lebs + [rf_const(-W, 1)]), b0, b1, R):
            return False
    return True


# ---------------------------------------------------------------- LemmaELeaf
def detP(P, Q): return padd(pmul(P[0], Q[1]), psmul(-1, pmul(Q[0], P[1])))
def xP(P, Q): return padd(pmul(P[1], Q[2]), psmul(-1, pmul(Q[1], P[2])))
def yP(P, Q): return padd(pmul(Q[0], P[2]), psmul(-1, pmul(P[0], Q[2])))


def sideL(Q, x0, x1, y0, y1, wx, wy):
    wall = psmul(-1, padd(Cp, Sp))
    return [(psmul(2, Np), [0], wall) if wx else ([Q], [0], [-x0]),
            ([-Q], [0], [x1]),
            ([0], psmul(2, Np), wall) if wy else ([0], [Q], [-y0]),
            ([0], [-Q], [y1])]


def loX(Q, x0, wx):
    return (padd(Cp, Sp), 0, 0, 0, 1, 2) if wx else rf_const(x0, Q)


def affRF(P, x, y):
    one = [1]
    return rf_add(one, rf_add(one, rf_mul((P[0], 0, 0, 0, 0, 1), x), rf_mul((P[1], 0, 0, 0, 0, 1), y)),
                  (P[2], 0, 0, 0, 0, 1))


def cornersOk(Q, x0, x1, y0, y1, U0, U1, R, wx, wy, neg, P):
    cs = [(loX(Q, x0, wx), loX(Q, y0, wy)), (loX(Q, x0, wx), rf_const(y1, Q)),
          (rf_const(x1, Q), loX(Q, y0, wy)), (rf_const(x1, Q), rf_const(y1, Q))]
    for x, y in cs:
        r = affRF(P, x, y)
        if not ckRF(True, rf_neg(r) if neg else r, U0, U1, R):
            return False
    return True


def formsSL(A, B, lo1, lo2, up1, up2):
    return [sl_sub(up1, A), sl_sub(up2, A), sl_sub(B, lo1), sl_sub(B, lo2),
            sl_sub(up1, lo1), sl_sub(up1, lo2), sl_sub(up2, lo1), sl_sub(up2, lo2)]


def hFormsSLs(Dn, e):
    return formsSL(sl_cst(e[0], Dn), sl_cst(e[2], Dn), hTA(Dn, e[1]), hTB(Dn, e[1]), hTC(Dn, e[1]), hTD(Dn, e[1]))


def vFormsSLs(Dn, e):
    return formsSL(sl_cst(e[1], Dn), sl_cst(e[3], Dn), vLXs(Dn, e[0]), vLYs(Dn, e[0]), vUXs(Dn, e[0]), vUYs(Dn, e[0]))


def lebSLs(Dn, r):
    return [capX(Dn, r[0]), sl_sub(capX(Dn, r[0]), sSL(1)), capY(Dn, r[1]), sl_sub(capY(Dn, r[1]), sSL(1))]


def widN(R, U0, U1): return nat_sub(R * R + 2 * U1 * R, U0 * U0)
def widD(R, U0): return R * R + U0 * U0
