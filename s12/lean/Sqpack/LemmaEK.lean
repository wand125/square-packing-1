import Sqpack.LemmaEDec
import Sqpack.KBern

/-!
# The vertex test in Kronecker form

On a sub-bin `[U0/R, U1/R]` the degree-`n` Bernstein coefficients of `p` (scaled by binomials) are
the coefficients of `γ(t) = Σₖ pₖ (U0 + U1 t)ᵏ (R + R t)ⁿ⁻ᵏ`.  With `X = 2ᴷ`, `A = U0 + U1 X` and
`B = R (1 + X)`, the number `γ(X) = Bⁿ p(A/B)` carries all of them at once: when `2 Σ|γᵢ| < X` they
are its balanced base-`X` digits, and they are all `≥ 0` iff `γ(X) ≥ 0` and no digit has its top bit
set.  `Bⁿ p(A/B)` is computed directly through the ring operations (`KH`): the numerators of the
rational functions of the vertex test are never expanded as lists.

`KR` carries the list form `r` alongside; the kernel evaluates it only where it is used (the
common-factor certificates).
-/

namespace SquarePacking

namespace LemmaEK

open BernZ RatU ChordE LemmaE LemmaEPoly LemmaEVert ZMTreeM LemmaELeaf KArith

/-- The vertex context: the evaluation point, the polynomials of the vertex and their images. -/
structure Ctx where
  A : ℤ
  B : ℕ
  K : ℕ
  M : ℕ
  Δ : Poly
  X : Poly
  Y : Poly
  hΔ : KH
  hX : KH
  hY : KH
  hC : KH
  hS : KH
  hN : KH

def mkCtx (Δ X Y : Poly) (b0 b1 R K : ℕ) : Ctx :=
  let A : ℤ := (b0 : ℤ) + (b1 : ℤ) * 2 ^ K
  let B : ℕ := R * (1 + 2 ^ K)
  ⟨A, B, K, max (b0 + b1) (2 * R), Δ, X, Y, hP A B Δ, hP A B X, hP A B Y, hP A B Cp, hP A B Sp,
    hP A B Np⟩

/-! ## Rational functions -/

structure KR where
  h : KH
  e : ℕ
  i : ℕ
  j : ℕ
  k : ℕ
  d : ℕ
  r : RF

def kRF (c : Ctx) (r : RF) : KR := ⟨hP c.A c.B r.num, r.e, r.i, r.j, r.k, r.d, r⟩

def kconst (n : ℤ) (d : ℕ) : KR := ⟨hconst n, 0, 0, 0, 0, d, RF.const n d⟩

def hmulOpt (p q : KH) (a : ℕ) : KH := if a = 0 then p else hmul p q

def kraise (c : Ctx) (r : KR) (a b cc g m : ℕ) : KR :=
  ⟨hmulOpt (hmulOpt (hmulOpt (hmulOpt (if m = 1 then r.h else hsmul m r.h) (hpow c.hΔ a) a)
      (hpow c.hC b) b) (hpow c.hS cc) cc) (hpow c.hN g) g,
    r.e + a, r.i + b, r.j + cc, r.k + g, r.d * m, raise c.Δ r.r a b cc g m⟩

def kadd (c : Ctx) (r s : KR) : KR :=
  let e := max r.e s.e
  let i := max r.i s.i
  let j := max r.j s.j
  let k := max r.k s.k
  let l := Nat.lcm r.d s.d
  ⟨hadd c.B (kraise c r (e - r.e) (i - r.i) (j - r.j) (k - r.k) (l / r.d)).h
      (kraise c s (e - s.e) (i - s.i) (j - s.j) (k - s.k) (l / s.d)).h,
    e, i, j, k, l, RF.add c.Δ r.r s.r⟩

def kmul (r s : KR) : KR :=
  ⟨hmul r.h s.h, r.e + s.e, r.i + s.i, r.j + s.j, r.k + s.k, r.d * s.d, RF.mul r.r s.r⟩

def kneg (r : KR) : KR := ⟨hsmul (-1) r.h, r.e, r.i, r.j, r.k, r.d, RF.neg r.r⟩

def ckK (c : Ctx) (σ : Bool) (r : KR) : Bool := hcheck c.K c.M (!(σ || r.e % 2 == 0)) r.h

/-! ## Scaled lines -/

structure KSL where
  P1 : KH
  P2 : KH
  P3 : KH
  i : ℕ
  j : ℕ
  k : ℕ
  d : ℕ
  s : SL

def kSL (c : Ctx) (L : SL) : KSL :=
  ⟨hP c.A c.B L.P.1, hP c.A c.B L.P.2.1, hP c.A c.B L.P.2.2, L.i, L.j, L.k, L.d, L⟩

def kden (c : Ctx) (L : KSL) : KH :=
  hmul (hpow c.hC L.i) (hmul (hpow c.hS L.j) (hmul (hpow c.hN L.k) (hconst L.d)))

def ksub (c : Ctx) (L M : KSL) : KSL :=
  let dM := kden c M
  let dL := kden c L
  ⟨hadd c.B (hmul dM L.P1) (hsmul (-1) (hmul dL M.P1)),
    hadd c.B (hmul dM L.P2) (hsmul (-1) (hmul dL M.P2)),
    hadd c.B (hmul dM L.P3) (hsmul (-1) (hmul dL M.P3)),
    L.i + M.i, L.j + M.j, L.k + M.k, L.d * M.d, L.s.sub M.s⟩

def katV (c : Ctx) (L : KSL) : KR :=
  ⟨hadd c.B (hadd c.B (hmul L.P1 c.hX) (hmul L.P2 c.hY)) (hmul L.P3 c.hΔ), 1, L.i, L.j, L.k, L.d,
    L.s.atV c.Δ c.X c.Y⟩

/-! ## The vertex test, mirrored -/

def kget (c : Ctx) (Ls : List SL) (i : ℕ) : KSL := kSL c (Ls.getD i (SL.cst 0 1))

def segValK (c : Ctx) (w D len : ℕ) (ups los : List SL) (iu il : ℕ) : KR :=
  kmul (kconst (w * D : ℕ) len) (katV c (ksub c (kget c ups iu) (kget c los il)))

def ghOkK (c : Ctx) (σ : Bool) (cap : SL) (mode : ℕ) : Bool :=
  if mode = 0 then ckK c σ (katV c (ksub c (kSL c (SL.cst 0 1)) (kSL c cap)))
  else if mode = 1 then true
  else ckK c σ (katV c (ksub c (kSL c cap) (kSL c (sSL 1))))

def ghUK (c : Ctx) (cap : SL) (mode : ℕ) : KR :=
  if mode = 0 then kconst 0 1
  else if mode = 1 then
    kmul (kmul (katV c (kSL c cap)) (katV c (kSL c cap))) (kRF c ⟨BernZ.mul Np Np, 0, 1, 1, 0, 2⟩)
  else kmul (katV c (ksub c (kSL c cap) (kSL c (sSL 2)))) (kRF c ⟨Np, 0, 1, 0, 0, 1⟩)

def segOkAK (c : Ctx) (σ : Bool) (ups los : List SL) (Ua La : List ℕ) : Bool :=
  !Ua.isEmpty && !La.isEmpty && Ua.all (· < ups.length) && La.all (· < los.length) &&
    ups.all (fun U => Ua.any fun a => ckK c σ (katV c (ksub c (kSL c U) (kget c ups a)))) &&
    los.all (fun L => La.any fun b => ckK c σ (katV c (ksub c (kget c los b) (kSL c L))))

def segAltsK (c : Ctx) (w D len : ℕ) (ups los : List SL) (Ua La : List ℕ) : List KR :=
  Ua.flatMap fun a => La.map fun b => segValK c w D len ups los a b

def segCAltsK (c : Ctx) (w D len : ℕ) (ups los : List SL) (bx : List ℕ × List ℕ) : SegC → List KR
  | .drop => [kconst 0 1]
  | .box => segAltsK c w D len ups los bx.1 bx.2
  | .alt Ua La => segAltsK c w D len ups los Ua La

def segCOkK (c : Ctx) (σ : Bool) (ups los : List SL) (bx : List ℕ × List ℕ) : SegC → Bool
  | .drop => true
  | .box => !bx.1.isEmpty && !bx.2.isEmpty && bx.1.all (· < ups.length) && bx.2.all (· < los.length)
  | .alt Ua La => segOkAK c σ ups los Ua La

def sprocK (c : Ctx) (sp : Split) (b : Bool) : KR :=
  if b then kneg (kmul (kconst sp.np sp.dp) (katV c (kSL c sp.q)))
  else kmul (kconst sp.nm sp.dm) (katV c (kSL c sp.q))

def capAOkK (c : Ctx) (σ : Bool) (splits : List Split) (cap : SL) : CapA → Bool
  | .zeroC => ghOkK c σ cap 0
  | .zeroT k => decide (k < splits.length) && splitAt splits k == cap
  | .par => true
  | .parT k _ => decide (k < splits.length)
  | .linC => ghOkK c σ cap 2
  | .linT k => decide (k < splits.length) && splitAt splits k == cap.sub (sSL 1)

def capAUK (c : Ctx) (cap : SL) : CapA → KR
  | .zeroC => ghUK c cap 0
  | .zeroT _ => ghUK c cap 0
  | .par => ghUK c cap 1
  | .parT _ _ => ghUK c cap 1
  | .linC => ghUK c cap 2
  | .linT _ => ghUK c cap 2

def lebRFK (c : Ctx) (D : ℕ) (r : RectM) (ax ay : CapA) : KR :=
  kmul (kconst r.1.2.2.2.2 1) (kadd c (kadd c (kconst 1 1)
    (kneg (capAUK c (capXm D r) ax))) (kneg (capAUK c (capYm D r) ay)))

def slAtPK (c : Ctx) (L : SL) (x y q : ℕ) : KR :=
  let K := kSL c L
  ⟨hadd c.B (hadd c.B (hsmul x K.P1) (hsmul y K.P2)) (hsmul q K.P3), 0, L.i, L.j, L.k, L.d * q,
    slAtP L x y q⟩

def mcRFK (c : Ctx) (A B bs α β : KR) : KR :=
  kmul (kRF c i2cRF) (kadd c (kadd c
    (kmul (kmul (kconst 2 1) (kRF c cRF)) (kadd c (kadd c (kmul A β) (kmul B α)) (kneg (kmul A B))))
    (kmul (kRF c sRF) (kadd c (kmul (kmul (kconst 2 1) bs) β) (kneg (kmul bs bs)))))
    (kneg (kmul (kRF c sRF) (kmul α α))))

def lebRFsK (c : Ctx) (D : ℕ) (r : RectM) (ax ay : CapA) : List KR :=
  let w := kconst r.1.2.2.2.2 1
  let gx := kneg (capAUK c (capXm D r) ax)
  let gy := kneg (capAUK c (capYm D r) ay)
  match r.2.2.2 with
  | .std => [lebRFK c D r ax ay]
  | .c3 xa ya ym q =>
    let aL := (capX D r.1.1).sub (sSL 1)
    let bL := capY D r.1.2.1
    let mc := mcRFK c (slAtPK c aL xa ya q) (slAtPK c bL xa ya q) (slAtPK c bL xa ym q)
      (katV c (kSL c ((capXm D r).sub (sSL 1)))) (katV c (kSL c (capYm D r)))
    [kmul w (kadd c (kadd c (kadd c (kconst 1 1) gx) gy) mc), kmul w (kadd c (kconst 1 1) gx)]
  | .xc xa ya ym q =>
    let aL := capX D r.1.1
    let bL := (capY D r.1.2.1).sub (cSL 1)
    let mc := mcRFK c (slAtPK c aL xa ya q) (slAtPK c bL xa ya q) (slAtPK c bL xa ym q)
      (katV c (kSL c (capXm D r))) (katV c (kSL c ((capYm D r).sub (cSL 1))))
    [kmul w (kadd c (kadd c (kconst 1 1) gy) mc), lebRFK c D r ax ay]

def sumK (c : Ctx) : List KR → KR
  | [] => kconst 0 1
  | r :: rs => kadd c r (sumK c rs)

def totOkK (c : Ctx) (σ : Bool) (b0 b1 R : ℕ) (splits : List Split) (pat : List Bool)
    (fcs : List FCert) (T : KR) : Bool :=
  ckK c σ T || fcs.any fun f => fcOk σ c.Δ c.X c.Y b0 b1 R splits pat f T.r

def hAltsPK (c : Ctx) (D : ℕ) (pat : List Bool) (q : (SegE × (List ℕ × List ℕ)) × List (SegC × Tag)) :
    List KR :=
  (q.2.filter fun x => tagOk pat x.2).flatMap fun x =>
    segCAltsK c q.1.1.2.2.2.2 D (q.1.1.2.2.1 - q.1.1.1) (hUps D q.1.1) (hLos D q.1.1) q.1.2 x.1
def vAltsPK (c : Ctx) (D : ℕ) (pat : List Bool) (q : (SegE × (List ℕ × List ℕ)) × List (SegC × Tag)) :
    List KR :=
  (q.2.filter fun x => tagOk pat x.2).flatMap fun x =>
    segCAltsK c q.1.1.2.2.2.2 D (q.1.1.2.2.2.1 - q.1.1.2.1) (vUps D q.1.1) (vLos D q.1.1) q.1.2 x.1
def lAltsPK (c : Ctx) (D : ℕ) (pat : List Bool) (p : RectM × (List CapA × List CapA)) : List KR :=
  (p.2.1.filter fun a => tagOk pat (capTag a)).flatMap fun ax =>
    (p.2.2.filter fun a => tagOk pat (capTag a)).flatMap fun ay => lebRFsK c D p.1 ax ay

def reordK (L : List (List KR)) : List (List KR) :=
  L.filter (fun l => l.length != 1) ++ L.filter (fun l => l.length == 1)

def vertOkK' (c : Ctx) (D W : ℕ) (σ : Bool) (b0 b1 R : ℕ) (chs cvs : List SegE)
    (crs : List RectM) (hbx vbx : List (List ℕ × List ℕ)) (v : VCert) : Bool :=
  hbx.length == chs.length && vbx.length == cvs.length &&
    v.hc.length == chs.length && v.vc.length == cvs.length && v.lc.length == crs.length &&
    v.splits.all (fun sp => sp.dm != 0 && sp.dp != 0) &&
    ((chs.zip hbx).zip v.hc).all (fun q => q.2.all fun x =>
      segCOkK c σ (hUps D q.1.1) (hLos D q.1.1) q.1.2 x.1) &&
    ((cvs.zip vbx).zip v.vc).all (fun q => q.2.all fun x =>
      segCOkK c σ (vUps D q.1.1) (vLos D q.1.1) q.1.2 x.1) &&
    (crs.zip v.lc).all (fun p => p.2.1.all (capAOkK c σ v.splits (capXm D p.1)) &&
      p.2.2.all (capAOkK c σ v.splits (capYm D p.1))) &&
    (pats v.splits.length).all fun pat =>
      v.hc.all (fun l => l.any fun x => tagOk pat x.2) &&
      v.vc.all (fun l => l.any fun x => tagOk pat x.2) &&
      v.lc.all (fun l => l.1.any (fun a => tagOk pat (capTag a)) && l.2.any (fun a => tagOk pat (capTag a))) &&
      (cprod (reordK (((chs.zip hbx).zip v.hc).map (hAltsPK c D pat) ++
          ((cvs.zip vbx).zip v.vc).map (vAltsPK c D pat) ++
          (crs.zip v.lc).map (lAltsPK c D pat)))).all fun comb =>
        totOkK c σ b0 b1 R v.splits pat v.fcs (sumK c (comb ++
          (v.splits.zip pat).map (fun x => sprocK c x.1 x.2) ++ [kconst (-(W : ℤ)) 1]))

/-- **The vertex test** at the evaluation point `2ᴷ`. -/
def vertOkK (D W : ℕ) (σ : Bool) (Δ X Y : Poly) (b0 b1 R K : ℕ) (chs cvs : List SegE)
    (crs : List RectM) (hbx vbx : List (List ℕ × List ℕ)) (v : VCert) : Bool :=
  vertOkK' (mkCtx Δ X Y b0 b1 R K) D W σ b0 b1 R chs cvs crs hbx vbx v

/-! ## The leaf test, with the vertex test in Kronecker form -/

def subOkK (K D W R : ℕ) (side : List PL) (chs cvs : List SegE) (crs : List RectM)
    (hbx vbx : List (List ℕ × List ℕ)) (P Q : PL)
    (b0 : ℕ) (sb : SubBin) : Bool :=
  let Δ := detP P Q; let X := xP P Q; let Y := yP P Q
  Nat.blt b0 sb.b1 && signOk sb.σ Δ sb.m b0 sb.b1 R &&
    match sb.kind with
    | .out k m =>
      let S := side.getD k ([0], [0], [0])
      let nm := (SL.atV ⟨S, 0, 0, 0, 1⟩ Δ X Y).num
      decide (k < side.length) && (nm.take m).all (· == 0) &&
        checkPos (sgn (!sb.σ) (nm.drop m)) ((nm.drop m).length - 1) b0 sb.b1 R
    | .val c => c.splits.all (fun sp => sp.q.d != 0) &&
      vertOkK D W sb.σ Δ X Y b0 sb.b1 R K chs cvs crs hbx vbx c

def binsOkK (K D W R : ℕ) (side : List PL) (chs cvs : List SegE) (crs : List RectM)
    (hbx vbx : List (List ℕ × List ℕ)) (P Q : PL) :
    ℕ → ℕ → List SubBin → Bool
  | b0, U1, [] => b0 == U1
  | b0, U1, sb :: sbs =>
    subOkK K D W R side chs cvs crs hbx vbx P Q b0 sb &&
      binsOkK K D W R side chs cvs crs hbx vbx P Q sb.b1 U1 sbs

def pairOkK (K D W R U0 U1 : ℕ) (side : List PL) (chs cvs : List SegE) (crs : List RectM)
    (hbx vbx : List (List ℕ × List ℕ)) (P Q : PL) :
    PairCert → Bool
  | .par => (detP P Q).all (· == 0)
  | .bins sbs => binsOkK K D W R side chs cvs crs hbx vbx P Q U0 U1 sbs

end LemmaEK

end SquarePacking
