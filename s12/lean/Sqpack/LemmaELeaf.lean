import Sqpack.LemmaEVert

/-!
# Lemma E on a pose box: the `EXACT` leaf

For a box of centres and an angle bin `u ∈ (U0/R, U1/R]`, the leaf names the claimed segments and
rectangles, a list of lines `Ls` (polynomial triples in `u`), and for every pair of lines of
`side ++ Ls` (`side`: the four sides of the region) a certificate on sub-bins of `u`: the pair is
parallel (`Δ ≡ 0`), or on each sub-bin `Δ` has a certified sign and the vertex `(X/Δ, Y/Δ)` is
outside the region (a side is negative there) or `fE ≥ W` there (`vertOk`).  Every form of the
claimed terms is a line of `Ls` or has a certified sign on the region (four corners).  Then every
admissible pose of the box captures mass `≥ W` (`CovMPo.of_exact`).

This file: the vertex of two lines (`cramer`), sub-bin and pair certificates, and their soundness.
-/

namespace SquarePacking

namespace LemmaELeaf

open BernZ RatU ChordE LemmaE LemmaEPoly LemmaEVert PolyMin ZMTreeM

/-! ## 1.  The vertex of two lines -/

/-- `Δ`, `X`, `Y` of two polynomial lines: the vertex is `(X/Δ, Y/Δ)`. -/
def detP (P Q : PL) : Poly := BernZ.add (BernZ.mul P.1 Q.2.1) (smul (-1) (BernZ.mul Q.1 P.2.1))
def xP (P Q : PL) : Poly := BernZ.add (BernZ.mul P.2.1 Q.2.2) (smul (-1) (BernZ.mul Q.2.1 P.2.2))
def yP (P Q : PL) : Poly := BernZ.add (BernZ.mul Q.1 P.2.2) (smul (-1) (BernZ.mul P.1 Q.2.2))

lemma eval_detP (P Q : PL) (u : ℝ) :
    eval (detP P Q) u = (evalPL P u).1 * (evalPL Q u).2.1 - (evalPL P u).2.1 * (evalPL Q u).1 := by
  simp only [detP, evalPL, BernZ.eval_add, BernZ.eval_mul, eval_smul]; push_cast; ring

/-- **Cramer**: two lines with `det ≠ 0`, both zero at `v`, meet at `(X/Δ, Y/Δ)`. -/
lemma cramer (P Q : PL) (u : ℝ) (v : ℝ × ℝ) (hdet : eval (detP P Q) u ≠ 0)
    (h1 : aff (evalPL P u) v = 0) (h2 : aff (evalPL Q u) v = 0) :
    v = vtx (xP P Q) (yP P Q) (eval (detP P Q) u) u := by
  simp only [aff, evalPL] at h1 h2
  ext
  · show v.1 = eval (xP P Q) u / eval (detP P Q) u
    rw [eq_div_iff hdet, eval_detP]
    simp only [xP, BernZ.eval_add, BernZ.eval_mul, eval_smul, evalPL]
    push_cast
    linear_combination (eval Q.2.1 u) * h1 - (eval P.2.1 u) * h2
  · show v.2 = eval (yP P Q) u / eval (detP P Q) u
    rw [eq_div_iff hdet, eval_detP]
    simp only [yP, BernZ.eval_add, BernZ.eval_mul, eval_smul, evalPL]
    push_cast
    linear_combination (eval P.1 u) * h2 - (eval Q.1 u) * h1

lemma detP_swap (P Q : PL) (u : ℝ) : eval (detP Q P) u = -eval (detP P Q) u := by
  simp only [eval_detP]; ring

/-! ## 2.  Certificates for a pair of lines on sub-bins -/

/-- What a sub-bin `[b0, b1]` shows about the vertex of a pair: it lies outside the region (side
`k` is negative there, with `u^m` divided out of the numerator), or the bound holds there. -/
inductive Kind where
  | out (k m : ℕ)
  | val (c : VCert)

/-- A sub-bin: its upper end, the sign of `Δ` and the power of `u` dividing `Δ`, and its kind. -/
structure SubBin where
  b1 : ℕ
  σ : Bool
  m : ℕ
  kind : Kind

/-- `σ ·` a polynomial. -/
def sgn (σ : Bool) (p : Poly) : Poly := if σ then p else smul (-1) p

/-- The test of one sub-bin of the pair `(P, Q)`. -/
def subOk (D W R : ℕ) (side : List PL) (chs cvs : List SegE) (crs : List RectE) (P Q : PL)
    (b0 : ℕ) (sb : SubBin) : Bool :=
  let Δ := detP P Q; let X := xP P Q; let Y := yP P Q
  Nat.blt b0 sb.b1 && signOk sb.σ Δ sb.m b0 sb.b1 R &&
    match sb.kind with
    | .out k m =>
      let S := side.getD k ([0], [0], [0])
      let nm := (SL.atV ⟨S, 0, 0, 0, 1⟩ Δ X Y).num
      decide (k < side.length) && (nm.take m).all (· == 0) &&
        checkPos (sgn (!sb.σ) (nm.drop m)) ((nm.drop m).length - 1) b0 sb.b1 R
    | .val c => vertOk D W sb.σ Δ X Y b0 sb.b1 R chs cvs crs c

/-- A pair's certificate: parallel, or sub-bins covering `[U0, U1]` in order. -/
inductive PairCert where
  | par
  | bins (sbs : List SubBin)

def binsOk (D W R : ℕ) (side : List PL) (chs cvs : List SegE) (crs : List RectE) (P Q : PL) :
    ℕ → ℕ → List SubBin → Bool
  | b0, U1, [] => b0 == U1
  | b0, U1, sb :: sbs =>
    subOk D W R side chs cvs crs P Q b0 sb && binsOk D W R side chs cvs crs P Q sb.b1 U1 sbs

def pairOk (D W R U0 U1 : ℕ) (side : List PL) (chs cvs : List SegE) (crs : List RectE) (P Q : PL) :
    PairCert → Bool
  | .par => (detP P Q).all (· == 0)
  | .bins sbs => binsOk D W R side chs cvs crs P Q U0 U1 sbs

/-- All pairs `i < j` of a list, the certificates of `L[i]` with the later lines in order. -/
def allPairsOk (D W R U0 U1 : ℕ) (side : List PL) (chs cvs : List SegE) (crs : List RectE) :
    List PL → List (List PairCert) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | P :: Ps, cs :: css =>
    cs.length == Ps.length && (Ps.zip cs).all (fun q => pairOk D W R U0 U1 side chs cvs crs P q.1 q.2) &&
      allPairsOk D W R U0 U1 side chs cvs crs Ps css

/-! ## 3.  Soundness of the pair certificates -/

/-- The common hypotheses on the claims. -/
structure Claims (D : ℕ) (chs cvs : List SegE) : Prop where
  hD : 0 < D
  hch : ∀ e ∈ chs, e.1 < e.2.2.1
  hcv : ∀ e ∈ cvs, e.2.1 < e.2.2.2.1

/-- The bound `fE` at `θ = 2 arctan u` for the claims. -/
noncomputable def fEu (D : ℕ) (chs cvs : List SegE) (crs : List RectE) (u : ℝ) (p : ℝ × ℝ) : ℝ :=
  fE (Real.sin (2 * Real.arctan u)) (Real.cos (2 * Real.arctan u))
    (chs.map (hsegT (2 * Real.arctan u) D) ++ cvs.map (vsegT (2 * Real.arctan u) D))
    (crs.map (rectT (2 * Real.arctan u) D)) p

lemma binsOk_find {D W R : ℕ} {side : List PL} {chs cvs : List SegE} {crs : List RectE} {P Q : PL}
    {u : ℝ} (hR : 0 < R) :
    ∀ (sbs : List SubBin) (b0 U1 : ℕ), binsOk D W R side chs cvs crs P Q b0 U1 sbs = true →
      (b0 : ℝ) / R < u → u ≤ (U1 : ℝ) / R →
      ∃ b0' : ℕ, ∃ sb : SubBin, subOk D W R side chs cvs crs P Q b0' sb = true ∧
        (b0' : ℝ) / R ≤ u ∧ u ≤ (sb.b1 : ℝ) / R
  | [], b0, U1, h, h0, h1 => by
    simp only [binsOk, beq_iff_eq] at h
    subst h; linarith
  | sb :: sbs, b0, U1, h, h0, h1 => by
    simp only [binsOk, Bool.and_eq_true] at h
    by_cases hu : u ≤ (sb.b1 : ℝ) / R
    · exact ⟨b0, sb, h.1, h0.le, hu⟩
    · exact binsOk_find hR sbs sb.b1 U1 h.2 (not_le.mp hu) h1

/-- **One pair**: if two lines of a certified pair meet at a point of the region, the bound holds
there. -/
theorem pair_sound {D W R U0 U1 : ℕ} {side : List PL} {chs cvs : List SegE} {crs : List RectE}
    (hcl : Claims D chs cvs) (hR : 0 < R) {P Q : PL} {cert : PairCert}
    (hok : pairOk D W R U0 U1 side chs cvs crs P Q cert = true) {u : ℝ} (hu0 : (U0 : ℝ) / R < u)
    (hu1 : u ≤ (U1 : ℝ) / R) (hpos : 0 < u) (hlt : u < 1) {v : ℝ × ℝ}
    (hdet : eval (detP P Q) u ≠ 0) (h1 : aff (evalPL P u) v = 0) (h2 : aff (evalPL Q u) v = 0)
    (hv : v ∈ poly (side.map (evalPL · u))) :
    (W : ℝ) ≤ fEu D chs cvs crs u v := by
  cases cert with
  | par =>
    exfalso; apply hdet
    simp only [pairOk, List.all_eq_true, beq_iff_eq] at hok
    rw [eval_eq_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    have : (detP P Q).getD k 0 = 0 := by
      rw [List.getD_eq_getElem _ _ (Finset.mem_range.mp hk)]
      exact hok _ (List.getElem_mem _)
    rw [this]; simp
  | bins sbs =>
    simp only [pairOk] at hok
    obtain ⟨b0, sb, hsub, hb0, hb1⟩ := binsOk_find hR sbs U0 U1 hok hu0 hu1
    have hv' := cramer P Q u v hdet h1 h2
    simp only [subOk, Bool.and_eq_true, Nat.blt_eq] at hsub
    obtain ⟨⟨_, hsg⟩, hk⟩ := hsub
    have hσ := sign_of_signOk hsg hR hpos hb0 hb1
    have ctx : VCtx (detP P Q) (xP P Q) (yP P Q) sb.σ b0 sb.b1 R u (eval (detP P Q) u) :=
      ⟨hR, hpos, hlt, hb0, hb1, rfl, hσ⟩
    rcases hsbk : sb.kind with ⟨k, m⟩ | c
    · -- outside the region: a contradiction
      rw [hsbk] at hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨⟨hkl, hz⟩, hp⟩ := hk
      exfalso
      set S := side.getD k ([0], [0], [0])
      have hS : S ∈ side := getD_mem _ hkl
      have hge := hv (evalPL S u) (List.mem_map_of_mem hS)
      set nm := (SL.atV ⟨S, 0, 0, 0, 1⟩ (detP P Q) (xP P Q) (yP P Q)).num
      have hpos' := pos_of_checkPos hp hR hb0 hb1
      have hnm := eval_take_drop nm m hz u
      have hat : eval nm u / eval (detP P Q) u = aff (evalPL S u) v := by
        have e1 := eval_atV (⟨S, 0, 0, 0, 1⟩ : SL) (detP P Q) (xP P Q) (yP P Q) rfl ctx.ok.hδ
        have hden : den (SL.atV ⟨S, 0, 0, 0, 1⟩ (detP P Q) (xP P Q) (yP P Q)) (eval (detP P Q) u) u =
            eval (detP P Q) u := by simp [den, SL.atV]
        rw [RF.eval, hden] at e1
        refine e1.trans ?_
        rw [hv']
        simp [SL.val, sden, vtx]
      have hum : 0 < u ^ m := pow_pos hpos m
      have key : aff (evalPL S u) v < 0 := by
        rw [← hat, hnm]
        cases hσ' : sb.σ
        · rw [hσ'] at hσ hpos'
          simp only [Bool.false_eq_true, if_false] at hσ
          simp only [sgn, Bool.not_false, if_true] at hpos'
          exact div_neg_of_pos_of_neg (mul_pos hum hpos') hσ
        · rw [hσ'] at hσ hpos'
          simp only [if_true] at hσ
          simp only [sgn, Bool.not_true, Bool.false_eq_true, if_false, eval_smul] at hpos'
          push_cast at hpos'
          exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hum (by linarith)) hσ
      simp only [aff] at key hge
      linarith
    · rw [hsbk] at hk
      rw [hv']
      exact vertOk_sound hcl.hD ctx hcl.hch hcl.hcv hk

/-- **All pairs**: every pair `i < j` of the list has a passing certificate. -/
lemma allPairs_sound {D W R U0 U1 : ℕ} {side : List PL} {chs cvs : List SegE} {crs : List RectE} :
    ∀ (L : List PL) (css : List (List PairCert)), allPairsOk D W R U0 U1 side chs cvs crs L css = true →
      ∀ (i j : ℕ) (hi : i < j) (hj : j < L.length),
        ∃ c, pairOk D W R U0 U1 side chs cvs crs (L[i]'(by omega)) (L[j]) c = true
  | [], _, _, i, j, _, hj => absurd hj (by simp)
  | _ :: _, [], h, _, _, _, _ => by simp [allPairsOk] at h
  | P :: Ps, cs :: css, h, i, j, hij, hj => by
    simp only [allPairsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨hl, hall⟩, hrest⟩ := h
    cases i with
    | zero =>
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' : j' < Ps.length := by simpa using hj
      have hmem : (Ps[j'], cs[j']'(by omega)) ∈ Ps.zip cs := by
        rw [List.mem_iff_getElem]
        exact ⟨j', by simp [hl]; omega, by simp⟩
      exact ⟨_, hall _ hmem⟩
    | succ i =>
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      obtain ⟨c, hc⟩ := allPairs_sound Ps css hrest i j' (by omega) (by simpa using hj)
      exact ⟨c, by simpa using hc⟩

/-! ## 4.  The region and the pinning of forms -/

/-- The region's four sides: the lower `x` side is the box side `Q x ≥ x0` or the wall
`2N x ≥ C + S` (`x ≥ w/2`), the upper side `Q x ≤ x1`; likewise in `y`. -/
def sideL (Q x0 x1 y0 y1 : ℕ) (wx wy : Bool) : List PL :=
  [if wx then (smul 2 Np, [0], smul (-1) (BernZ.add Cp Sp)) else ([(Q : ℤ)], [0], [-(x0 : ℤ)]),
    ([-(Q : ℤ)], [0], [(x1 : ℤ)]),
    if wy then ([0], smul 2 Np, smul (-1) (BernZ.add Cp Sp)) else ([0], [(Q : ℤ)], [-(y0 : ℤ)]),
    ([0], [-(Q : ℤ)], [(y1 : ℤ)])]

/-- The lower ends of the region (`RF`s without `Δ`). -/
def loX (Q x0 : ℕ) (wx : Bool) : RF := if wx then ⟨BernZ.add Cp Sp, 0, 0, 0, 1, 2⟩ else RF.const x0 Q

lemma eval_loX {Q x0 : ℕ} (hQ : 0 < Q) (wx : Bool) (δ u : ℝ) :
    (loX Q x0 wx).eval δ u = if wx then (1 - u ^ 2 + 2 * u) / (2 * (1 + u ^ 2)) else (x0 : ℝ) / Q := by
  unfold loX; split_ifs
  · simp only [RF.eval, den, BernZ.eval_add, eval_Cp, eval_Sp]; push_cast; ring
  · rw [eval_const]; push_cast; rfl

/-- The region is the rectangle `[loX, x1/Q] × [loY, y1/Q]`. -/
lemma mem_region {Q x0 x1 y0 y1 : ℕ} (hQ : 0 < Q) {wx wy : Bool} {u : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ poly ((sideL Q x0 x1 y0 y1 wx wy).map (evalPL · u))) :
    (loX Q x0 wx).eval 1 u ≤ p.1 ∧ p.1 ≤ (x1 : ℝ) / Q ∧ (loX Q y0 wy).eval 1 u ≤ p.2 ∧
      p.2 ≤ (y1 : ℝ) / Q := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hN : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have h := fun C (hC : C ∈ sideL Q x0 x1 y0 y1 wx wy) => hp _ (List.mem_map_of_mem hC)
  simp only [sideL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [eval_loX hQ, eval_loX hQ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · split_ifs at h1 ⊢
    · simp only [evalPL, eval_smul, eval_Np, BernZ.eval_add, eval_Cp, eval_Sp, eval_cons, eval_nil]
        at h1
      push_cast at h1
      rw [div_le_iff₀ (by positivity)]; nlinarith
    · simp only [evalPL, eval_cons, eval_nil] at h1
      push_cast at h1
      rw [div_le_iff₀ hQr]; nlinarith
  · simp only [evalPL, eval_cons, eval_nil] at h2
    push_cast at h2
    rw [le_div_iff₀ hQr]; nlinarith
  · split_ifs at h3 ⊢
    · simp only [evalPL, eval_smul, eval_Np, BernZ.eval_add, eval_Cp, eval_Sp, eval_cons, eval_nil]
        at h3
      push_cast at h3
      rw [div_le_iff₀ (by positivity)]; nlinarith
    · simp only [evalPL, eval_cons, eval_nil] at h3
      push_cast at h3
      rw [div_le_iff₀ hQr]; nlinarith
  · simp only [evalPL, eval_cons, eval_nil] at h4
    push_cast at h4
    rw [le_div_iff₀ hQr]; nlinarith

lemma region_bounded {Q x0 x1 y0 y1 : ℕ} (hQ : 0 < Q) (wx wy : Bool) (u : ℝ) :
    Bornology.IsBounded (poly ((sideL Q x0 x1 y0 y1 wx wy).map (evalPL · u))) := by
  refine (Metric.isBounded_Icc ((loX Q x0 wx).eval 1 u, (loX Q y0 wy).eval 1 u)
    ((x1 : ℝ) / Q, (y1 : ℝ) / Q)).subset fun p hp => ?_
  obtain ⟨a, b, c, d⟩ := mem_region hQ hp
  exact ⟨⟨a, c⟩, ⟨b, d⟩⟩

/-- The value of a line at a point given by two `RF`s (no `Δ`: pass `Δ = [1]`). -/
def affRF (P : PL) (x y : RF) : RF :=
  RF.add [1] (RF.add [1] (RF.mul ⟨P.1, 0, 0, 0, 0, 1⟩ x) (RF.mul ⟨P.2.1, 0, 0, 0, 0, 1⟩ y))
    ⟨P.2.2, 0, 0, 0, 0, 1⟩

lemma affRF_d (P : PL) {x y : RF} (hx : x.d ≠ 0) (hy : y.d ≠ 0) : (affRF P x y).d ≠ 0 := by
  simp only [affRF, RF.add, RF.mul]; simp [hx, hy]

lemma eval_affRF (P : PL) {x y : RF} (hx : x.d ≠ 0) (hy : y.d ≠ 0) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) : (affRF P x y).eval 1 u = aff (evalPL P u) (x.eval 1 u, y.eval 1 u) := by
  have ok : Ok 1 u := ⟨hu0, hu1, one_ne_zero⟩
  have e1 : BernZ.eval [1] u = 1 := by simp
  unfold affRF
  rw [eval_add ok e1 (by simp [RF.add, RF.mul, hx, hy]) (by simp),
    eval_add ok e1 (by simp [RF.mul, hx]) (by simp [RF.mul, hy]), eval_mul ok (by simp) hx,
    eval_mul ok (by simp) hy]
  simp [RF.eval, den, aff, evalPL]

/-- A form is `≥ 0` (`neg = false`) or `≤ 0` (`neg = true`) at the four corners of the region. -/
def cornersOk (Q x0 x1 y0 y1 U0 U1 R : ℕ) (wx wy neg : Bool) (P : PL) : Bool :=
  [(loX Q x0 wx, loX Q y0 wy), (loX Q x0 wx, RF.const y1 Q), (RF.const x1 Q, loX Q y0 wy),
    (RF.const x1 Q, RF.const y1 Q)].all fun q =>
    ckRF true (if neg then RF.neg (affRF P q.1 q.2) else affRF P q.1 q.2) U0 U1 R

lemma affine_nonneg_rect {a b k xl xh yl yh x y : ℝ} (hx0 : xl ≤ x) (hx1 : x ≤ xh) (hy0 : yl ≤ y)
    (hy1 : y ≤ yh) (c00 : 0 ≤ a * xl + b * yl + k) (c01 : 0 ≤ a * xl + b * yh + k)
    (c10 : 0 ≤ a * xh + b * yl + k) (c11 : 0 ≤ a * xh + b * yh + k) : 0 ≤ a * x + b * y + k := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · nlinarith [mul_le_mul_of_nonneg_left hx0 ha, mul_le_mul_of_nonneg_left hy0 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hx0 ha, mul_le_mul_of_nonpos_left hy1 hb]
  · nlinarith [mul_le_mul_of_nonpos_left hx1 ha, mul_le_mul_of_nonneg_left hy0 hb]
  · nlinarith [mul_le_mul_of_nonpos_left hx1 ha, mul_le_mul_of_nonpos_left hy1 hb]

/-- **The corner test**: a form `≥ 0` (or `≤ 0`) at the four corners has that sign on the region. -/
lemma corners_sound {Q x0 x1 y0 y1 U0 U1 R : ℕ} (hQ : 0 < Q) (hR : 0 < R) {wx wy neg : Bool}
    {P : PL} (h : cornersOk Q x0 x1 y0 y1 U0 U1 R wx wy neg P = true) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) (hb0 : (U0 : ℝ) / R ≤ u) (hb1 : u ≤ (U1 : ℝ) / R) :
    ∀ p ∈ poly ((sideL Q x0 x1 y0 y1 wx wy).map (evalPL · u)),
      if neg then aff (evalPL P u) p ≤ 0 else 0 ≤ aff (evalPL P u) p := by
  intro p hp
  obtain ⟨hx0, hx1, hy0, hy1⟩ := mem_region hQ hp
  have ok : Ok 1 u := ⟨hu0, hu1, one_ne_zero⟩
  have dl : ∀ (z : ℕ) (w : Bool), (loX Q z w).d ≠ 0 := by
    intro z w; unfold loX; split_ifs <;> simp [RF.const] <;> omega
  have dc : ∀ z : ℕ, (RF.const z Q).d ≠ 0 := by intro z; simp [RF.const]; omega
  have hcx : ∀ z : ℕ, (RF.const z Q).eval 1 u = (z : ℝ) / Q := by
    intro z; rw [eval_const]; push_cast; rfl
  simp only [cornersOk, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨c1, c2, c3, c4⟩ := h
  have val : ∀ (x y : RF), x.d ≠ 0 → y.d ≠ 0 →
      ckRF true (if neg then RF.neg (affRF P x y) else affRF P x y) U0 U1 R = true →
      if neg then aff (evalPL P u) (x.eval 1 u, y.eval 1 u) ≤ 0
        else 0 ≤ aff (evalPL P u) (x.eval 1 u, y.eval 1 u) := by
    intro x y hx hy hc
    have hd : (if neg then RF.neg (affRF P x y) else affRF P x y).d ≠ 0 := by
      split_ifs <;> simp [RF.neg, affRF_d P hx hy]
    have h0 := nonneg_of_checkRF hc hR ok (by simp) hd hb0 hb1
    split_ifs at h0 ⊢
    · rw [eval_neg, eval_affRF P hx hy hu0 hu1] at h0; linarith
    · rwa [eval_affRF P hx hy hu0 hu1] at h0
  have v1 := val _ _ (dl x0 wx) (dl y0 wy) c1
  have v2 := val _ _ (dl x0 wx) (dc y1) c2
  have v3 := val _ _ (dc x1) (dl y0 wy) c3
  have v4 := val _ _ (dc x1) (dc y1) c4
  rw [hcx] at v2 v3 v4
  rw [hcx] at v4
  simp only [aff, evalPL] at v1 v2 v3 v4 ⊢
  split_ifs at v1 v2 v3 v4 ⊢
  · have := affine_nonneg_rect (a := -eval P.1 u) (b := -eval P.2.1 u) (k := -eval P.2.2 u)
      hx0 hx1 hy0 hy1 (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  · exact affine_nonneg_rect hx0 hx1 hy0 hy1 v1 v2 v3 v4

/-! ### Pinning -/

/-- A scaled line is pinned: its line is in `Ls`, or it is `≥ 0` / `≤ 0` at the corners. -/
def pinOk (Q x0 x1 y0 y1 U0 U1 R : ℕ) (wx wy : Bool) (Ls : List PL) (L : SL) : Bool :=
  Ls.contains L.P || cornersOk Q x0 x1 y0 y1 U0 U1 R wx wy false L.P ||
    cornersOk Q x0 x1 y0 y1 U0 U1 R wx wy true L.P

lemma pin_sound {Q x0 x1 y0 y1 U0 U1 R : ℕ} (hQ : 0 < Q) (hR : 0 < R) {wx wy : Bool}
    {Ls : List PL} {L : SL} (h : pinOk Q x0 x1 y0 y1 U0 U1 R wx wy Ls L = true) (hd : L.d ≠ 0)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hb0 : (U0 : ℝ) / R ≤ u) (hb1 : u ≤ (U1 : ℝ) / R)
    {F : ℝ × ℝ × ℝ} (hF : ∀ c, aff F c = L.val u c) :
    Pinned (poly ((sideL Q x0 x1 y0 y1 wx wy).map (evalPL · u))) (Ls.map (evalPL · u)) F := by
  simp only [pinOk, Bool.or_eq_true, List.contains_iff_mem] at h
  have hsd := sden_pos L hd hu0 hu1
  rcases h with (h | h) | h
  · exact Or.inl (posMul_of_SL L hd hu0 hu1 hF (List.mem_map_of_mem h))
  · right; left; intro p hp
    have := corners_sound hQ hR h hu0 hu1 hb0 hb1 p hp
    simp only [Bool.false_eq_true, if_false] at this
    rw [hF, SL.val]; exact div_nonneg this hsd.le
  · right; right; intro p hp
    have := corners_sound hQ hR h hu0 hu1 hb0 hb1 p hp
    simp only [if_true] at this
    rw [hF, SL.val]; exact div_nonpos_of_nonpos_of_nonneg this hsd.le

/-- The scaled lines of `formsOf`, in the same order. -/
def formsSL (A B lo1 lo2 up1 up2 : SL) : List SL :=
  [up1.sub A, up2.sub A, B.sub lo1, B.sub lo2, up1.sub lo1, up1.sub lo2, up2.sub lo1, up2.sub lo2]

lemma formsSL_match {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) {A B : ℝ} {lo1 lo2 up1 up2 : ℝ × ℝ × ℝ}
    {A' B' lo1' lo2' up1' up2' : SL} (dA : A'.d ≠ 0) (dB : B'.d ≠ 0) (d1 : lo1'.d ≠ 0)
    (d2 : lo2'.d ≠ 0) (d3 : up1'.d ≠ 0) (d4 : up2'.d ≠ 0)
    (eA : ∀ c, A'.val u c = A) (eB : ∀ c, B'.val u c = B) (e1 : ∀ c, aff lo1 c = lo1'.val u c)
    (e2 : ∀ c, aff lo2 c = lo2'.val u c) (e3 : ∀ c, aff up1 c = up1'.val u c)
    (e4 : ∀ c, aff up2 c = up2'.val u c) :
    ∀ F ∈ formsOf A B lo1 lo2 up1 up2, ∃ L ∈ formsSL A' B' lo1' lo2' up1' up2', L.d ≠ 0 ∧
      ∀ c, aff F c = L.val u c := by
  intro F hF
  simp only [formsOf, List.mem_cons, List.not_mem_nil, or_false] at hF
  simp only [formsSL, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left; exact ⟨Nat.mul_ne_zero d3 dA, fun c => by rw [aff_subF, aff_constF, val_sub _ _ d3 dA hu0 hu1, e3, eA]⟩
  · right; left; exact ⟨Nat.mul_ne_zero d4 dA, fun c => by rw [aff_subF, aff_constF, val_sub _ _ d4 dA hu0 hu1, e4, eA]⟩
  · right; right; left; exact ⟨Nat.mul_ne_zero dB d1, fun c => by rw [aff_subF, aff_constF, val_sub _ _ dB d1 hu0 hu1, e1, eB]⟩
  · right; right; right; left; exact ⟨Nat.mul_ne_zero dB d2, fun c => by rw [aff_subF, aff_constF, val_sub _ _ dB d2 hu0 hu1, e2, eB]⟩
  · right; right; right; right; left; exact ⟨Nat.mul_ne_zero d3 d1, fun c => by rw [aff_subF, val_sub _ _ d3 d1 hu0 hu1, e3, e1]⟩
  · right; right; right; right; right; left; exact ⟨Nat.mul_ne_zero d3 d2, fun c => by rw [aff_subF, val_sub _ _ d3 d2 hu0 hu1, e3, e2]⟩
  · right; right; right; right; right; right; left; exact ⟨Nat.mul_ne_zero d4 d1, fun c => by rw [aff_subF, val_sub _ _ d4 d1 hu0 hu1, e4, e1]⟩
  · right; right; right; right; right; right; right; exact ⟨Nat.mul_ne_zero d4 d2, fun c => by rw [aff_subF, val_sub _ _ d4 d2 hu0 hu1, e4, e2]⟩

end LemmaELeaf

end SquarePacking
