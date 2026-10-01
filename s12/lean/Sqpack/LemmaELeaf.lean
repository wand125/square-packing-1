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

end LemmaELeaf

end SquarePacking
