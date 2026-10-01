import Sqpack.LemmaEPoly

/-!
# Lemma E: the bound at a vertex, certified in integer arithmetic

At a vertex `v(u) = (X(u)/Δ(u), Y(u)/Δ(u))` of the arrangement, on a sub-bin of `u` where `Δ` has a
certified sign, the kernel bounds `fE(v)` from below and compares with `W`:

* a claimed segment contributes `κ · (up − lo)` for a chosen upper end `up ∈ {B, t_C, t_D}` and lower
  end `lo ∈ {A, t_A, t_B}` (vertical lines: `{B, upX, upY}`, `{A, lowX, lowY}`), after checking
  that `up` is the least of the three and `lo` the largest (`segOk`); or `0` (dropped);
* a Lebesgue rectangle contributes `ρ (1 − ĝ_x − ĝ_y)`, each `ĝ` bounded above by `0` (when `d ≤ 0`
  is checked), by the parabola `d²/(2 s c)` (always), or by `(d − s/2)/c` (when `d ≥ s` is checked);
* the sum minus `W` is checked `≥ 0`.

All quantities are `RF`s (`RatU.lean`); `vertOk_sound` turns an accepted certificate into
`W ≤ fE(v)`.
-/

namespace SquarePacking

namespace LemmaEVert

open BernZ RatU ChordE LemmaE LemmaEPoly ZMTreeM

/-! ## 1.  Sign of `Δ` on a sub-bin -/

/-- `Δ = u^m Δ'` and `σ Δ' > 0` on the closed sub-bin: then `Δ` has sign `σ` on `(b0/R, b1/R]`. -/
def signOk (σ : Bool) (Δ : Poly) (m b0 b1 R : ℕ) : Bool :=
  (Δ.take m).all (· == 0) &&
    checkPos (if σ then Δ.drop m else smul (-1) (Δ.drop m)) ((Δ.drop m).length - 1) b0 b1 R

lemma eval_take_drop (p : Poly) (m : ℕ) (h : (p.take m).all (· == 0) = true) (u : ℝ) :
    eval p u = u ^ m * eval (p.drop m) u := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    cases p with
    | nil => simp
    | cons a q =>
      simp only [List.take_succ_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      rw [eval_cons, h.1, List.drop_succ_cons, ih q h.2, pow_succ]
      push_cast; ring

lemma sign_of_signOk {σ : Bool} {Δ : Poly} {m b0 b1 R : ℕ} (h : signOk σ Δ m b0 b1 R = true)
    (hR : 0 < R) {u : ℝ} (hu0 : 0 < u) (hb0 : (b0 : ℝ) / R ≤ u) (hb1 : u ≤ (b1 : ℝ) / R) :
    if σ then 0 < eval Δ u else eval Δ u < 0 := by
  simp only [signOk, Bool.and_eq_true] at h
  obtain ⟨hz, hp⟩ := h
  have hpos := pos_of_checkPos hp hR hb0 hb1
  rw [eval_take_drop Δ m hz u]
  have hum : 0 < u ^ m := pow_pos hu0 m
  cases σ
  · simp only [Bool.false_eq_true, if_false, eval_smul] at hpos ⊢
    push_cast at hpos
    nlinarith
  · simp only [if_true] at hpos ⊢
    exact mul_pos hum hpos

/-! ## 2.  A segment's term -/

/-- The candidate ends of a horizontal segment `(X0, Y, X1, ·, w)` and of a vertical one. -/
def hUps (D : ℕ) (e : SegE) : List SL := [SL.cst e.2.2.1 D, hTC D e.2.1, hTD D e.2.1]
def hLos (D : ℕ) (e : SegE) : List SL := [SL.cst e.1 D, hTA D e.2.1, hTB D e.2.1]
def vUps (D : ℕ) (e : SegE) : List SL := [SL.cst e.2.2.2.1 D, vUXs D e.1, vUYs D e.1]
def vLos (D : ℕ) (e : SegE) : List SL := [SL.cst e.2.1 D, vLXs D e.1, vLYs D e.1]

/-- `RF ≥ 0` on the sub-bin, with a Bernstein degree of at least the numerator's. -/
def ckRF (σ : Bool) (r : RF) (b0 b1 R : ℕ) : Bool := checkRF σ r (r.num.length - 1) b0 b1 R

/-- The test of a segment's choice `(iu, il)`: the chosen upper end is the least, the lower the
largest. -/
def segOk (σ : Bool) (Δ X Y : Poly) (b0 b1 R : ℕ) (ups los : List SL) (iu il : ℕ) : Bool :=
  decide (iu < ups.length) && decide (il < los.length) &&
    ups.all (fun U => ckRF σ ((U.sub (ups.getD iu (SL.cst 0 1))).atV Δ X Y) b0 b1 R) &&
    los.all (fun L => ckRF σ (((los.getD il (SL.cst 0 1)).sub L).atV Δ X Y) b0 b1 R)

/-- The value of a segment's choice: `κ · (up − lo)` with `κ = w D / len`. -/
def segVal (Δ X Y : Poly) (w D len : ℕ) (ups los : List SL) (iu il : ℕ) : RF :=
  RF.mul (RF.const (w * D : ℕ) len) (((ups.getD iu (SL.cst 0 1)).sub (los.getD il (SL.cst 0 1))).atV Δ X Y)

/-! ### Soundness of a segment's term -/

/-- The data of a vertex on a sub-bin, as real numbers. -/
structure VCtx (Δ X Y : Poly) (σ : Bool) (b0 b1 R : ℕ) (u δ : ℝ) : Prop where
  hR : 0 < R
  hu0 : 0 < u
  hu1 : u < 1
  hb0 : (b0 : ℝ) / R ≤ u
  hb1 : u ≤ (b1 : ℝ) / R
  hΔ : eval Δ u = δ
  hσ : if σ then 0 < δ else δ < 0

lemma VCtx.ok {Δ X Y : Poly} {σ : Bool} {b0 b1 R : ℕ} {u δ : ℝ} (h : VCtx Δ X Y σ b0 b1 R u δ) :
    Ok δ u :=
  ⟨h.hu0, h.hu1, by have := h.hσ; split_ifs at this <;> [exact this.ne'; exact this.ne]⟩

/-- The vertex. -/
noncomputable def vtx (X Y : Poly) (δ u : ℝ) : ℝ × ℝ := (eval X u / δ, eval Y u / δ)

lemma ckRF_sound {σ : Bool} {r : RF} {b0 b1 R : ℕ} (hc : ckRF σ r b0 b1 R = true)
    {Δ X Y : Poly} {u δ : ℝ} (h : VCtx Δ X Y σ b0 b1 R u δ) (hd : r.d ≠ 0) : 0 ≤ r.eval δ u :=
  nonneg_of_checkRF hc h.hR h.ok h.hσ hd h.hb0 h.hb1

/-- If the chosen element is checked against all others (`U' − U ≥ 0` at the vertex), it is the
least of their values. -/
lemma le_of_all {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ} (h : VCtx Δ X Y σ b0 b1 R u δ)
    {Ls : List SL} (hd : ∀ L ∈ Ls, L.d ≠ 0) {U : SL} (hU : U.d ≠ 0)
    (hall : Ls.all (fun U' => ckRF σ ((U'.sub U).atV Δ X Y) b0 b1 R) = true) :
    ∀ U' ∈ Ls, U.val u (vtx X Y δ u) ≤ U'.val u (vtx X Y δ u) := by
  intro U' hU'
  have hc := (List.all_eq_true.mp hall) U' hU'
  have h0 := ckRF_sound hc h (Nat.mul_ne_zero (hd U' hU') hU)
  rw [eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ (hd U' hU') hU h.hu0 h.hu1] at h0
  simpa [vtx] using h0

lemma ge_of_all {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ} (h : VCtx Δ X Y σ b0 b1 R u δ)
    {Ls : List SL} (hd : ∀ L ∈ Ls, L.d ≠ 0) {U : SL} (hU : U.d ≠ 0)
    (hall : Ls.all (fun L => ckRF σ ((U.sub L).atV Δ X Y) b0 b1 R) = true) :
    ∀ L ∈ Ls, L.val u (vtx X Y δ u) ≤ U.val u (vtx X Y δ u) := by
  intro L hL
  have hc := (List.all_eq_true.mp hall) L hL
  have h0 := ckRF_sound hc h (Nat.mul_ne_zero hU (hd L hL))
  rw [eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ hU (hd L hL) h.hu0 h.hu1] at h0
  simpa [vtx] using h0

lemma getD_mem {α : Type*} {l : List α} {i : ℕ} (d : α) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

/-- **A horizontal segment's term** is at least its certified value. -/
theorem hseg_ge {D : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {e : SegE} (hx : e.1 < e.2.2.1) {iu il : ℕ}
    (hok : segOk σ Δ X Y b0 b1 R (hUps D e) (hLos D e) iu il = true) :
    (segVal Δ X Y e.2.2.2.2 D (e.2.2.1 - e.1) (hUps D e) (hLos D e) iu il).eval δ u ≤
      (hsegT (2 * Real.arctan u) D e).1 *
        max 0 (clampMin (hsegT (2 * Real.arctan u) D e).2.1 (hsegT (2 * Real.arctan u) D e).2.2
          (vtx X Y δ u)) := by
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hiu, hil⟩, hU⟩, hL⟩ := hok
  have hD2 : 2 * D ≠ 0 := by omega
  have hdU : ∀ L ∈ hUps D e, L.d ≠ 0 := by
    intro L hL; simp only [hUps, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, hTC, hTD] <;> omega
  have hdL : ∀ L ∈ hLos D e, L.d ≠ 0 := by
    intro L hL; simp only [hLos, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, hTA, hTB] <;> omega
  set U := (hUps D e).getD iu (SL.cst 0 1)
  set L := (hLos D e).getD il (SL.cst 0 1)
  have hUm : U ∈ hUps D e := getD_mem _ hiu
  have hLm : L ∈ hLos D e := getD_mem _ hil
  have u1 := le_of_all h hdU (hdU U hUm) hU
  have l1 := ge_of_all h hdL (hdL L hLm) hL
  set v := vtx X Y δ u
  set θ := 2 * Real.arctan u
  set η := (e.2.1 : ℝ) / D
  set A := (e.1 : ℝ) / D
  set B := (e.2.2.1 : ℝ) / D
  -- the values of the candidates
  have vB : (SL.cst e.2.2.1 D).val u v = B := by rw [val_cst]; push_cast; rfl
  have vA : (SL.cst e.1 D).val u v = A := by rw [val_cst]; push_cast; rfl
  have vC := val_hTC hD h.hu0 h.hu1 e.2.1 v
  have vDd := val_hTD hD h.hu0 h.hu1 e.2.1 v
  have vA' := val_hTA hD h.hu0 h.hu1 e.2.1 v
  have vB' := val_hTB hD h.hu0 h.hu1 e.2.1 v
  have hmin : U.val u v ≤ min B (min (aff (chC θ η) v) (aff (chD θ η) v)) := by
    refine le_min ?_ (le_min ?_ ?_)
    · have := u1 (SL.cst e.2.2.1 D) (by simp [hUps]); rwa [vB] at this
    · have := u1 (hTC D e.2.1) (by simp [hUps]); rwa [vC] at this
    · have := u1 (hTD D e.2.1) (by simp [hUps]); rwa [vDd] at this
  have hmax : max A (max (aff (chA θ η) v) (aff (chB θ η) v)) ≤ L.val u v := by
    refine max_le ?_ (max_le ?_ ?_)
    · have := l1 (SL.cst e.1 D) (by simp [hLos]); rwa [vA] at this
    · have := l1 (hTA D e.2.1) (by simp [hLos]); rwa [vA'] at this
    · have := l1 (hTB D e.2.1) (by simp [hLos]); rwa [vB'] at this
  have hcl := min_sub_max_formsOf A B (chA θ η) (chB θ η) (chC θ η) (chD θ η) v
  have hAB : A < B := by
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    exact div_lt_div_of_pos_right (by exact_mod_cast hx) hDr
  have hval : (segVal Δ X Y e.2.2.2.2 D (e.2.2.1 - e.1) (hUps D e) (hLos D e) iu il).eval δ u =
      (e.2.2.2.2 : ℝ) / (B - A) * (U.val u v - L.val u v) := by
    have hlen : (e.2.2.1 - e.1 : ℕ) ≠ 0 := by omega
    rw [segVal, eval_mul h.ok (by simp [RF.const]; omega) (Nat.mul_ne_zero (hdU U hUm) (hdL L hLm)),
      eval_const, eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ (hdU U hUm) (hdL L hLm) h.hu0 h.hu1]
    have hDr : (D : ℝ) ≠ 0 := by positivity
    have hsub : ((e.2.2.1 - e.1 : ℕ) : ℝ) = (e.2.2.1 : ℝ) - e.1 := Nat.cast_sub hx.le
    simp only [B, A, hsub]
    push_cast
    have : (e.2.2.1 : ℝ) - e.1 ≠ 0 := by
      have : (e.1 : ℝ) < e.2.2.1 := by exact_mod_cast hx
      linarith
    field_simp
    rfl
  rw [hval]
  simp only [hsegT]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Nat.cast_nonneg _) (by linarith))
  rw [← hcl]
  exact le_trans (by linarith) (le_max_right _ _)

/-- **A vertical segment's term** is at least its certified value. -/
theorem vseg_ge {D : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {e : SegE} (hx : e.2.1 < e.2.2.2.1) {iu il : ℕ}
    (hok : segOk σ Δ X Y b0 b1 R (vUps D e) (vLos D e) iu il = true) :
    (segVal Δ X Y e.2.2.2.2 D (e.2.2.2.1 - e.2.1) (vUps D e) (vLos D e) iu il).eval δ u ≤
      (vsegT (2 * Real.arctan u) D e).1 *
        max 0 (clampMin (vsegT (2 * Real.arctan u) D e).2.1 (vsegT (2 * Real.arctan u) D e).2.2
          (vtx X Y δ u)) := by
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hiu, hil⟩, hU⟩, hL⟩ := hok
  have hD2 : 2 * D ≠ 0 := by omega
  have hdU : ∀ L ∈ vUps D e, L.d ≠ 0 := by
    intro L hL; simp only [vUps, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, vUXs, vUYs] <;> omega
  have hdL : ∀ L ∈ vLos D e, L.d ≠ 0 := by
    intro L hL; simp only [vLos, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, vLXs, vLYs] <;> omega
  set U := (vUps D e).getD iu (SL.cst 0 1)
  set L := (vLos D e).getD il (SL.cst 0 1)
  have hUm : U ∈ vUps D e := getD_mem _ hiu
  have hLm : L ∈ vLos D e := getD_mem _ hil
  have u1 := le_of_all h hdU (hdU U hUm) hU
  have l1 := ge_of_all h hdL (hdL L hLm) hL
  set v := vtx X Y δ u
  set θ := 2 * Real.arctan u
  set ξ := (e.1 : ℝ) / D
  set A := (e.2.1 : ℝ) / D
  set B := (e.2.2.2.1 : ℝ) / D
  -- the values of the candidates
  have vB : (SL.cst e.2.2.2.1 D).val u v = B := by rw [val_cst]; push_cast; rfl
  have vA : (SL.cst e.2.1 D).val u v = A := by rw [val_cst]; push_cast; rfl
  have vC := val_vUX hD h.hu0 h.hu1 e.1 v
  have vDd := val_vUY hD h.hu0 h.hu1 e.1 v
  have vA' := val_vLX hD h.hu0 h.hu1 e.1 v
  have vB' := val_vLY hD h.hu0 h.hu1 e.1 v
  have hmin : U.val u v ≤ min B (min (aff (vUX θ ξ) v) (aff (vUY θ ξ) v)) := by
    refine le_min ?_ (le_min ?_ ?_)
    · have := u1 (SL.cst e.2.2.2.1 D) (by simp [vUps]); rwa [vB] at this
    · have := u1 (vUXs D e.1) (by simp [vUps]); rwa [vC] at this
    · have := u1 (vUYs D e.1) (by simp [vUps]); rwa [vDd] at this
  have hmax : max A (max (aff (vLX θ ξ) v) (aff (vLY θ ξ) v)) ≤ L.val u v := by
    refine max_le ?_ (max_le ?_ ?_)
    · have := l1 (SL.cst e.2.1 D) (by simp [vLos]); rwa [vA] at this
    · have := l1 (vLXs D e.1) (by simp [vLos]); rwa [vA'] at this
    · have := l1 (vLYs D e.1) (by simp [vLos]); rwa [vB'] at this
  have hcl := min_sub_max_formsOf A B (vLX θ ξ) (vLY θ ξ) (vUX θ ξ) (vUY θ ξ) v
  have hAB : A < B := by
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    exact div_lt_div_of_pos_right (by exact_mod_cast hx) hDr
  have hval : (segVal Δ X Y e.2.2.2.2 D (e.2.2.2.1 - e.2.1) (vUps D e) (vLos D e) iu il).eval δ u =
      (e.2.2.2.2 : ℝ) / (B - A) * (U.val u v - L.val u v) := by
    have hlen : (e.2.2.2.1 - e.2.1 : ℕ) ≠ 0 := by omega
    rw [segVal, eval_mul h.ok (by simp [RF.const]; omega) (Nat.mul_ne_zero (hdU U hUm) (hdL L hLm)),
      eval_const, eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ (hdU U hUm) (hdL L hLm) h.hu0 h.hu1]
    have hDr : (D : ℝ) ≠ 0 := by positivity
    have hsub : ((e.2.2.2.1 - e.2.1 : ℕ) : ℝ) = (e.2.2.2.1 : ℝ) - e.2.1 := Nat.cast_sub hx.le
    simp only [B, A, hsub]
    push_cast
    have : (e.2.2.2.1 : ℝ) - e.2.1 ≠ 0 := by
      have : (e.2.1 : ℝ) < e.2.2.2.1 := by exact_mod_cast hx
      linarith
    field_simp
    rfl
  rw [hval]
  simp only [vsegT]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Nat.cast_nonneg _) (by linarith))
  rw [← hcl]
  exact le_trans (by linarith) (le_max_right _ _)

end LemmaEVert

end SquarePacking
