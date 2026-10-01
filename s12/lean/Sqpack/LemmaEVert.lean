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
theorem hseg_core {D : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {e : SegE} (hx : e.1 < e.2.2.1) {U L : SL}
    (hUm : U ∈ hUps D e) (hLm : L ∈ hLos D e)
    (u1 : ∀ U' ∈ hUps D e, U.val u (vtx X Y δ u) ≤ U'.val u (vtx X Y δ u))
    (l1 : ∀ L' ∈ hLos D e, L'.val u (vtx X Y δ u) ≤ L.val u (vtx X Y δ u)) :
    (RF.mul (RF.const (e.2.2.2.2 * D : ℕ) (e.2.2.1 - e.1)) ((U.sub L).atV Δ X Y)).eval δ u ≤
      (hsegT (2 * Real.arctan u) D e).1 *
        max 0 (clampMin (hsegT (2 * Real.arctan u) D e).2.1 (hsegT (2 * Real.arctan u) D e).2.2
          (vtx X Y δ u)) := by
  have hD2 : 2 * D ≠ 0 := by omega
  have hdU : ∀ L ∈ hUps D e, L.d ≠ 0 := by
    intro L hL; simp only [hUps, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, hTC, hTD] <;> omega
  have hdL : ∀ L ∈ hLos D e, L.d ≠ 0 := by
    intro L hL; simp only [hLos, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, hTA, hTB] <;> omega
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
  have hval : (RF.mul (RF.const (e.2.2.2.2 * D : ℕ) (e.2.2.1 - e.1)) ((U.sub L).atV Δ X Y)).eval δ u =
      (e.2.2.2.2 : ℝ) / (B - A) * (U.val u v - L.val u v) := by
    have hlen : (e.2.2.1 - e.1 : ℕ) ≠ 0 := by omega
    rw [eval_mul h.ok (by simp [RF.const]; omega) (Nat.mul_ne_zero (hdU U hUm) (hdL L hLm)),
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
theorem vseg_core {D : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {e : SegE} (hx : e.2.1 < e.2.2.2.1) {U L : SL}
    (hUm : U ∈ vUps D e) (hLm : L ∈ vLos D e)
    (u1 : ∀ U' ∈ vUps D e, U.val u (vtx X Y δ u) ≤ U'.val u (vtx X Y δ u))
    (l1 : ∀ L' ∈ vLos D e, L'.val u (vtx X Y δ u) ≤ L.val u (vtx X Y δ u)) :
    (RF.mul (RF.const (e.2.2.2.2 * D : ℕ) (e.2.2.2.1 - e.2.1)) ((U.sub L).atV Δ X Y)).eval δ u ≤
      (vsegT (2 * Real.arctan u) D e).1 *
        max 0 (clampMin (vsegT (2 * Real.arctan u) D e).2.1 (vsegT (2 * Real.arctan u) D e).2.2
          (vtx X Y δ u)) := by
  have hD2 : 2 * D ≠ 0 := by omega
  have hdU : ∀ L ∈ vUps D e, L.d ≠ 0 := by
    intro L hL; simp only [vUps, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, vUXs, vUYs] <;> omega
  have hdL : ∀ L ∈ vLos D e, L.d ≠ 0 := by
    intro L hL; simp only [vLos, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, vLXs, vLYs] <;> omega
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
  have hval : (RF.mul (RF.const (e.2.2.2.2 * D : ℕ) (e.2.2.2.1 - e.2.1)) ((U.sub L).atV Δ X Y)).eval δ u =
      (e.2.2.2.2 : ℝ) / (B - A) * (U.val u v - L.val u v) := by
    have hlen : (e.2.2.2.1 - e.2.1 : ℕ) ≠ 0 := by omega
    rw [eval_mul h.ok (by simp [RF.const]; omega) (Nat.mul_ne_zero (hdU U hUm) (hdL L hLm)),
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

/-! ## 3.  A Lebesgue term -/

/-- `sin θ / h = 2u/((1+u²) h)` as a scaled line. -/
def sSL (h : ℕ) : SL := ⟨([0], [0], Sp), 0, 0, 1, h⟩

lemma val_sSL {h : ℕ} (hh : h ≠ 0) (u : ℝ) (c : ℝ × ℝ) :
    (sSL h).val u c = 2 * u / (1 + u ^ 2) / h := by
  have hN : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  simp only [SL.val, sden, sSL, aff, evalPL, eval_Sp, eval_cons, eval_nil]
  push_cast
  field_simp
  ring

/-- The test of a cap mode: `0`: `d ≤ 0`; `1`: none (parabola); `2`: `d ≥ s`. -/
def ghOk (σ : Bool) (Δ X Y : Poly) (b0 b1 R : ℕ) (cap : SL) (mode : ℕ) : Bool :=
  if mode = 0 then ckRF σ (((SL.cst 0 1).sub cap).atV Δ X Y) b0 b1 R
  else if mode = 1 then true
  else ckRF σ ((cap.sub (sSL 1)).atV Δ X Y) b0 b1 R

/-- The upper bound of `ĝ(d)` of a cap mode: `0`, `d² N²/(2 S C)`, `(d − s/2) N / C`. -/
def ghU (Δ X Y : Poly) (cap : SL) (mode : ℕ) : RF :=
  if mode = 0 then RF.const 0 1
  else if mode = 1 then RF.mul (RF.mul (cap.atV Δ X Y) (cap.atV Δ X Y)) ⟨BernZ.mul Np Np, 0, 1, 1, 0, 2⟩
  else RF.mul ((cap.sub (sSL 2)).atV Δ X Y) ⟨Np, 0, 1, 0, 0, 1⟩

lemma ghU_d (Δ X Y : Poly) (cap : SL) (hc : cap.d ≠ 0) (mode : ℕ) : (ghU Δ X Y cap mode).d ≠ 0 := by
  unfold ghU; split_ifs <;> simp [RF.const, RF.mul, SL.atV, SL.sub, sSL] <;> omega

lemma ghat_le_par {s co d : ℝ} (hs : 0 < s) (hc : 0 < co) : SqArea.ghat s co d ≤ d ^ 2 / (2 * s * co) := by
  unfold SqArea.ghat
  split_ifs with h1 h2
  · positivity
  · exact le_rfl
  · rw [div_le_div_iff₀ hc (by positivity)]
    nlinarith [sq_nonneg (d - s)]

lemma ghU_sound {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ} (h : VCtx Δ X Y σ b0 b1 R u δ)
    {cap : SL} (hcap : cap.d ≠ 0) {mode : ℕ} (hok : ghOk σ Δ X Y b0 b1 R cap mode = true) :
    SqArea.ghat (Real.sin (2 * Real.arctan u)) (Real.cos (2 * Real.arctan u))
        (cap.val u (vtx X Y δ u)) ≤ (ghU Δ X Y cap mode).eval δ u := by
  have hN : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have hC : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [h.hu0, h.hu1]
  have hu := h.hu0
  rw [(trig u).1, (trig u).2]
  have hs : (0 : ℝ) < 2 * u / (1 + u ^ 2) := by positivity
  have hc : (0 : ℝ) < (1 - u ^ 2) / (1 + u ^ 2) := by positivity
  set d := cap.val u (vtx X Y δ u)
  have hd : (cap.atV Δ X Y).eval δ u = d := eval_atV _ _ _ _ h.hΔ h.ok.hδ
  unfold ghOk at hok; unfold ghU
  split_ifs at hok ⊢ with h0 h1
  · have hd0 : d ≤ 0 := by
      have := ckRF_sound hok h (by simpa [SL.atV, SL.sub, SL.cst] using hcap)
      rw [eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ (by simp [SL.cst]) hcap h.hu0 h.hu1,
        val_cst] at this
      simp only [Int.cast_zero, Nat.cast_one, zero_div, zero_sub] at this
      have h' : 0 ≤ -d := this
      linarith
    rw [eval_const]
    simp only [SqArea.ghat, if_pos hd0, Int.cast_zero, Nat.cast_one, zero_div, le_refl]
  · refine le_trans (ghat_le_par hs hc) (le_of_eq ?_)
    rw [eval_mul h.ok (by simpa [RF.mul, SL.atV] using Nat.mul_ne_zero hcap hcap) (by norm_num),
      eval_mul h.ok (by simpa [SL.atV] using hcap) (by simpa [SL.atV] using hcap), hd]
    simp only [RF.eval, den, BernZ.eval_mul, eval_Np]
    push_cast
    field_simp
  · have hds : 2 * u / (1 + u ^ 2) ≤ d := by
      have := ckRF_sound hok h (by simpa [SL.atV, SL.sub, sSL] using hcap)
      rw [eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ hcap (by simp [sSL]) h.hu0 h.hu1,
        val_sSL (by norm_num)] at this
      simp only [Nat.cast_one, div_one] at this
      have h' : 0 ≤ d - 2 * u / (1 + u ^ 2) := this
      linarith
    rw [eval_mul h.ok (by simpa [SL.atV, SL.sub, sSL] using hcap) (by norm_num),
      eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ hcap (by simp [sSL]) h.hu0 h.hu1,
      val_sSL (by norm_num), show cap.val u (eval X u / δ, eval Y u / δ) = d from rfl]
    have key : SqArea.ghat (2 * u / (1 + u ^ 2)) ((1 - u ^ 2) / (1 + u ^ 2)) d =
        (d - 2 * u / (1 + u ^ 2) / 2) / ((1 - u ^ 2) / (1 + u ^ 2)) := by
      unfold SqArea.ghat
      rw [if_neg (by linarith)]
      split_ifs with h3
      · have : d = 2 * u / (1 + u ^ 2) := le_antisymm h3 hds
        rw [this]; field_simp; ring
      · ring
    rw [key]
    apply le_of_eq
    simp only [RF.eval, den, eval_Np]
    push_cast
    field_simp

/-! ### Pointwise bounds of `ĝ` -/

lemma ghat_le_parU {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ} (h : VCtx Δ X Y σ b0 b1 R u δ)
    {cap : SL} (hcap : cap.d ≠ 0) :
    SqArea.ghat (Real.sin (2 * Real.arctan u)) (Real.cos (2 * Real.arctan u))
        (cap.val u (vtx X Y δ u)) ≤ (ghU Δ X Y cap 1).eval δ u := by
  have ok : ghOk σ Δ X Y b0 b1 R cap 1 = true := by simp [ghOk]
  exact ghU_sound h hcap ok

lemma ghat_le_linU {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ} (h : VCtx Δ X Y σ b0 b1 R u δ)
    {cap : SL} (hcap : cap.d ≠ 0) (hds : 2 * u / (1 + u ^ 2) ≤ cap.val u (vtx X Y δ u)) :
    SqArea.ghat (Real.sin (2 * Real.arctan u)) (Real.cos (2 * Real.arctan u))
        (cap.val u (vtx X Y δ u)) ≤ (ghU Δ X Y cap 2).eval δ u := by
  have hN : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have hC : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [h.hu0, h.hu1]
  have hu := h.hu0
  rw [(trig u).1, (trig u).2]
  set d := cap.val u (vtx X Y δ u)
  simp only [ghU, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_false]
  rw [eval_mul h.ok (by simpa [SL.atV, SL.sub, sSL] using hcap) (by norm_num),
    eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ hcap (by simp [sSL]) h.hu0 h.hu1,
    val_sSL (by norm_num), show cap.val u (eval X u / δ, eval Y u / δ) = d from rfl]
  have key : SqArea.ghat (2 * u / (1 + u ^ 2)) ((1 - u ^ 2) / (1 + u ^ 2)) d =
      (d - 2 * u / (1 + u ^ 2) / 2) / ((1 - u ^ 2) / (1 + u ^ 2)) := by
    unfold SqArea.ghat
    rw [if_neg (by have : (0 : ℝ) < 2 * u / (1 + u ^ 2) := by positivity
                   linarith)]
    split_ifs with h3
    · have : d = 2 * u / (1 + u ^ 2) := le_antisymm h3 hds
      rw [this]; field_simp; ring
    · ring
  rw [key]
  apply le_of_eq
  simp only [RF.eval, den, eval_Np]
  push_cast
  field_simp

lemma ghat_zero_of {s co d : ℝ} (hd : d ≤ 0) : SqArea.ghat s co d = 0 := by
  simp [SqArea.ghat, hd]

/-! ### Cap bounds with alternatives -/

/-- A cap's bound: `0` (checked `d ≤ 0`), the parabola, the line (checked `d ≥ s`), or a split at
`d = 0` (`zp`) or at `d = s` (`pl`) whose two branches carry S-procedure terms with multipliers
`n/d ≥ 0`: whichever side of the split `u` is on, that branch bounds `ĝ`. -/
inductive CapM where
  | zero
  | par
  | lin
  | zp (n0 d0 n1 d1 : ℕ)
  | pl (n0 d0 n1 d1 : ℕ)

def capOk (σ : Bool) (Δ X Y : Poly) (b0 b1 R : ℕ) (cap : SL) : CapM → Bool
  | .zero => ghOk σ Δ X Y b0 b1 R cap 0
  | .par => true
  | .lin => ghOk σ Δ X Y b0 b1 R cap 2
  | .zp _ d0 _ d1 => d0 != 0 && d1 != 0
  | .pl _ d0 _ d1 => d0 != 0 && d1 != 0

def capAlts (Δ X Y : Poly) (cap : SL) : CapM → List RF
  | .zero => [ghU Δ X Y cap 0]
  | .par => [ghU Δ X Y cap 1]
  | .lin => [ghU Δ X Y cap 2]
  | .zp n0 d0 n1 d1 => [RF.neg (RF.mul (RF.const n0 d0) (cap.atV Δ X Y)),
      RF.add Δ (ghU Δ X Y cap 1) (RF.mul (RF.const n1 d1) (cap.atV Δ X Y))]
  | .pl n0 d0 n1 d1 => [RF.add Δ (ghU Δ X Y cap 1) (RF.mul (RF.const n0 d0) (((sSL 1).sub cap).atV Δ X Y)),
      RF.add Δ (ghU Δ X Y cap 2) (RF.mul (RF.const n1 d1) ((cap.sub (sSL 1)).atV Δ X Y))]

lemma capAlts_d (Δ X Y : Poly) {cap : SL} (hcap : cap.d ≠ 0) {m : CapM} (σ : Bool) (b0 b1 R : ℕ)
    (hok : capOk σ Δ X Y b0 b1 R cap m = true) : ∀ r ∈ capAlts Δ X Y cap m, r.d ≠ 0 := by
  have g0 := ghU_d Δ X Y cap hcap 0
  have g1 := ghU_d Δ X Y cap hcap 1
  have g2 := ghU_d Δ X Y cap hcap 2
  intro r hr
  cases m with
  | zero => simp [capAlts] at hr; subst hr; exact g0
  | par => simp [capAlts] at hr; subst hr; exact g1
  | lin => simp [capAlts] at hr; subst hr; exact g2
  | zp n0 d0 n1 d1 =>
    simp only [capOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    simp only [capAlts, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [RF.neg, RF.mul, RF.const, SL.atV, hok.1, hcap]
    · exact RF.add_d _ g1 (by simp [RF.mul, RF.const, SL.atV, hok.2, hcap])
  | pl n0 d0 n1 d1 =>
    simp only [capOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    simp only [capAlts, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact RF.add_d _ g1 (by simp [RF.mul, RF.const, SL.atV, SL.sub, sSL, hok.1, hcap])
    · exact RF.add_d _ g2 (by simp [RF.mul, RF.const, SL.atV, SL.sub, sSL, hok.2, hcap])

/-- **A cap**: some alternative bounds `ĝ(d)` from above at `u`. -/
theorem capAlts_sound {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {cap : SL} (hcap : cap.d ≠ 0) {m : CapM}
    (hok : capOk σ Δ X Y b0 b1 R cap m = true) :
    ∃ t ∈ capAlts Δ X Y cap m, SqArea.ghat (Real.sin (2 * Real.arctan u))
      (Real.cos (2 * Real.arctan u)) (cap.val u (vtx X Y δ u)) ≤ t.eval δ u := by
  set d := cap.val u (vtx X Y δ u)
  have hd : (cap.atV Δ X Y).eval δ u = d := eval_atV _ _ _ _ h.hΔ h.ok.hδ
  have hdc := capAlts_d Δ X Y hcap σ b0 b1 R hok
  have hpar := ghat_le_parU h hcap (Δ := Δ)
  cases m with
  | zero => exact ⟨_, List.mem_singleton_self _, ghU_sound h hcap hok⟩
  | par => exact ⟨_, List.mem_singleton_self _, hpar⟩
  | lin => exact ⟨_, List.mem_singleton_self _, ghU_sound h hcap hok⟩
  | zp n0 d0 n1 d1 =>
    simp only [capOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    have hl0 : (0 : ℝ) ≤ (n0 : ℝ) / d0 := by positivity
    have hl1 : (0 : ℝ) ≤ (n1 : ℝ) / d1 := by positivity
    rcases le_total d 0 with hd0 | hd0
    · refine ⟨RF.neg (RF.mul (RF.const n0 d0) (cap.atV Δ X Y)), by simp [capAlts], ?_⟩
      rw [ghat_zero_of hd0, eval_neg, eval_mul h.ok (by simp [RF.const, hok.1])
        (by simpa [SL.atV] using hcap), eval_const, hd]
      push_cast
      nlinarith
    · refine ⟨RF.add Δ (ghU Δ X Y cap 1) (RF.mul (RF.const n1 d1) (cap.atV Δ X Y)),
        by simp [capAlts], ?_⟩
      rw [eval_add h.ok h.hΔ (ghU_d Δ X Y cap hcap 1) (by simp [RF.mul, RF.const, SL.atV, hok.2, hcap]),
        eval_mul h.ok (by simp [RF.const, hok.2]) (by simpa [SL.atV] using hcap), eval_const, hd]
      push_cast
      nlinarith
  | pl n0 d0 n1 d1 =>
    simp only [capOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    have hl0 : (0 : ℝ) ≤ (n0 : ℝ) / d0 := by positivity
    have hl1 : (0 : ℝ) ≤ (n1 : ℝ) / d1 := by positivity
    have hsd : (((sSL 1).sub cap).atV Δ X Y).eval δ u = 2 * u / (1 + u ^ 2) - d := by
      rw [eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ (by simp [sSL]) hcap h.hu0 h.hu1,
        val_sSL (by norm_num)]
      simp [d, vtx]
    have hds' : ((cap.sub (sSL 1)).atV Δ X Y).eval δ u = d - 2 * u / (1 + u ^ 2) := by
      rw [eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ hcap (by simp [sSL]) h.hu0 h.hu1,
        val_sSL (by norm_num)]
      simp [d, vtx]
    rcases le_total d (2 * u / (1 + u ^ 2)) with hds | hds
    · refine ⟨RF.add Δ (ghU Δ X Y cap 1) (RF.mul (RF.const n0 d0) (((sSL 1).sub cap).atV Δ X Y)),
        by simp [capAlts], ?_⟩
      rw [eval_add h.ok h.hΔ (ghU_d Δ X Y cap hcap 1)
          (by simp [RF.mul, RF.const, SL.atV, SL.sub, sSL, hok.1, hcap]),
        eval_mul h.ok (by simp [RF.const, hok.1]) (by simp [SL.atV, SL.sub, sSL, hcap]), eval_const,
        hsd]
      push_cast
      nlinarith
    · refine ⟨RF.add Δ (ghU Δ X Y cap 2) (RF.mul (RF.const n1 d1) ((cap.sub (sSL 1)).atV Δ X Y)),
        by simp [capAlts], ?_⟩
      have hlin := ghat_le_linU h hcap hds (Δ := Δ)
      rw [eval_add h.ok h.hΔ (ghU_d Δ X Y cap hcap 2)
          (by simp [RF.mul, RF.const, SL.atV, SL.sub, sSL, hok.2, hcap]),
        eval_mul h.ok (by simp [RF.const, hok.2]) (by simp [SL.atV, SL.sub, sSL, hcap]), eval_const,
        hds']
      push_cast
      nlinarith

/-- The certified value of a rectangle's term `ρ (1 − U_x − U_y)`. -/
def lebVal (Δ X Y : Poly) (D : ℕ) (r : RectE) (mx my : ℕ) : RF :=
  RF.mul (RF.const r.2.2.2.2 1) (RF.add Δ (RF.add Δ (RF.const 1 1)
    (RF.neg (ghU Δ X Y (capX D r.1) mx))) (RF.neg (ghU Δ X Y (capY D r.2.1) my)))

lemma lebVal_d (Δ X Y : Poly) {D : ℕ} (hD : 0 < D) (r : RectE) (mx my : ℕ) :
    (lebVal Δ X Y D r mx my).d ≠ 0 := by
  have a := ghU_d Δ X Y (capX D r.1) (by simp [capX]; omega) mx
  have b := ghU_d Δ X Y (capY D r.2.1) (by simp [capY]; omega) my
  simp only [lebVal]
  refine Nat.mul_ne_zero one_ne_zero (RF.add_d Δ (RF.add_d Δ (by simp [RF.const]) ?_) ?_)
  · simpa [RF.neg] using a
  · simpa [RF.neg] using b

/-- **A rectangle's term** is at least its certified value. -/
theorem leb_ge {D : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) (r : RectE) {mx my : ℕ}
    (hx : ghOk σ Δ X Y b0 b1 R (capX D r.1) mx = true)
    (hy : ghOk σ Δ X Y b0 b1 R (capY D r.2.1) my = true) :
    (lebVal Δ X Y D r mx my).eval δ u ≤
      (rectT (2 * Real.arctan u) D r).1 *
        (1 - SqArea.ghat (Real.sin (2 * Real.arctan u)) (Real.cos (2 * Real.arctan u))
          (aff (rectT (2 * Real.arctan u) D r).2.1 (vtx X Y δ u)) -
          SqArea.ghat (Real.sin (2 * Real.arctan u)) (Real.cos (2 * Real.arctan u))
          (aff (rectT (2 * Real.arctan u) D r).2.2 (vtx X Y δ u))) := by
  have hcx : (capX D r.1).d ≠ 0 := by simp [capX]; omega
  have hcy : (capY D r.2.1).d ≠ 0 := by simp [capY]; omega
  have gx := ghU_sound h hcx hx
  have gy := ghU_sound h hcy hy
  have ex : aff (rectT (2 * Real.arctan u) D r).2.1 (vtx X Y δ u) = (capX D r.1).val u (vtx X Y δ u) := by
    rw [val_capX hD h.hu0 h.hu1]; simp only [aff, rectT]; ring
  have ey : aff (rectT (2 * Real.arctan u) D r).2.2 (vtx X Y δ u) = (capY D r.2.1).val u (vtx X Y δ u) := by
    rw [val_capY hD h.hu0 h.hu1]; simp only [aff, rectT]; ring
  rw [ex, ey]
  have dx := ghU_d Δ X Y (capX D r.1) hcx mx
  have dy := ghU_d Δ X Y (capY D r.2.1) hcy my
  have d1 : (RF.const 1 1).d ≠ 0 := by simp [RF.const]
  have d2 : (RF.neg (ghU Δ X Y (capX D r.1) mx)).d ≠ 0 := by simpa [RF.neg] using dx
  have d3 : (RF.neg (ghU Δ X Y (capY D r.2.1) my)).d ≠ 0 := by simpa [RF.neg] using dy
  have d12 : (RF.add Δ (RF.const 1 1) (RF.neg (ghU Δ X Y (capX D r.1) mx))).d ≠ 0 :=
    RF.add_d Δ d1 d2
  have d123 : (RF.add Δ (RF.add Δ (RF.const 1 1) (RF.neg (ghU Δ X Y (capX D r.1) mx)))
      (RF.neg (ghU Δ X Y (capY D r.2.1) my))).d ≠ 0 := RF.add_d Δ d12 d3
  rw [lebVal, eval_mul h.ok (by simp [RF.const]) d123, eval_add h.ok h.hΔ d12 d3,
    eval_add h.ok h.hΔ d1 d2, eval_neg, eval_neg, eval_const, eval_const]
  simp only [rectT, Int.cast_one, Nat.cast_one, div_one, Int.cast_natCast]
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

/-! ## 4.  The whole bound at a vertex -/

def sumRF (Δ : Poly) : List RF → RF
  | [] => RF.const 0 1
  | r :: rs => RF.add Δ r (sumRF Δ rs)

lemma sumRF_d (Δ : Poly) : ∀ rs : List RF, (∀ r ∈ rs, r.d ≠ 0) → (sumRF Δ rs).d ≠ 0
  | [], _ => by simp [sumRF, RF.const]
  | r :: rs, h => by
    simp only [sumRF]
    exact RF.add_d Δ (h r List.mem_cons_self)
      (sumRF_d Δ rs fun x hx => h x (List.mem_cons_of_mem _ hx))

lemma eval_sumRF {Δ : Poly} {δ u : ℝ} (h : Ok δ u) (hΔ : eval Δ u = δ) :
    ∀ rs : List RF, (∀ r ∈ rs, r.d ≠ 0) → (sumRF Δ rs).eval δ u = (rs.map (·.eval δ u)).sum
  | [], _ => by simp [sumRF, eval_const]
  | r :: rs, hd => by
    have h1 := hd r List.mem_cons_self
    have h2 : ∀ x ∈ rs, x.d ≠ 0 := fun x hx => hd x (List.mem_cons_of_mem _ hx)
    simp only [sumRF, List.map_cons, List.sum_cons]
    rw [eval_add h hΔ h1 (sumRF_d Δ rs h2), eval_sumRF h hΔ rs h2]

/-! ### Alternatives -/

/-- The test of a segment's alternatives `Ua`, `La` (indices into the candidate upper and lower
ends): every candidate upper end is `≥` one in `Ua`, every lower end `≤` one in `La`. -/
def segOkA (σ : Bool) (Δ X Y : Poly) (b0 b1 R : ℕ) (ups los : List SL) (Ua La : List ℕ) : Bool :=
  !Ua.isEmpty && !La.isEmpty && Ua.all (· < ups.length) && La.all (· < los.length) &&
    ups.all (fun U => Ua.any fun a => ckRF σ ((U.sub (ups.getD a (SL.cst 0 1))).atV Δ X Y) b0 b1 R) &&
    los.all (fun L => La.any fun b => ckRF σ (((los.getD b (SL.cst 0 1)).sub L).atV Δ X Y) b0 b1 R)

/-- The values of a segment's alternatives `κ (up_a − lo_b)`. -/
def segAlts (Δ X Y : Poly) (w D len : ℕ) (ups los : List SL) (Ua La : List ℕ) : List RF :=
  Ua.flatMap fun a => La.map fun b => segVal Δ X Y w D len ups los a b

/-- Pointwise dominance: every candidate upper end is `≥` an alternative, every lower end `≤` one. -/
def DomU (u : ℝ) (v : ℝ × ℝ) (ups : List SL) (Ua : List ℕ) : Prop :=
  ∀ U ∈ ups, ∃ a ∈ Ua, (ups.getD a (SL.cst 0 1)).val u v ≤ U.val u v
def DomL (u : ℝ) (v : ℝ × ℝ) (los : List SL) (La : List ℕ) : Prop :=
  ∀ L ∈ los, ∃ b ∈ La, L.val u v ≤ (los.getD b (SL.cst 0 1)).val u v

lemma domU_of_check {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {ups : List SL} (hd : ∀ L ∈ ups, L.d ≠ 0) {Ua : List ℕ}
    (hlt : ∀ a ∈ Ua, a < ups.length)
    (hall : ups.all (fun U => Ua.any fun a =>
      ckRF σ ((U.sub (ups.getD a (SL.cst 0 1))).atV Δ X Y) b0 b1 R) = true) :
    DomU u (vtx X Y δ u) ups Ua := by
  intro U hU
  obtain ⟨b, hb, hc⟩ := List.any_eq_true.mp ((List.all_eq_true.mp hall) U hU)
  have hbm := getD_mem (SL.cst 0 1) (hlt b hb)
  have h0 := ckRF_sound hc h (Nat.mul_ne_zero (hd U hU) (hd _ hbm))
  rw [eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ (hd U hU) (hd _ hbm) h.hu0 h.hu1] at h0
  exact ⟨b, hb, by simp only [vtx] at h0 ⊢; linarith⟩

lemma domL_of_check {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {los : List SL} (hd : ∀ L ∈ los, L.d ≠ 0) {La : List ℕ}
    (hlt : ∀ a ∈ La, a < los.length)
    (hall : los.all (fun L => La.any fun b =>
      ckRF σ (((los.getD b (SL.cst 0 1)).sub L).atV Δ X Y) b0 b1 R) = true) :
    DomL u (vtx X Y δ u) los La := by
  intro L hL
  obtain ⟨b, hb, hc⟩ := List.any_eq_true.mp ((List.all_eq_true.mp hall) L hL)
  have hbm := getD_mem (SL.cst 0 1) (hlt b hb)
  have h0 := ckRF_sound hc h (Nat.mul_ne_zero (hd _ hbm) (hd L hL))
  rw [eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ (hd _ hbm) (hd L hL) h.hu0 h.hu1] at h0
  exact ⟨b, hb, by simp only [vtx] at h0 ⊢; linarith⟩

lemma exists_min_of_dom {u : ℝ} {v : ℝ × ℝ} {ups : List SL} {Ua : List ℕ} (hne : Ua ≠ [])
    (hdom : DomU u v ups Ua) :
    ∃ a ∈ Ua, ∀ U' ∈ ups, (ups.getD a (SL.cst 0 1)).val u v ≤ U'.val u v := by
  classical
  obtain ⟨a, ha, hmin⟩ := Ua.toFinset.exists_min_image (fun a => (ups.getD a (SL.cst 0 1)).val u v)
    (by obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil Ua hne; exact ⟨x, List.mem_toFinset.mpr hx⟩)
  refine ⟨a, List.mem_toFinset.mp ha, fun U' hU' => ?_⟩
  obtain ⟨b, hb, hle⟩ := hdom U' hU'
  exact le_trans (hmin b (List.mem_toFinset.mpr hb)) hle

lemma exists_max_of_dom {u : ℝ} {v : ℝ × ℝ} {los : List SL} {La : List ℕ} (hne : La ≠ [])
    (hdom : DomL u v los La) :
    ∃ b ∈ La, ∀ L' ∈ los, L'.val u v ≤ (los.getD b (SL.cst 0 1)).val u v := by
  classical
  obtain ⟨a, ha, hmax⟩ := La.toFinset.exists_max_image (fun a => (los.getD a (SL.cst 0 1)).val u v)
    (by obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil La hne; exact ⟨x, List.mem_toFinset.mpr hx⟩)
  refine ⟨a, List.mem_toFinset.mp ha, fun L' hL' => ?_⟩
  obtain ⟨b, hb, hle⟩ := hdom L' hL'
  exact le_trans hle (hmax b (List.mem_toFinset.mpr hb))

lemma hd_hUps {D : ℕ} (hD : 0 < D) (e : SegE) : ∀ L ∈ hUps D e, L.d ≠ 0 := by
  intro L hL; simp only [hUps, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl <;> simp [SL.cst, hTC, hTD] <;> omega
lemma hd_hLos {D : ℕ} (hD : 0 < D) (e : SegE) : ∀ L ∈ hLos D e, L.d ≠ 0 := by
  intro L hL; simp only [hLos, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl <;> simp [SL.cst, hTA, hTB] <;> omega
lemma hd_vUps {D : ℕ} (hD : 0 < D) (e : SegE) : ∀ L ∈ vUps D e, L.d ≠ 0 := by
  intro L hL; simp only [vUps, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl <;> simp [SL.cst, vUXs, vUYs] <;> omega
lemma hd_vLos {D : ℕ} (hD : 0 < D) (e : SegE) : ∀ L ∈ vLos D e, L.d ≠ 0 := by
  intro L hL; simp only [vLos, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl <;> simp [SL.cst, vLXs, vLYs] <;> omega

/-- **A horizontal segment's term** is at least one of its alternatives, under dominance. -/
theorem hseg_dom {D : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {e : SegE} (hx : e.1 < e.2.2.1) {Ua La : List ℕ}
    (hUa : Ua ≠ []) (hLa : La ≠ []) (hlu : ∀ a ∈ Ua, a < (hUps D e).length)
    (hll : ∀ b ∈ La, b < (hLos D e).length) (du : DomU u (vtx X Y δ u) (hUps D e) Ua)
    (dl : DomL u (vtx X Y δ u) (hLos D e) La) :
    ∃ t ∈ segAlts Δ X Y e.2.2.2.2 D (e.2.2.1 - e.1) (hUps D e) (hLos D e) Ua La,
      t.eval δ u ≤ (hsegT (2 * Real.arctan u) D e).1 *
        max 0 (clampMin (hsegT (2 * Real.arctan u) D e).2.1 (hsegT (2 * Real.arctan u) D e).2.2
          (vtx X Y δ u)) := by
  obtain ⟨a, ha, hamin⟩ := exists_min_of_dom hUa du
  obtain ⟨b, hb, hbmax⟩ := exists_max_of_dom hLa dl
  refine ⟨_, List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩, ?_⟩
  exact hseg_core hD h hx (getD_mem _ (hlu a ha)) (getD_mem _ (hll b hb)) hamin hbmax

theorem vseg_dom {D : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {e : SegE} (hx : e.2.1 < e.2.2.2.1) {Ua La : List ℕ}
    (hUa : Ua ≠ []) (hLa : La ≠ []) (hlu : ∀ a ∈ Ua, a < (vUps D e).length)
    (hll : ∀ b ∈ La, b < (vLos D e).length) (du : DomU u (vtx X Y δ u) (vUps D e) Ua)
    (dl : DomL u (vtx X Y δ u) (vLos D e) La) :
    ∃ t ∈ segAlts Δ X Y e.2.2.2.2 D (e.2.2.2.1 - e.2.1) (vUps D e) (vLos D e) Ua La,
      t.eval δ u ≤ (vsegT (2 * Real.arctan u) D e).1 *
        max 0 (clampMin (vsegT (2 * Real.arctan u) D e).2.1 (vsegT (2 * Real.arctan u) D e).2.2
          (vtx X Y δ u)) := by
  obtain ⟨a, ha, hamin⟩ := exists_min_of_dom hUa du
  obtain ⟨b, hb, hbmax⟩ := exists_max_of_dom hLa dl
  refine ⟨_, List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩, ?_⟩
  exact vseg_core hD h hx (getD_mem _ (hlu a ha)) (getD_mem _ (hll b hb)) hamin hbmax

/-! ### Combinations -/

/-- All ways of picking one element from each list. -/
def cprod {α : Type*} : List (List α) → List (List α)
  | [] => [[]]
  | l :: ls => l.flatMap fun a => (cprod ls).map (a :: ·)

/-- If each `x_s` is at least some alternative of list `s`, some combination sums to at most
`Σ x_s`. -/
lemma exists_comb_le {f : RF → ℝ} :
    ∀ (Ls : List (List RF)) (xs : List ℝ), Ls.length = xs.length →
      (∀ p ∈ Ls.zip xs, ∃ t ∈ p.1, f t ≤ p.2) →
      ∃ comb ∈ cprod Ls, (comb.map f).sum ≤ xs.sum
  | [], [], _, _ => ⟨[], by simp [cprod], by simp⟩
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | l :: Ls, x :: xs, h, hp => by
    obtain ⟨t, ht, htx⟩ := hp (l, x) List.mem_cons_self
    obtain ⟨comb, hc, hcs⟩ := exists_comb_le Ls xs (by simpa using h)
      fun p hq => hp p (List.mem_cons_of_mem _ hq)
    refine ⟨t :: comb, List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨comb, hc, rfl⟩⟩, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    linarith

lemma mem_cprod {α : Type*} {P : α → Prop} : ∀ (Ls : List (List α)), (∀ l ∈ Ls, ∀ a ∈ l, P a) →
    ∀ comb ∈ cprod Ls, ∀ a ∈ comb, P a
  | [], _, comb, hc, a, ha => by simp [cprod] at hc; subst hc; simp at ha
  | l :: Ls, h, comb, hc, a, ha => by
    obtain ⟨b, hb, hc'⟩ := List.mem_flatMap.mp hc
    obtain ⟨c, hc'', rfl⟩ := List.mem_map.mp hc'
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h l List.mem_cons_self a hb
    · exact mem_cprod Ls (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) c hc'' a ha

/-! ### The test at a vertex -/

/-- A segment's certificate at a vertex: dropped, the leaf's box-wide alternatives (dominance
certified once for the whole region), or alternatives checked at this vertex. -/
inductive SegC where
  | drop
  | box
  | alt (Ua La : List ℕ)

/-- A certificate at a vertex. -/
structure VCert where
  hc : List SegC
  vc : List SegC
  lc : List (CapM × CapM)

def segCAlts (Δ X Y : Poly) (w D len : ℕ) (ups los : List SL) (bx : List ℕ × List ℕ) : SegC → List RF
  | .drop => [RF.const 0 1]
  | .box => segAlts Δ X Y w D len ups los bx.1 bx.2
  | .alt Ua La => segAlts Δ X Y w D len ups los Ua La

def segCOk (σ : Bool) (Δ X Y : Poly) (b0 b1 R : ℕ) (ups los : List SL) (bx : List ℕ × List ℕ) :
    SegC → Bool
  | .drop => true
  | .box => !bx.1.isEmpty && !bx.2.isEmpty && bx.1.all (· < ups.length) && bx.2.all (· < los.length)
  | .alt Ua La => segOkA σ Δ X Y b0 b1 R ups los Ua La

def hAltsC (Δ X Y : Poly) (D : ℕ) (q : (SegE × (List ℕ × List ℕ)) × SegC) : List RF :=
  segCAlts Δ X Y q.1.1.2.2.2.2 D (q.1.1.2.2.1 - q.1.1.1) (hUps D q.1.1) (hLos D q.1.1) q.1.2 q.2
def vAltsC (Δ X Y : Poly) (D : ℕ) (q : (SegE × (List ℕ × List ℕ)) × SegC) : List RF :=
  segCAlts Δ X Y q.1.1.2.2.2.2 D (q.1.1.2.2.2.1 - q.1.1.2.1) (vUps D q.1.1) (vLos D q.1.1) q.1.2 q.2

/-- The alternatives of a rectangle's term `ρ (1 − U_x − U_y)`. -/
def lebAlts (Δ X Y : Poly) (D : ℕ) (r : RectE) (mx my : CapM) : List RF :=
  (capAlts Δ X Y (capX D r.1) mx).flatMap fun ux => (capAlts Δ X Y (capY D r.2.1) my).map fun uy =>
    RF.mul (RF.const r.2.2.2.2 1) (RF.add Δ (RF.add Δ (RF.const 1 1) (RF.neg ux)) (RF.neg uy))

/-- **The test at a vertex**: each claimed term's alternatives pass, and for every combination of
alternatives the sum minus `W` is `≥ 0`. -/
def vertOk (D W : ℕ) (σ : Bool) (Δ X Y : Poly) (b0 b1 R : ℕ) (chs cvs : List SegE)
    (crs : List RectE) (hbx vbx : List (List ℕ × List ℕ)) (c : VCert) : Bool :=
  hbx.length == chs.length && vbx.length == cvs.length &&
    c.hc.length == chs.length && c.vc.length == cvs.length && c.lc.length == crs.length &&
    ((chs.zip hbx).zip c.hc).all (fun q => segCOk σ Δ X Y b0 b1 R (hUps D q.1.1) (hLos D q.1.1) q.1.2 q.2) &&
    ((cvs.zip vbx).zip c.vc).all (fun q => segCOk σ Δ X Y b0 b1 R (vUps D q.1.1) (vLos D q.1.1) q.1.2 q.2) &&
    (crs.zip c.lc).all (fun p => capOk σ Δ X Y b0 b1 R (capX D p.1.1) p.2.1 &&
      capOk σ Δ X Y b0 b1 R (capY D p.1.2.1) p.2.2) &&
    (cprod (((chs.zip hbx).zip c.hc).map (hAltsC Δ X Y D) ++ ((cvs.zip vbx).zip c.vc).map (vAltsC Δ X Y D) ++
      (crs.zip c.lc).map (fun p => lebAlts Δ X Y D p.1 p.2.1 p.2.2))).all fun comb =>
      ckRF σ (sumRF Δ (comb ++ [RF.const (-(W : ℤ)) 1])) b0 b1 R

lemma segVal_d {D : ℕ} (hD : 0 < D) {Δ X Y : Poly} {w len : ℕ} (hlen : len ≠ 0) {ups los : List SL}
    (hu : ∀ L ∈ ups, L.d ≠ 0) (hl : ∀ L ∈ los, L.d ≠ 0) (iu il : ℕ) :
    (segVal Δ X Y w D len ups los iu il).d ≠ 0 := by
  have a : (ups.getD iu (SL.cst 0 1)).d ≠ 0 := by
    by_cases h : iu < ups.length
    · exact hu _ (getD_mem _ h)
    · rw [List.getD_eq_default _ _ (by omega)]; simp [SL.cst]
  have b : (los.getD il (SL.cst 0 1)).d ≠ 0 := by
    by_cases h : il < los.length
    · exact hl _ (getD_mem _ h)
    · rw [List.getD_eq_default _ _ (by omega)]; simp [SL.cst]
  simp only [segVal, RF.mul, RF.const, SL.atV, SL.sub]
  exact Nat.mul_ne_zero hlen (Nat.mul_ne_zero a b)

lemma segCAlts_d {D : ℕ} (hD : 0 < D) {Δ X Y : Poly} {w len : ℕ} (hlen : len ≠ 0)
    {ups los : List SL} (hu : ∀ L ∈ ups, L.d ≠ 0) (hl : ∀ L ∈ los, L.d ≠ 0) (bx : List ℕ × List ℕ)
    (c : SegC) : ∀ r ∈ segCAlts Δ X Y w D len ups los bx c, r.d ≠ 0 := by
  intro r hr
  cases c with
  | drop => simp [segCAlts] at hr; subst hr; simp [RF.const]
  | box =>
    obtain ⟨a, _, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hr
    exact segVal_d hD hlen hu hl a b
  | alt Ua La =>
    obtain ⟨a, _, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hr
    exact segVal_d hD hlen hu hl a b

lemma lebAlts_d (Δ X Y : Poly) {D : ℕ} (hD : 0 < D) (r : RectE) {σ : Bool} {b0 b1 R : ℕ}
    {mx my : CapM} (hx : capOk σ Δ X Y b0 b1 R (capX D r.1) mx = true)
    (hy : capOk σ Δ X Y b0 b1 R (capY D r.2.1) my = true) :
    ∀ t ∈ lebAlts Δ X Y D r mx my, t.d ≠ 0 := by
  intro t ht
  obtain ⟨ux, hux, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨uy, huy, rfl⟩ := List.mem_map.mp ht
  have a := capAlts_d Δ X Y (by simp [capX]; omega) σ b0 b1 R hx ux hux
  have b := capAlts_d Δ X Y (by simp [capY]; omega) σ b0 b1 R hy uy huy
  exact Nat.mul_ne_zero one_ne_zero (RF.add_d _ (RF.add_d _ (by simp [RF.const])
    (by simpa [RF.neg] using a)) (by simpa [RF.neg] using b))

/-- **A rectangle's term** is at least one of its alternatives. -/
theorem leb_alt {D : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) (r : RectE) {mx my : CapM}
    (hx : capOk σ Δ X Y b0 b1 R (capX D r.1) mx = true)
    (hy : capOk σ Δ X Y b0 b1 R (capY D r.2.1) my = true) :
    ∃ t ∈ lebAlts Δ X Y D r mx my, t.eval δ u ≤
      (rectT (2 * Real.arctan u) D r).1 *
        (1 - SqArea.ghat (Real.sin (2 * Real.arctan u)) (Real.cos (2 * Real.arctan u))
          (aff (rectT (2 * Real.arctan u) D r).2.1 (vtx X Y δ u)) -
          SqArea.ghat (Real.sin (2 * Real.arctan u)) (Real.cos (2 * Real.arctan u))
          (aff (rectT (2 * Real.arctan u) D r).2.2 (vtx X Y δ u))) := by
  have hcx : (capX D r.1).d ≠ 0 := by simp [capX]; omega
  have hcy : (capY D r.2.1).d ≠ 0 := by simp [capY]; omega
  obtain ⟨ux, hux, gx⟩ := capAlts_sound h hcx hx
  obtain ⟨uy, huy, gy⟩ := capAlts_sound h hcy hy
  have ex : aff (rectT (2 * Real.arctan u) D r).2.1 (vtx X Y δ u) = (capX D r.1).val u (vtx X Y δ u) := by
    rw [val_capX hD h.hu0 h.hu1]; simp only [aff, rectT]; ring
  have ey : aff (rectT (2 * Real.arctan u) D r).2.2 (vtx X Y δ u) = (capY D r.2.1).val u (vtx X Y δ u) := by
    rw [val_capY hD h.hu0 h.hu1]; simp only [aff, rectT]; ring
  refine ⟨_, List.mem_flatMap.mpr ⟨ux, hux, List.mem_map.mpr ⟨uy, huy, rfl⟩⟩, ?_⟩
  rw [ex, ey]
  have dx := capAlts_d Δ X Y hcx σ b0 b1 R hx ux hux
  have dy := capAlts_d Δ X Y hcy σ b0 b1 R hy uy huy
  have d1 : (RF.const 1 1).d ≠ 0 := by simp [RF.const]
  have d2 : (RF.neg ux).d ≠ 0 := by simpa [RF.neg] using dx
  have d3 : (RF.neg uy).d ≠ 0 := by simpa [RF.neg] using dy
  rw [eval_mul h.ok (by simp [RF.const]) (RF.add_d _ (RF.add_d _ d1 d2) d3),
    eval_add h.ok h.hΔ (RF.add_d _ d1 d2) d3, eval_add h.ok h.hΔ d1 d2, eval_neg, eval_neg,
    eval_const, eval_const]
  simp only [rectT, Int.cast_one, Nat.cast_one, div_one, Int.cast_natCast]
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

lemma exists_comb_zip {β : Type*} {f : RF → ℝ} :
    ∀ (ps : List β) (alts : β → List RF) (x : β → ℝ), (∀ p ∈ ps, ∃ t ∈ alts p, f t ≤ x p) →
      ∃ comb ∈ cprod (ps.map alts), (comb.map f).sum ≤ (ps.map x).sum
  | [], _, _, _ => ⟨[], by simp [cprod], by simp⟩
  | p :: ps, alts, x, h => by
    obtain ⟨t, ht, htx⟩ := h p List.mem_cons_self
    obtain ⟨comb, hc, hcs⟩ := exists_comb_zip ps alts x fun q hq => h q (List.mem_cons_of_mem _ hq)
    refine ⟨t :: comb, ?_, ?_⟩
    · simp only [List.map_cons, cprod]
      exact List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨comb, hc, rfl⟩⟩
    · simp only [List.map_cons, List.sum_cons]; linarith

lemma cprod_append {α : Type*} : ∀ (A B : List (List α)) {c1 c2 : List α}, c1 ∈ cprod A →
    c2 ∈ cprod B → c1 ++ c2 ∈ cprod (A ++ B)
  | [], B, c1, c2, h1, h2 => by simp [cprod] at h1; subst h1; simpa using h2
  | l :: A, B, c1, c2, h1, h2 => by
    obtain ⟨a, ha, h1'⟩ := List.mem_flatMap.mp h1
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h1'
    simp only [List.cons_append, cprod]
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨c ++ c2, cprod_append A B hc h2, rfl⟩⟩

lemma sum_map_zip_fst {α β : Type*} (l : List α) (m : List β) (g : α → ℝ) (h : m.length = l.length) :
    ((l.zip m).map fun q => g q.1).sum = (l.map g).sum := by
  rw [show (fun q : α × β => g q.1) = g ∘ Prod.fst from rfl, ← List.map_map,
    List.map_fst_zip (by omega)]

/-- The leaf's box-wide dominance, at the vertex. -/
def BoxDom (D : ℕ) (u : ℝ) (v : ℝ × ℝ) (chs cvs : List SegE) (hbx vbx : List (List ℕ × List ℕ)) :
    Prop :=
  (∀ q ∈ chs.zip hbx, DomU u v (hUps D q.1) q.2.1 ∧ DomL u v (hLos D q.1) q.2.2) ∧
    (∀ q ∈ cvs.zip vbx, DomU u v (vUps D q.1) q.2.1 ∧ DomL u v (vLos D q.1) q.2.2)

/-- **Soundness of the test at a vertex**: `W ≤ fE(v)`. -/
theorem vertOk_sound {D W : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {chs cvs : List SegE} {crs : List RectE}
    (hch : ∀ e ∈ chs, e.1 < e.2.2.1) (hcv : ∀ e ∈ cvs, e.2.1 < e.2.2.2.1)
    {hbx vbx : List (List ℕ × List ℕ)} (hbd : BoxDom D u (vtx X Y δ u) chs cvs hbx vbx) {c : VCert}
    (hok : vertOk D W σ Δ X Y b0 b1 R chs cvs crs hbx vbx c = true) :
    (W : ℝ) ≤ fE (Real.sin (2 * Real.arctan u)) (Real.cos (2 * Real.arctan u))
      (chs.map (hsegT (2 * Real.arctan u) D) ++ cvs.map (vsegT (2 * Real.arctan u) D))
      (crs.map (rectT (2 * Real.arctan u) D)) (vtx X Y δ u) := by
  simp only [vertOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨lh, lv⟩, l1⟩, l2⟩, l3⟩, hH⟩, hV⟩, hL⟩, htot⟩ := hok
  set θ := 2 * Real.arctan u
  set v := vtx X Y δ u
  -- each term is at least one of its alternatives
  have segC_ge : ∀ (ups los : List SL) (e : SegE) (bx : List ℕ × List ℕ) (sc : SegC) (w len : ℕ)
      (T : ℝ), 0 ≤ T →
      segCOk σ Δ X Y b0 b1 R ups los bx sc = true →
      (sc = .box → DomU u v ups bx.1 ∧ DomL u v los bx.2) →
      (∀ Ua La, Ua ≠ [] → La ≠ [] → (∀ a ∈ Ua, a < ups.length) → (∀ b ∈ La, b < los.length) →
        DomU u v ups Ua → DomL u v los La →
        ∃ t ∈ segAlts Δ X Y w D len ups los Ua La, t.eval δ u ≤ T) →
      (∀ L ∈ ups, L.d ≠ 0) → (∀ L ∈ los, L.d ≠ 0) →
      ∃ t ∈ segCAlts Δ X Y w D len ups los bx sc, t.eval δ u ≤ T := by
    intro ups los e bx sc w len T hT hok hbox hcore hdu hdl
    cases sc with
    | drop =>
      exact ⟨_, List.mem_singleton_self _, by rw [eval_const]; simpa using hT⟩
    | box =>
      simp only [segCOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hok
      obtain ⟨du, dl⟩ := hbox rfl
      exact hcore _ _ h1 h2 h3 h4 du dl
    | alt Ua La =>
      simp only [segCOk, segOkA, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
      exact hcore _ _ h1 h2 h3 h4 (domU_of_check h hdu h3 (List.all_eq_true.mpr h5))
        (domL_of_check h hdl h4 (List.all_eq_true.mpr h6))
  have hH' : ∀ q ∈ (chs.zip hbx).zip c.hc, ∃ t ∈ hAltsC Δ X Y D q, t.eval δ u ≤
      (hsegT θ D q.1.1).1 * max 0 (clampMin (hsegT θ D q.1.1).2.1 (hsegT θ D q.1.1).2.2 v) := by
    intro q hq
    have hq1 := (List.of_mem_zip hq).1
    have hx := hch q.1.1 (List.of_mem_zip hq1).1
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hAB : (q.1.1.1 : ℝ) / D < q.1.1.2.2.1 / D := div_lt_div_of_pos_right (by exact_mod_cast hx) hDr
    refine segC_ge _ _ q.1.1 q.1.2 q.2 _ _ _
      (mul_nonneg (by simp only [hsegT]; exact div_nonneg (Nat.cast_nonneg _) (by linarith))
        (le_max_left _ _)) (hH q hq) (fun _ => hbd.1 q.1 hq1)
      (fun Ua La h1 h2 h3 h4 du dl => hseg_dom hD h hx h1 h2 h3 h4 du dl)
      (hd_hUps hD q.1.1) (hd_hLos hD q.1.1)
  have hV' : ∀ q ∈ (cvs.zip vbx).zip c.vc, ∃ t ∈ vAltsC Δ X Y D q, t.eval δ u ≤
      (vsegT θ D q.1.1).1 * max 0 (clampMin (vsegT θ D q.1.1).2.1 (vsegT θ D q.1.1).2.2 v) := by
    intro q hq
    have hq1 := (List.of_mem_zip hq).1
    have hx := hcv q.1.1 (List.of_mem_zip hq1).1
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hAB : (q.1.1.2.1 : ℝ) / D < q.1.1.2.2.2.1 / D :=
      div_lt_div_of_pos_right (by exact_mod_cast hx) hDr
    refine segC_ge _ _ q.1.1 q.1.2 q.2 _ _ _
      (mul_nonneg (by simp only [vsegT]; exact div_nonneg (Nat.cast_nonneg _) (by linarith))
        (le_max_left _ _)) (hV q hq) (fun _ => hbd.2 q.1 hq1)
      (fun Ua La h1 h2 h3 h4 du dl => vseg_dom hD h hx h1 h2 h3 h4 du dl)
      (hd_vUps hD q.1.1) (hd_vLos hD q.1.1)
  have hL' : ∀ p ∈ crs.zip c.lc, ∃ t ∈ lebAlts Δ X Y D p.1 p.2.1 p.2.2, t.eval δ u ≤
      (rectT θ D p.1).1 * (1 - SqArea.ghat (Real.sin θ) (Real.cos θ) (aff (rectT θ D p.1).2.1 v) -
        SqArea.ghat (Real.sin θ) (Real.cos θ) (aff (rectT θ D p.1).2.2 v)) := by
    intro p hp
    have hk := hL p hp
    exact leb_alt hD h p.1 hk.1 hk.2
  obtain ⟨c1, hc1, hs1⟩ := exists_comb_zip (f := fun t => t.eval δ u) _ _ _ hH'
  obtain ⟨c2, hc2, hs2⟩ := exists_comb_zip (f := fun t => t.eval δ u) _ _ _ hV'
  obtain ⟨c3, hc3, hs3⟩ := exists_comb_zip (f := fun t => t.eval δ u) _ _ _ hL'
  have hcomb := cprod_append _ _ (cprod_append _ _ hc1 hc2) hc3
  -- constants
  have dAll : ∀ l ∈ ((chs.zip hbx).zip c.hc).map (hAltsC Δ X Y D) ++
      ((cvs.zip vbx).zip c.vc).map (vAltsC Δ X Y D) ++
      (crs.zip c.lc).map (fun p => lebAlts Δ X Y D p.1 p.2.1 p.2.2), ∀ r ∈ l, r.d ≠ 0 := by
    intro l hl r hr
    simp only [List.mem_append, List.mem_map] at hl
    rcases hl with (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨p, hp, rfl⟩
    · have hx := hch q.1.1 (List.of_mem_zip (List.of_mem_zip hq).1).1
      exact segCAlts_d hD (by omega) (hd_hUps hD q.1.1) (hd_hLos hD q.1.1) _ _ r hr
    · have hx := hcv q.1.1 (List.of_mem_zip (List.of_mem_zip hq).1).1
      exact segCAlts_d hD (by omega) (hd_vUps hD q.1.1) (hd_vLos hD q.1.1) _ _ r hr
    · have hk := hL p hp
      exact lebAlts_d Δ X Y hD p.1 hk.1 hk.2 r hr
  have hall : ∀ r ∈ c1 ++ c2 ++ c3 ++ [RF.const (-(W : ℤ)) 1], r.d ≠ 0 := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact mem_cprod (P := fun r => r.d ≠ 0) _ dAll _ hcomb r hr
    · simp at hr; subst hr; simp [RF.const]
  have h0 := ckRF_sound (htot _ hcomb) h (sumRF_d Δ _ hall)
  rw [eval_sumRF h.ok h.hΔ _ hall] at h0
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, eval_const] at h0
  have z1 := sum_map_zip_fst (chs.zip hbx) c.hc
    (fun q => (hsegT θ D q.1).1 * max 0 (clampMin (hsegT θ D q.1).2.1 (hsegT θ D q.1).2.2 v))
    (by simp [l1, lh])
  have z1' := sum_map_zip_fst chs hbx
    (fun e => (hsegT θ D e).1 * max 0 (clampMin (hsegT θ D e).2.1 (hsegT θ D e).2.2 v)) lh
  have z2 := sum_map_zip_fst (cvs.zip vbx) c.vc
    (fun q => (vsegT θ D q.1).1 * max 0 (clampMin (vsegT θ D q.1).2.1 (vsegT θ D q.1).2.2 v))
    (by simp [l2, lv])
  have z2' := sum_map_zip_fst cvs vbx
    (fun e => (vsegT θ D e).1 * max 0 (clampMin (vsegT θ D e).2.1 (vsegT θ D e).2.2 v)) lv
  have z3 := sum_map_zip_fst crs c.lc
    (fun r => (rectT θ D r).1 * (1 - SqArea.ghat (Real.sin θ) (Real.cos θ) (aff (rectT θ D r).2.1 v) -
      SqArea.ghat (Real.sin θ) (Real.cos θ) (aff (rectT θ D r).2.2 v))) l3
  rw [z1, z1'] at hs1
  rw [z2, z2'] at hs2
  rw [z3] at hs3
  simp only [fE, List.map_append, List.sum_append, List.map_map]
  simp only [Function.comp_def, List.map_map] at h0 hs1 hs2 hs3 ⊢
  push_cast at h0
  linarith


end LemmaEVert

end SquarePacking
