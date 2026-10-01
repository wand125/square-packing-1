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

/-- From the test, the least alternative upper end is below every candidate. -/
lemma exists_min_alt {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {ups : List SL} (hd : ∀ L ∈ ups, L.d ≠ 0) {Ua : List ℕ}
    (hne : Ua ≠ []) (hlt : ∀ a ∈ Ua, a < ups.length)
    (hall : ups.all (fun U => Ua.any fun a =>
      ckRF σ ((U.sub (ups.getD a (SL.cst 0 1))).atV Δ X Y) b0 b1 R) = true) :
    ∃ a ∈ Ua, ∀ U' ∈ ups, (ups.getD a (SL.cst 0 1)).val u (vtx X Y δ u) ≤ U'.val u (vtx X Y δ u) := by
  classical
  obtain ⟨a, ha, hmin⟩ := Ua.toFinset.exists_min_image
    (fun a => (ups.getD a (SL.cst 0 1)).val u (vtx X Y δ u))
    (by obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil Ua hne; exact ⟨x, List.mem_toFinset.mpr hx⟩)
  refine ⟨a, List.mem_toFinset.mp ha, fun U' hU' => ?_⟩
  obtain ⟨b, hb, hc⟩ := List.any_eq_true.mp ((List.all_eq_true.mp hall) U' hU')
  have hbm := getD_mem (SL.cst 0 1) (hlt b hb)
  have h0 := ckRF_sound hc h (Nat.mul_ne_zero (hd U' hU') (hd _ hbm))
  rw [eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ (hd U' hU') (hd _ hbm) h.hu0 h.hu1] at h0
  have := hmin b (List.mem_toFinset.mpr hb)
  simp only [vtx] at h0 this ⊢
  linarith

lemma exists_max_alt {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {los : List SL} (hd : ∀ L ∈ los, L.d ≠ 0) {La : List ℕ}
    (hne : La ≠ []) (hlt : ∀ a ∈ La, a < los.length)
    (hall : los.all (fun L => La.any fun b =>
      ckRF σ (((los.getD b (SL.cst 0 1)).sub L).atV Δ X Y) b0 b1 R) = true) :
    ∃ b ∈ La, ∀ L' ∈ los, L'.val u (vtx X Y δ u) ≤ (los.getD b (SL.cst 0 1)).val u (vtx X Y δ u) := by
  classical
  obtain ⟨a, ha, hmax⟩ := La.toFinset.exists_max_image
    (fun a => (los.getD a (SL.cst 0 1)).val u (vtx X Y δ u))
    (by obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil La hne; exact ⟨x, List.mem_toFinset.mpr hx⟩)
  refine ⟨a, List.mem_toFinset.mp ha, fun L' hL' => ?_⟩
  obtain ⟨b, hb, hc⟩ := List.any_eq_true.mp ((List.all_eq_true.mp hall) L' hL')
  have hbm := getD_mem (SL.cst 0 1) (hlt b hb)
  have h0 := ckRF_sound hc h (Nat.mul_ne_zero (hd _ hbm) (hd L' hL'))
  rw [eval_atV _ _ _ _ h.hΔ h.ok.hδ, val_sub _ _ (hd _ hbm) (hd L' hL') h.hu0 h.hu1] at h0
  have := hmax b (List.mem_toFinset.mpr hb)
  simp only [vtx] at h0 this ⊢
  linarith

lemma segOkA_parts {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {ups los : List SL} {Ua La : List ℕ}
    (hok : segOkA σ Δ X Y b0 b1 R ups los Ua La = true) :
    Ua ≠ [] ∧ La ≠ [] ∧ (∀ a ∈ Ua, a < ups.length) ∧ (∀ b ∈ La, b < los.length) ∧
      ups.all (fun U => Ua.any fun a =>
        ckRF σ ((U.sub (ups.getD a (SL.cst 0 1))).atV Δ X Y) b0 b1 R) = true ∧
      los.all (fun L => La.any fun b =>
        ckRF σ (((los.getD b (SL.cst 0 1)).sub L).atV Δ X Y) b0 b1 R) = true := by
  simp only [segOkA, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok
  exact ⟨h1, h2, h3, h4, List.all_eq_true.mpr h5, List.all_eq_true.mpr h6⟩

/-- **A horizontal segment's term** is at least one of its certified alternatives. -/
theorem hseg_alt {D : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {e : SegE} (hx : e.1 < e.2.2.1) {Ua La : List ℕ}
    (hok : segOkA σ Δ X Y b0 b1 R (hUps D e) (hLos D e) Ua La = true) :
    ∃ t ∈ segAlts Δ X Y e.2.2.2.2 D (e.2.2.1 - e.1) (hUps D e) (hLos D e) Ua La,
      t.eval δ u ≤ (hsegT (2 * Real.arctan u) D e).1 *
        max 0 (clampMin (hsegT (2 * Real.arctan u) D e).2.1 (hsegT (2 * Real.arctan u) D e).2.2
          (vtx X Y δ u)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := segOkA_parts hok
  have hD2 : 2 * D ≠ 0 := by omega
  have hdU : ∀ L ∈ hUps D e, L.d ≠ 0 := by
    intro L hL; simp only [hUps, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, hTC, hTD] <;> omega
  have hdL : ∀ L ∈ hLos D e, L.d ≠ 0 := by
    intro L hL; simp only [hLos, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, hTA, hTB] <;> omega
  obtain ⟨a, ha, hamin⟩ := exists_min_alt h hdU h1 h3 h5
  obtain ⟨b, hb, hbmax⟩ := exists_max_alt h hdL h2 h4 h6
  refine ⟨_, List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩, ?_⟩
  exact hseg_core hD h hx (getD_mem _ (h3 a ha)) (getD_mem _ (h4 b hb)) hamin hbmax

/-- **A vertical segment's term** is at least one of its certified alternatives. -/
theorem vseg_alt {D : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {e : SegE} (hx : e.2.1 < e.2.2.2.1) {Ua La : List ℕ}
    (hok : segOkA σ Δ X Y b0 b1 R (vUps D e) (vLos D e) Ua La = true) :
    ∃ t ∈ segAlts Δ X Y e.2.2.2.2 D (e.2.2.2.1 - e.2.1) (vUps D e) (vLos D e) Ua La,
      t.eval δ u ≤ (vsegT (2 * Real.arctan u) D e).1 *
        max 0 (clampMin (vsegT (2 * Real.arctan u) D e).2.1 (vsegT (2 * Real.arctan u) D e).2.2
          (vtx X Y δ u)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := segOkA_parts hok
  have hD2 : 2 * D ≠ 0 := by omega
  have hdU : ∀ L ∈ vUps D e, L.d ≠ 0 := by
    intro L hL; simp only [vUps, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, vUXs, vUYs] <;> omega
  have hdL : ∀ L ∈ vLos D e, L.d ≠ 0 := by
    intro L hL; simp only [vLos, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, vLXs, vLYs] <;> omega
  obtain ⟨a, ha, hamin⟩ := exists_min_alt h hdU h1 h3 h5
  obtain ⟨b, hb, hbmax⟩ := exists_max_alt h hdL h2 h4 h6
  refine ⟨_, List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩, ?_⟩
  exact vseg_core hD h hx (getD_mem _ (h3 a ha)) (getD_mem _ (h4 b hb)) hamin hbmax

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

/-- A certificate at a vertex: per claimed horizontal / vertical segment `none` (dropped) or the
alternatives `(Ua, La)`; per claimed rectangle the cap modes `(mx, my)`. -/
structure VCert where
  hc : List (Option (List ℕ × List ℕ))
  vc : List (Option (List ℕ × List ℕ))
  lc : List (ℕ × ℕ)

def hAlts (Δ X Y : Poly) (D : ℕ) (p : SegE × Option (List ℕ × List ℕ)) : List RF :=
  match p.2 with
  | none => [RF.const 0 1]
  | some q => segAlts Δ X Y p.1.2.2.2.2 D (p.1.2.2.1 - p.1.1) (hUps D p.1) (hLos D p.1) q.1 q.2
def vAlts (Δ X Y : Poly) (D : ℕ) (p : SegE × Option (List ℕ × List ℕ)) : List RF :=
  match p.2 with
  | none => [RF.const 0 1]
  | some q => segAlts Δ X Y p.1.2.2.2.2 D (p.1.2.2.2.1 - p.1.2.1) (vUps D p.1) (vLos D p.1) q.1 q.2
def hTOk (σ : Bool) (Δ X Y : Poly) (b0 b1 R D : ℕ) (p : SegE × Option (List ℕ × List ℕ)) : Bool :=
  match p.2 with
  | none => true
  | some q => segOkA σ Δ X Y b0 b1 R (hUps D p.1) (hLos D p.1) q.1 q.2
def vTOk (σ : Bool) (Δ X Y : Poly) (b0 b1 R D : ℕ) (p : SegE × Option (List ℕ × List ℕ)) : Bool :=
  match p.2 with
  | none => true
  | some q => segOkA σ Δ X Y b0 b1 R (vUps D p.1) (vLos D p.1) q.1 q.2

/-- **The test at a vertex**: the alternatives and cap modes pass, and for every combination of
alternatives the sum minus `W` is `≥ 0`. -/
def vertOk (D W : ℕ) (σ : Bool) (Δ X Y : Poly) (b0 b1 R : ℕ) (chs cvs : List SegE)
    (crs : List RectE) (c : VCert) : Bool :=
  c.hc.length == chs.length && c.vc.length == cvs.length && c.lc.length == crs.length &&
    (chs.zip c.hc).all (hTOk σ Δ X Y b0 b1 R D) && (cvs.zip c.vc).all (vTOk σ Δ X Y b0 b1 R D) &&
    (crs.zip c.lc).all (fun p => ghOk σ Δ X Y b0 b1 R (capX D p.1.1) p.2.1 &&
      ghOk σ Δ X Y b0 b1 R (capY D p.1.2.1) p.2.2) &&
    (cprod ((chs.zip c.hc).map (hAlts Δ X Y D) ++ (cvs.zip c.vc).map (vAlts Δ X Y D))).all fun comb =>
      ckRF σ (sumRF Δ (comb ++ (crs.zip c.lc).map (fun p => lebVal Δ X Y D p.1 p.2.1 p.2.2) ++
        [RF.const (-(W : ℤ)) 1])) b0 b1 R

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

lemma segAlts_d {D : ℕ} (hD : 0 < D) {Δ X Y : Poly} {w len : ℕ} (hlen : len ≠ 0)
    {ups los : List SL} (hu : ∀ L ∈ ups, L.d ≠ 0) (hl : ∀ L ∈ los, L.d ≠ 0) {Ua La : List ℕ} :
    ∀ r ∈ segAlts Δ X Y w D len ups los Ua La, r.d ≠ 0 := by
  intro r hr
  obtain ⟨a, _, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hr
  exact segVal_d hD hlen hu hl a b


lemma sum_zip_le {α β : Type*} (f : α → ℝ) (g : α × β → ℝ) :
    ∀ (l : List α) (cs : List β), cs.length = l.length → (∀ p ∈ l.zip cs, g p ≤ f p.1) →
      ((l.zip cs).map g).sum ≤ (l.map f).sum
  | [], _, _, _ => by simp
  | a :: l, [], h, _ => by simp at h
  | a :: l, b :: cs, h, hle => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    exact add_le_add (hle (a, b) List.mem_cons_self)
      (sum_zip_le f g l cs (by simpa using h) fun p hp => hle p (List.mem_cons_of_mem _ hp))

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

/-- **Soundness of the test at a vertex**: `W ≤ fE(v)`. -/
theorem vertOk_sound {D W : ℕ} (hD : 0 < D) {σ : Bool} {Δ X Y : Poly} {b0 b1 R : ℕ} {u δ : ℝ}
    (h : VCtx Δ X Y σ b0 b1 R u δ) {chs cvs : List SegE} {crs : List RectE}
    (hch : ∀ e ∈ chs, e.1 < e.2.2.1) (hcv : ∀ e ∈ cvs, e.2.1 < e.2.2.2.1) {c : VCert}
    (hok : vertOk D W σ Δ X Y b0 b1 R chs cvs crs c = true) :
    (W : ℝ) ≤ fE (Real.sin (2 * Real.arctan u)) (Real.cos (2 * Real.arctan u))
      (chs.map (hsegT (2 * Real.arctan u) D) ++ cvs.map (vsegT (2 * Real.arctan u) D))
      (crs.map (rectT (2 * Real.arctan u) D)) (vtx X Y δ u) := by
  simp only [vertOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨l1, l2⟩, l3⟩, hH⟩, hV⟩, hL⟩, htot⟩ := hok
  have hD2 : 2 * D ≠ 0 := by omega
  have hUh : ∀ e, ∀ L ∈ hUps D e, L.d ≠ 0 := fun e L hL => by
    simp only [hUps, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, hTC, hTD] <;> omega
  have hLh : ∀ e, ∀ L ∈ hLos D e, L.d ≠ 0 := fun e L hL => by
    simp only [hLos, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, hTA, hTB] <;> omega
  have hUv : ∀ e, ∀ L ∈ vUps D e, L.d ≠ 0 := fun e L hL => by
    simp only [vUps, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, vUXs, vUYs] <;> omega
  have hLv : ∀ e, ∀ L ∈ vLos D e, L.d ≠ 0 := fun e L hL => by
    simp only [vLos, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl <;> simp [SL.cst, vLXs, vLYs] <;> omega
  set θ := 2 * Real.arctan u
  set v := vtx X Y δ u
  set Ls := (chs.zip c.hc).map (hAlts Δ X Y D) ++ (cvs.zip c.vc).map (vAlts Δ X Y D) with hLs
  set xs := (chs.map fun e => (hsegT θ D e).1 * max 0 (clampMin (hsegT θ D e).2.1 (hsegT θ D e).2.2 v)) ++
    (cvs.map fun e => (vsegT θ D e).1 * max 0 (clampMin (vsegT θ D e).2.1 (vsegT θ D e).2.2 v)) with hxs
  -- every alternative has a non-zero constant
  have dAlt : ∀ l ∈ Ls, ∀ r ∈ l, r.d ≠ 0 := by
    intro l hl r hr
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      have hx := hch p.1 (List.of_mem_zip hp).1
      unfold hAlts at hr; split at hr
      · simp at hr; subst hr; simp [RF.const]
      · exact segAlts_d hD (by omega) (hUh p.1) (hLh p.1) r hr
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      have hx := hcv p.1 (List.of_mem_zip hp).1
      unfold vAlts at hr; split at hr
      · simp at hr; subst hr; simp [RF.const]
      · exact segAlts_d hD (by omega) (hUv p.1) (hLv p.1) r hr
  -- the combinations below the segment terms
  have hH' : ∀ q ∈ chs.zip c.hc, ∃ t ∈ hAlts Δ X Y D q, t.eval δ u ≤
      (hsegT θ D q.1).1 * max 0 (clampMin (hsegT θ D q.1).2.1 (hsegT θ D q.1).2.2 v) := by
    intro q hq
    have hx := hch q.1 (List.of_mem_zip hq).1
    have hk := hH q hq
    unfold hAlts; unfold hTOk at hk
    split
    · refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [eval_const]; simp only [Int.cast_zero, Nat.cast_one, zero_div]
      refine mul_nonneg ?_ (le_max_left _ _)
      simp only [hsegT]
      have hDr : (0 : ℝ) < D := by exact_mod_cast hD
      have : (q.1.1 : ℝ) / D < q.1.2.2.1 / D := div_lt_div_of_pos_right (by exact_mod_cast hx) hDr
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    · rename_i r hr
      rw [hr] at hk
      exact hseg_alt hD h hx hk
  have hV' : ∀ q ∈ cvs.zip c.vc, ∃ t ∈ vAlts Δ X Y D q, t.eval δ u ≤
      (vsegT θ D q.1).1 * max 0 (clampMin (vsegT θ D q.1).2.1 (vsegT θ D q.1).2.2 v) := by
    intro q hq
    have hx := hcv q.1 (List.of_mem_zip hq).1
    have hk := hV q hq
    unfold vAlts; unfold vTOk at hk
    split
    · refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [eval_const]; simp only [Int.cast_zero, Nat.cast_one, zero_div]
      refine mul_nonneg ?_ (le_max_left _ _)
      simp only [vsegT]
      have hDr : (0 : ℝ) < D := by exact_mod_cast hD
      have : (q.1.2.1 : ℝ) / D < q.1.2.2.2.1 / D :=
        div_lt_div_of_pos_right (by exact_mod_cast hx) hDr
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    · rename_i r hr
      rw [hr] at hk
      exact vseg_alt hD h hx hk
  obtain ⟨comb1, hc1, hs1⟩ := exists_comb_zip (f := fun t => t.eval δ u) (chs.zip c.hc)
    (hAlts Δ X Y D) _ hH'
  obtain ⟨comb2, hc2, hs2⟩ := exists_comb_zip (f := fun t => t.eval δ u) (cvs.zip c.vc)
    (vAlts Δ X Y D) _ hV'
  have hcomb : comb1 ++ comb2 ∈ cprod Ls := cprod_append _ _ hc1 hc2
  have hd12 : ∀ r ∈ comb1 ++ comb2, r.d ≠ 0 := fun r hr => mem_cprod (P := fun r => r.d ≠ 0) Ls
    dAlt _ hcomb r hr
  have dL : ∀ p ∈ crs.zip c.lc, (lebVal Δ X Y D p.1 p.2.1 p.2.2).d ≠ 0 :=
    fun p _ => lebVal_d Δ X Y hD p.1 _ _
  have hall : ∀ r ∈ comb1 ++ comb2 ++ (crs.zip c.lc).map (fun p => lebVal Δ X Y D p.1 p.2.1 p.2.2) ++
      [RF.const (-(W : ℤ)) 1], r.d ≠ 0 := by
    intro r hr
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ((hr | hr) | ⟨p, hp, rfl⟩) | rfl
    · exact hd12 r (List.mem_append_left _ hr)
    · exact hd12 r (List.mem_append_right _ hr)
    · exact dL p hp
    · simp [RF.const]
  have h0 := ckRF_sound (htot _ hcomb) h (sumRF_d Δ _ hall)
  rw [eval_sumRF h.ok h.hΔ _ hall] at h0
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, eval_const] at h0
  -- the Lebesgue terms
  have SL' : (((crs.zip c.lc).map ((fun r => r.eval δ u) ∘ fun p => lebVal Δ X Y D p.1 p.2.1 p.2.2))).sum ≤
      (crs.map (fun r => (rectT θ D r).1 * (1 - SqArea.ghat (Real.sin θ) (Real.cos θ)
        (aff (rectT θ D r).2.1 v) - SqArea.ghat (Real.sin θ) (Real.cos θ)
        (aff (rectT θ D r).2.2 v)))).sum := by
    refine sum_zip_le _ _ crs c.lc l3 fun p hp => ?_
    have hk := hL p hp
    exact leb_ge hD h p.1 hk.1 hk.2
  have z1 := sum_map_zip_fst chs c.hc
    (fun e => (hsegT θ D e).1 * max 0 (clampMin (hsegT θ D e).2.1 (hsegT θ D e).2.2 v)) l1
  have z2 := sum_map_zip_fst cvs c.vc
    (fun e => (vsegT θ D e).1 * max 0 (clampMin (vsegT θ D e).2.1 (vsegT θ D e).2.2 v)) l2
  rw [z1] at hs1
  rw [z2] at hs2
  simp only [fE, List.map_append, List.sum_append, List.map_map]
  simp only [Function.comp_def, List.map_map] at SL' h0 ⊢
  push_cast at h0
  linarith

end LemmaEVert

end SquarePacking
