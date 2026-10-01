import Sqpack.CovM
import Sqpack.SquareArea

/-!
# `CovMP`: mixed covers with Lebesgue rectangles (points + segments + area)

The mixed covers of `certificates/s21/FORMAT.md` may carry mass uniformly by area on polygons
(`MixedCover.poly`).  The covers of `certificates/k2m3/` use one: the Lebesgue square
`[9/5, 26/5]²` with mass = area (density 1).  This file adds **axis-parallel rectangles of constant
density** to `CovM`.

* A rectangle entry `(X0, Y0, X1, Y1, ρ)` is the closed rectangle `[X0/D, X1/D] × [Y0/D, Y1/D]`
  carrying density `ρ/W` (mass per unit area).  The mass a closed square `Q` captures from it is
  `ρ · |Q ∩ rect| / W` (`rectMass`).
* `CovMP` — `CovM` with the rectangle mass added; `CovMP.split{X,Y,U}`, `CovMP.of_covM`.
* **`lebOk`, `CovMP.of_leb`** — the `LEB` leaf (Lemma U of `search/QUADRANT_EXACT.md` §4.2): if every
  admissible square of the box lies inside a rectangle of density `≥ 1`, it captures mass `≥ 1` (its
  area is `1`, `SqArea.volume_sq`).  The test is in natural numbers: the half-width `w(θ)/2` of a
  square at angle `θ = 2 arctan u` is bounded on the bin by `widHat`.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace SquarePacking

namespace ZMTreeM

/-- A rectangle entry `(X0, Y0, X1, Y1, ρ)`. -/
abbrev RectE := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The closed rectangle of an entry, over `D`. -/
def rectSet (D : ℕ) (e : RectE) : Set (ℝ × ℝ) :=
  Set.Icc ((e.1 : ℝ) / D) ((e.2.2.1 : ℝ) / D) ×ˢ Set.Icc ((e.2.1 : ℝ) / D) ((e.2.2.2.1 : ℝ) / D)

/-- The rectangle mass a closed square captures (not yet divided by `W`). -/
noncomputable def rectMass (D : ℕ) (rects : List RectE) (Qs : Set (ℝ × ℝ)) : ℝ :=
  ∑ e ∈ rects.toFinset, (e.2.2.2.2 : ℝ) * (volume (Qs ∩ rectSet D e)).toReal

lemma rectMass_nonneg (D : ℕ) (rects : List RectE) (Qs : Set (ℝ × ℝ)) : 0 ≤ rectMass D rects Qs :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg

lemma ptMass_nonneg (D : ℕ) (pts : List (ℕ × ℕ × ℕ)) (Qs : Set (ℝ × ℝ)) : 0 ≤ ptMass D pts Qs :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- **What a box certifies, with rectangles**: every closed unit square inside `[0, Mq/D]²` with
centre in `[x0,x1]×[y0,y1]` (over `Q = D·S`) and angle `2 arctan u`, `u ∈ [u0/R, u1/R]`, captures
point, segment and rectangle mass `≥ W`. -/
def CovMP (D S Mq R W : ℕ) (pts : List (ℕ × ℕ × ℕ)) (segs : List SegE) (rects : List RectE)
    (x0 x1 y0 y1 u0 u1 : ℕ) : Prop :=
  ∀ (c : ℝ × ℝ) (u : ℝ),
    (x0 : ℝ) / (D * S) ≤ c.1 → c.1 ≤ (x1 : ℝ) / (D * S) →
    (y0 : ℝ) / (D * S) ≤ c.2 → c.2 ≤ (y1 : ℝ) / (D * S) →
    (u0 : ℝ) / R ≤ u → u ≤ (u1 : ℝ) / R →
    sq c (2 * Real.arctan u) 1 ⊆ box ((Mq : ℝ) / D) →
    (W : ℝ) ≤ ptMass D pts (sq c (2 * Real.arctan u) 1) + segMass D segs (sq c (2 * Real.arctan u) 1)
      + rectMass D rects (sq c (2 * Real.arctan u) 1)

variable {D S Mq R W : ℕ} {pts : List (ℕ × ℕ × ℕ)} {segs : List SegE} {rects : List RectE}
  {x0 x1 y0 y1 u0 u1 : ℕ}

theorem CovMP.splitX (m : ℕ) (h1 : CovMP D S Mq R W pts segs rects x0 m y0 y1 u0 u1)
    (h2 : CovMP D S Mq R W pts segs rects m x1 y0 y1 u0 u1) :
    CovMP D S Mq R W pts segs rects x0 x1 y0 y1 u0 u1 := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub
  rcases le_total c.1 ((m : ℝ) / (D * S)) with h | h
  · exact h1 c u hx0 h hy0 hy1 hu0 hu1 hsub
  · exact h2 c u h hx1 hy0 hy1 hu0 hu1 hsub

theorem CovMP.splitY (m : ℕ) (h1 : CovMP D S Mq R W pts segs rects x0 x1 y0 m u0 u1)
    (h2 : CovMP D S Mq R W pts segs rects x0 x1 m y1 u0 u1) :
    CovMP D S Mq R W pts segs rects x0 x1 y0 y1 u0 u1 := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub
  rcases le_total c.2 ((m : ℝ) / (D * S)) with h | h
  · exact h1 c u hx0 hx1 hy0 h hu0 hu1 hsub
  · exact h2 c u hx0 hx1 h hy1 hu0 hu1 hsub

theorem CovMP.splitU (m : ℕ) (h1 : CovMP D S Mq R W pts segs rects x0 x1 y0 y1 u0 m)
    (h2 : CovMP D S Mq R W pts segs rects x0 x1 y0 y1 m u1) :
    CovMP D S Mq R W pts segs rects x0 x1 y0 y1 u0 u1 := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub
  rcases le_total u ((m : ℝ) / R) with h | h
  · exact h1 c u hx0 hx1 hy0 hy1 hu0 h hsub
  · exact h2 c u hx0 hx1 hy0 hy1 h hu1 hsub

/-- A points-and-segments certificate is a certificate with rectangles (their mass is `≥ 0`). -/
theorem CovMP.of_covM (h : CovM D S Mq R W pts segs x0 x1 y0 y1 u0 u1) :
    CovMP D S Mq R W pts segs rects x0 x1 y0 y1 u0 u1 := by
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 hsub
  have := h c u hx0 hx1 hy0 hy1 hu0 hu1 hsub
  linarith [rectMass_nonneg D rects (sq c (2 * Real.arctan u) 1)]

/-! ## The `LEB` leaf (Lemma U) -/

/-- An upper bound of `w(θ) = cos θ + sin θ` on the bin `u ∈ [U0/R, U1/R] ⊆ [0, 1]`: the numerator
`1 − u² + 2u` is at most `1 − (U0/R)² + 2 U1/R`, the denominator `1 + u²` at least `1 + (U0/R)²`.
As the fraction `widN/widD` of naturals. -/
def widN (R U0 U1 : ℕ) : ℕ := R * R + 2 * U1 * R - U0 * U0
def widD (R U0 : ℕ) : ℕ := R * R + U0 * U0

lemma wid_le_widHat {R U0 U1 : ℕ} (hR : 0 < R) (hU1 : U1 ≤ R) {u : ℝ} (hu0 : (U0 : ℝ) / R ≤ u)
    (hu1 : u ≤ (U1 : ℝ) / R) :
    wid (2 * Real.arctan u) ≤ (widN R U0 U1 : ℝ) / widD R U0 := by
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have h0u : 0 ≤ u := le_trans (by positivity) hu0
  have hu0' : (U0 : ℝ) ≤ R * u := by rw [div_le_iff₀ hRr] at hu0; linarith
  have hu1' : R * u ≤ (U1 : ℝ) := by rw [le_div_iff₀ hRr] at hu1; linarith
  have hU1r : (U1 : ℝ) ≤ R := by exact_mod_cast hU1
  have hu1'' : u ≤ 1 := by nlinarith
  have hUU : U0 * U0 ≤ R * R + 2 * U1 * R := by
    have : (U0 : ℝ) ≤ U1 := le_trans hu0' hu1'
    have h2 : U0 ≤ U1 := by exact_mod_cast this
    nlinarith
  rw [wid_two_arctan h0u hu1'', widU, widN, widD, Nat.cast_sub hUU]
  push_cast
  have hD : (0 : ℝ) < (R : ℝ) * R + U0 * U0 := by positivity
  rw [div_le_div_iff₀ (by positivity) hD]
  -- `(1 − u² + 2u)(R² + U0²) ≤ (R² + 2 U1 R − U0²)(1 + u²)`
  have hU0 : (0 : ℝ) ≤ U0 := Nat.cast_nonneg _
  nlinarith [mul_nonneg hU0 hU0, mul_nonneg h0u h0u, mul_nonneg hU0 h0u,
    mul_le_mul_of_nonneg_left hu0' hU0, mul_le_mul_of_nonneg_left hu1' hRr.le,
    mul_le_mul_of_nonneg_left hu0' h0u, mul_nonneg (sub_nonneg.mpr hu1') (mul_nonneg h0u h0u),
    mul_nonneg (sub_nonneg.mpr hu1') hRr.le, mul_nonneg (sub_nonneg.mpr hu0') (sub_nonneg.mpr hu0')]

/-- The natural-number test of `LEB`: the bin is in `[0, 1]`, the density is `≥ W`, and the box of
centres widened by `widHat/2` on every side lies in the rectangle. -/
def lebOk (D S R W x0 x1 y0 y1 u0 u1 : ℕ) (e : RectE) : Bool :=
  Nat.ble u1 R && Nat.ble u0 u1 && Nat.ble W e.2.2.2.2 &&
    Nat.ble (2 * e.1 * S * widD R u0 + D * S * widN R u0 u1) (2 * x0 * widD R u0) &&
    Nat.ble (2 * x1 * widD R u0 + D * S * widN R u0 u1) (2 * e.2.2.1 * S * widD R u0) &&
    Nat.ble (2 * e.2.1 * S * widD R u0 + D * S * widN R u0 u1) (2 * y0 * widD R u0) &&
    Nat.ble (2 * y1 * widD R u0 + D * S * widN R u0 u1) (2 * e.2.2.2.1 * S * widD R u0)

lemma half_add_le {A x D S Wn Wd : ℕ} (hD : 0 < D) (hS : 0 < S) (hWd : 0 < Wd)
    (h : 2 * A * S * Wd + D * S * Wn ≤ 2 * x * Wd) :
    (A : ℝ) / D + (Wn : ℝ) / Wd / 2 ≤ (x : ℝ) / (D * S) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have hWr : (0 : ℝ) < Wd := by exact_mod_cast hWd
  have hr : ((2 * A * S * Wd + D * S * Wn : ℕ) : ℝ) ≤ ((2 * x * Wd : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hr
  have e1 : (A : ℝ) / D + (Wn : ℝ) / Wd / 2 =
      (2 * A * S * Wd + D * S * Wn) / (2 * D * S * Wd) := by field_simp
  have e2 : (x : ℝ) / (D * S) = (2 * x * Wd) / (2 * D * S * Wd) := by field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right hr (by positivity)

lemma add_half_le {A x D S Wn Wd : ℕ} (hD : 0 < D) (hS : 0 < S) (hWd : 0 < Wd)
    (h : 2 * x * Wd + D * S * Wn ≤ 2 * A * S * Wd) :
    (x : ℝ) / (D * S) + (Wn : ℝ) / Wd / 2 ≤ (A : ℝ) / D := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have hWr : (0 : ℝ) < Wd := by exact_mod_cast hWd
  have hr : ((2 * x * Wd + D * S * Wn : ℕ) : ℝ) ≤ ((2 * A * S * Wd : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hr
  have e1 : (x : ℝ) / (D * S) + (Wn : ℝ) / Wd / 2 =
      (2 * x * Wd + D * S * Wn) / (2 * D * S * Wd) := by field_simp
  have e2 : (A : ℝ) / D = (2 * A * S * Wd) / (2 * D * S * Wd) := by field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right hr (by positivity)

/-- A closed unit square inside a rectangle of `rects` captures its density. -/
lemma rectMass_ge_of_subset {e : RectE} (he : e ∈ rects) {Qs : Set (ℝ × ℝ)} {c : ℝ × ℝ} {θ : ℝ}
    (hQ : Qs = sq c θ 1) (hsub : Qs ⊆ rectSet D e) :
    (e.2.2.2.2 : ℝ) ≤ rectMass D rects Qs := by
  have hvol : (volume (Qs ∩ rectSet D e)).toReal = 1 := by
    rw [Set.inter_eq_left.mpr hsub, hQ, SqArea.volume_sq]; simp
  have := Finset.single_le_sum (f := fun e => (e.2.2.2.2 : ℝ) * (volume (Qs ∩ rectSet D e)).toReal)
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg) (List.mem_toFinset.mpr he)
  simp only [hvol, mul_one] at this
  exact this

/-- **Soundness of the `LEB` leaf.** -/
theorem CovMP.of_leb (hD : 0 < D) (hS : 0 < S) (hR : 0 < R) {e : RectE} (he : e ∈ rects)
    (h : lebOk D S R W x0 x1 y0 y1 u0 u1 e = true) :
    CovMP D S Mq R W pts segs rects x0 x1 y0 y1 u0 u1 := by
  simp only [lebOk, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hu1R, hu01⟩, hW⟩, hX0⟩, hX1⟩, hY0⟩, hY1⟩ := h
  intro c u hx0 hx1 hy0 hy1 hu0 hu1 _
  have hwd : 0 < widD R u0 := by unfold widD; have : 0 < R * R := Nat.mul_pos hR hR; omega
  have hw := wid_le_widHat hR hu1R hu0 hu1
  have a1 := half_add_le hD hS hwd hX0
  have a2 := add_half_le hD hS hwd hX1
  have a3 := half_add_le hD hS hwd hY0
  have a4 := add_half_le hD hS hwd hY1
  have hsub : sq c (2 * Real.arctan u) 1 ⊆ rectSet D e := by
    intro p hp
    obtain ⟨h1, h2⟩ := abs_sub_le_wid hp
    rw [abs_le] at h1 h2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hr := rectMass_ge_of_subset (D := D) he rfl hsub
  have hWr : (W : ℝ) ≤ e.2.2.2.2 := by exact_mod_cast hW
  linarith [ptMass_nonneg D pts (sq c (2 * Real.arctan u) 1),
    segMass_nonneg D segs (sq c (2 * Real.arctan u) 1)]

end ZMTreeM

end SquarePacking
