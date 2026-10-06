import Sqpack.SquareArea
import Sqpack.CovMP

/-!
# Lemma K (caps of the Lebesgue rectangle paid by the segments on its sides)

A closed unit square `Q` with centre right of the line `x = a` loses at most `d · len(a)` of area
left of the line (`SqArea.cap_le_chord`, `d = a − x_min`), where `len(a)` is the chord of `Q` on the
line.  If the cover's pieces on `x = a` cover the chord with density (weight per length) at least
`ρ`, they put at least `ρ · len(a)` of mass in `Q`.  So `w · d ≤ ρ` (the rectangle's weight `w` per
area) pays for the cap.  With the same on `y = a`, a square inside `{x ≤ b, y ≤ b}` has mass at
least the rectangle's weight (`QUADRANT_EXACT.md` §4.2, Lemma K).

Here: the chord range (`chord_mem`), the mass of a vertical piece (`segFrac_vert_ge`), and a chain of
contiguous pieces (`chain_mass_ge`).
-/

open MeasureTheory Set

namespace SquarePacking

namespace CapK

open SqArea

section chord

variable {c : ℝ × ℝ} {θ : ℝ}

/-- The ends of the chord of `Q` on the line `x = a`. -/
noncomputable def lo (c : ℝ × ℝ) (θ a : ℝ) : ℝ := max (lowX c θ a) (lowY c θ a)
noncomputable def hi (c : ℝ × ℝ) (θ a : ℝ) : ℝ := min (upX c θ a) (upY c θ a)

lemma len_eq (a : ℝ) : len c θ a = hi c θ a - lo c θ a := rfl

/-- **The chord range**: on `x = a = x_min + d`, the chord lies within `[y_TL − (cos/sin) d,
y_TL + (sin/cos) d]`, `y_TL = c_y + (cos − sin)/2` (the leftmost vertex), and within
`[c_y − (cos + sin)/2, c_y + (cos + sin)/2]`. -/
lemma hi_le (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) (a : ℝ) :
    hi c θ a ≤ c.2 + (Real.cos θ - Real.sin θ) / 2 + Real.sin θ / Real.cos θ * (a - xmin c θ) := by
  refine (min_le_right _ _).trans (le_of_eq ?_)
  have h1 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq θ
  simp only [upY, xmin]
  field_simp
  nlinarith [h1]

lemma lo_ge (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) (a : ℝ) :
    c.2 + (Real.cos θ - Real.sin θ) / 2 - Real.cos θ / Real.sin θ * (a - xmin c θ) ≤ lo c θ a := by
  refine le_trans (le_of_eq ?_) (le_max_left _ _)
  have h1 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq θ
  simp only [lowX, xmin]
  field_simp
  nlinarith [h1]

end chord

section piece

variable {c : ℝ × ℝ} {θ : ℝ}

/-- The overlap of `[p0, p1]` with the chord, nonnegative. -/
noncomputable def ovl (c : ℝ × ℝ) (θ a p0 p1 : ℝ) : ℝ := max 0 (min p1 (hi c θ a) - max p0 (lo c θ a))

/-- **A vertical piece** `[(a, p0), (a, p1)]` puts at least its overlap with the chord, over its
length, of its weight in `Q`. -/
lemma segFrac_vert_ge (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) {a p0 p1 : ℝ} (hp : p0 < p1) :
    ovl c θ a p0 p1 / (p1 - p0) ≤ segFrac (a, p0) (a, p1) (sq c θ 1) := by
  have hL : 0 < p1 - p0 := by linarith
  set t0 := max 0 ((lo c θ a - p0) / (p1 - p0))
  set t1 := min 1 ((hi c θ a - p0) / (p1 - p0))
  have hsub : Icc t0 t1 ⊆ segPt (a, p0) (a, p1) ⁻¹' sq c θ 1 ∩ Icc (0 : ℝ) 1 := by
    rintro t ⟨h0, h1⟩
    have ht0 : 0 ≤ t := (le_max_left _ _).trans h0
    have ht1 : t ≤ 1 := h1.trans (min_le_left _ _)
    have hlo : (lo c θ a - p0) / (p1 - p0) ≤ t := (le_max_right _ _).trans h0
    have hhi : t ≤ (hi c θ a - p0) / (p1 - p0) := h1.trans (min_le_right _ _)
    rw [div_le_iff₀ hL] at hlo
    rw [le_div_iff₀ hL] at hhi
    refine ⟨?_, ht0, ht1⟩
    simp only [mem_preimage, segPt, sub_self, mul_zero, add_zero]
    rw [mem_sq_iff_slice hs hc]
    exact ⟨by simp only [lo] at hlo; linarith, by simp only [hi] at hhi; linarith⟩
  have hvol := measure_mono (μ := volume) hsub
  rw [Real.volume_Icc] at hvol
  have hfin : volume (segPt (a, p0) (a, p1) ⁻¹' sq c θ 1 ∩ Icc (0 : ℝ) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono inter_subset_right)
  have key : max 0 (t1 - t0) ≤ segFrac (a, p0) (a, p1) (sq c θ 1) := by
    unfold segFrac
    rcases le_total t1 t0 with h | h
    · rw [max_eq_left (by linarith)]; exact ENNReal.toReal_nonneg
    · rw [max_eq_right (by linarith)]
      calc t1 - t0 = (ENNReal.ofReal (t1 - t0)).toReal := (ENNReal.toReal_ofReal (by linarith)).symm
        _ ≤ _ := ENNReal.toReal_mono hfin hvol
  refine le_trans ?_ key
  have a1 : (min p1 (hi c θ a) - p0) / (p1 - p0) ≤ t1 :=
    le_min (by rw [div_le_one hL]; linarith [min_le_left p1 (hi c θ a)])
      (div_le_div_of_nonneg_right (by linarith [min_le_right p1 (hi c θ a)]) hL.le)
  have a2 : t0 ≤ (max p0 (lo c θ a) - p0) / (p1 - p0) :=
    max_le (div_nonneg (by linarith [le_max_left p0 (lo c θ a)]) hL.le)
      (div_le_div_of_nonneg_right (by linarith [le_max_right p0 (lo c θ a)]) hL.le)
  unfold ovl
  rw [div_le_iff₀ hL]
  rcases le_total (min p1 (hi c θ a) - max p0 (lo c θ a)) 0 with h | h
  · rw [max_eq_left h]; positivity
  · rw [max_eq_right h]
    have : (min p1 (hi c θ a) - max p0 (lo c θ a)) / (p1 - p0) ≤ t1 - t0 := by
      have e : (min p1 (hi c θ a) - max p0 (lo c θ a)) / (p1 - p0) =
          (min p1 (hi c θ a) - p0) / (p1 - p0) - (max p0 (lo c θ a) - p0) / (p1 - p0) := by
        rw [← sub_div]; ring_nf
      rw [e]; linarith
    rw [div_le_iff₀ hL] at this
    nlinarith [le_max_right 0 (t1 - t0)]

end piece

section chain

/-- The overlap of `[x, y]` with `[lo, hi]`. -/
noncomputable def ov (lo hi x y : ℝ) : ℝ := max 0 (min y hi - max x lo)

lemma ov_nonneg (lo hi x y : ℝ) : 0 ≤ ov lo hi x y := le_max_left _ _

lemma ov_add {lo hi x m y : ℝ} (h1 : x ≤ m) (h2 : m ≤ y) :
    ov lo hi x y ≤ ov lo hi x m + ov lo hi m y := by
  unfold ov
  have hA := le_max_right 0 (min m hi - max x lo)
  have hB := le_max_right 0 (min y hi - max m lo)
  have hA0 := le_max_left 0 (min m hi - max x lo)
  have hB0 := le_max_left 0 (min y hi - max m lo)
  refine max_le (by linarith) ?_
  rcases lt_or_ge m lo with h | h
  · have e1 : max x lo = lo := max_eq_right (h1.trans h.le)
    have e2 : max m lo = lo := max_eq_right h.le
    simp only [e1, e2] at hA hB hA0 hB0 ⊢; linarith
  · rcases le_or_gt m hi with h' | h'
    · have e1 : min m hi = m := min_eq_left h'
      have e2 : max m lo = m := max_eq_left h
      simp only [e1, e2] at hA hB hA0 hB0 ⊢; linarith
    · have e1 : min m hi = hi := min_eq_right h'.le
      have e2 : min y hi = hi := min_eq_right (h'.le.trans h2)
      simp only [e1, e2] at hA hB hA0 hB0 ⊢; linarith

/-- A chain of intervals starting at `x`: `[x, p₁], [p₁, p₂], …`. -/
def ChainFrom : ℝ → List (ℝ × ℝ) → Prop
  | _, [] => True
  | x, p :: l => p.1 = x ∧ p.1 ≤ p.2 ∧ ChainFrom p.2 l

/-- Its end. -/
def endOf : ℝ → List (ℝ × ℝ) → ℝ
  | x, [] => x
  | _, p :: l => endOf p.2 l

lemma le_endOf : ∀ (l : List (ℝ × ℝ)) (x : ℝ), ChainFrom x l → x ≤ endOf x l
  | [], x, _ => le_rfl
  | p :: l, x, ⟨h1, h2, h3⟩ => by
    simp only [endOf]; have := le_endOf l p.2 h3; rw [← h1]; linarith

/-- **The pieces of a chain overlap `[lo, hi]` at least as much as the whole chain does.** -/
lemma ov_chain (lo hi : ℝ) : ∀ (l : List (ℝ × ℝ)) (x : ℝ), ChainFrom x l →
    ov lo hi x (endOf x l) ≤ (l.map fun p => ov lo hi p.1 p.2).sum
  | [], x, _ => by simp [endOf, ov]
  | p :: l, x, ⟨h1, h2, h3⟩ => by
    simp only [endOf, List.map_cons, List.sum_cons]
    have ih := ov_chain lo hi l p.2 h3
    have he := le_endOf l p.2 h3
    rw [← h1]
    calc ov lo hi p.1 (endOf p.2 l) ≤ ov lo hi p.1 p.2 + ov lo hi p.2 (endOf p.2 l) := ov_add h2 he
      _ ≤ _ := by linarith

lemma ov_cover {lo hi x y : ℝ} (hx : x ≤ lo) (hy : hi ≤ y) : hi - lo ≤ ov lo hi x y := by
  unfold ov
  rw [min_eq_right hy, max_eq_right hx]; exact le_max_right _ _

end chain

section side

variable {c : ℝ × ℝ} {θ : ℝ}

/-- **One side of Lemma K**: the cap of `Q` left of `x = a` (centre right of the line), times the
weight per area `we`, is paid by a chain of vertical pieces `(p0, p1, w)` on the line covering the
chord with weight per length `≥ ρ ≥ we · d̄`. -/
theorem side_x (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) {a : ℝ} (ha : a ≤ c.1) {we ρ dbar : ℝ}
    (hwe : 0 ≤ we) (hρ : 0 ≤ ρ) (hd : a - xmin c θ ≤ dbar) (hwd : we * dbar ≤ ρ)
    (pcs : List (ℝ × ℝ × ℝ)) {P : ℝ} (hch : ChainFrom P (pcs.map fun p => (p.1, p.2.1)))
    (hpos : ∀ p ∈ pcs, p.1 < p.2.1) (hden : ∀ p ∈ pcs, ρ * (p.2.1 - p.1) ≤ p.2.2)
    (hP : lo c θ a < hi c θ a → P ≤ lo c θ a ∧ hi c θ a ≤ endOf P (pcs.map fun p => (p.1, p.2.1))) :
    we * (volume (sq c θ 1 ∩ {p | p.1 < a})).toReal ≤
      (pcs.map fun p => p.2.2 * segFrac (a, p.1) (a, p.2.1) (sq c θ 1)).sum := by
  have hcap := cap_le_chord (c := c) hs hc ha
  have hcap' : (volume (sq c θ 1 ∩ {p | p.1 < a})).toReal ≤ max 0 ((a - xmin c θ) * len c θ a) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcap
    rwa [ENNReal.toReal_ofReal', max_comm] at this
  -- each piece: `ρ · overlap ≤ w · segFrac`
  have hterm : ∀ p ∈ pcs, ρ * ov (lo c θ a) (hi c θ a) p.1 p.2.1 ≤
      p.2.2 * segFrac (a, p.1) (a, p.2.1) (sq c θ 1) := by
    intro p hp
    have hL : 0 < p.2.1 - p.1 := by linarith [hpos p hp]
    have hw : 0 ≤ p.2.2 := le_trans (mul_nonneg hρ hL.le) (hden p hp)
    have hf := segFrac_vert_ge (c := c) hs hc (a := a) (hpos p hp)
    have hov := ov_nonneg (lo c θ a) (hi c θ a) p.1 p.2.1
    calc ρ * ov (lo c θ a) (hi c θ a) p.1 p.2.1
        ≤ p.2.2 * (ov (lo c θ a) (hi c θ a) p.1 p.2.1 / (p.2.1 - p.1)) := by
          rw [mul_div_assoc', le_div_iff₀ hL]
          nlinarith [hden p hp]
      _ ≤ p.2.2 * segFrac (a, p.1) (a, p.2.1) (sq c θ 1) := mul_le_mul_of_nonneg_left hf hw
  have hsum : ρ * (pcs.map fun p => ov (lo c θ a) (hi c θ a) p.1 p.2.1).sum ≤
      (pcs.map fun p => p.2.2 * segFrac (a, p.1) (a, p.2.1) (sq c θ 1)).sum := by
    rw [← List.sum_map_mul_left]
    exact List.sum_le_sum fun p hp => hterm p hp
  have hsum0 : 0 ≤ (pcs.map fun p => ov (lo c θ a) (hi c θ a) p.1 p.2.1).sum :=
    List.sum_nonneg fun x hx => by obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx; exact ov_nonneg _ _ _ _
  have hchain := ov_chain (lo c θ a) (hi c θ a) _ P hch
  simp only [List.map_map, Function.comp_def] at hchain
  by_cases hz : len c θ a ≤ 0 ∨ a - xmin c θ ≤ 0
  · have h0 : (volume (sq c θ 1 ∩ {p | p.1 < a})).toReal = 0 := by
      rcases le_or_gt (a - xmin c θ) 0 with h | h
      · have hg := cap_le_ghat (c := c) hs hc a
        rw [show ghat (Real.sin θ) (Real.cos θ) (a - xmin c θ) = 0 by simp [ghat, h],
          ENNReal.ofReal_zero, nonpos_iff_eq_zero] at hg
        rw [hg]; rfl
      · have hl : len c θ a ≤ 0 := hz.resolve_right (not_le.mpr h)
        rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos h.le hl)] at hcap'
        exact le_antisymm hcap' ENNReal.toReal_nonneg
    rw [h0, mul_zero]; exact le_trans (mul_nonneg hρ hsum0) hsum
  · push_neg at hz
    obtain ⟨hl, hx⟩ := hz
    have hlh : lo c θ a < hi c θ a := by rw [len_eq] at hl; linarith
    obtain ⟨h1, h2⟩ := hP hlh
    have hcov := ov_cover (lo := lo c θ a) (hi := hi c θ a) h1 h2
    rw [← len_eq] at hcov
    have hmax : max 0 ((a - xmin c θ) * len c θ a) = (a - xmin c θ) * len c θ a :=
      max_eq_right (mul_pos hx hl).le
    rw [hmax] at hcap'
    calc we * (volume (sq c θ 1 ∩ {p | p.1 < a})).toReal
        ≤ we * ((a - xmin c θ) * len c θ a) := mul_le_mul_of_nonneg_left hcap' hwe
      _ ≤ we * (dbar * len c θ a) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd hl.le) hwe
      _ = (we * dbar) * len c θ a := by ring
      _ ≤ ρ * len c θ a := mul_le_mul_of_nonneg_right hwd hl.le
      _ ≤ ρ * (pcs.map fun p => ov (lo c θ a) (hi c θ a) p.1 p.2.1).sum :=
          mul_le_mul_of_nonneg_left (hcov.trans hchain) hρ
      _ ≤ _ := hsum

end side

end CapK

end SquarePacking
