import Sqpack.SquareArea
import Sqpack.CovMP
import Sqpack.D4

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

section swap

variable {c : ℝ × ℝ} {θ : ℝ}

/-- `x ↔ y` maps `Q(c, θ)` onto `Q(swap c, π/2 − θ)`. -/
lemma mem_sq_swap (p : ℝ × ℝ) :
    swapXY p ∈ sq (swapXY c) (Real.pi / 2 - θ) 1 ↔ p ∈ sq c θ 1 := by
  rw [show Real.pi / 2 - θ = -θ + Real.pi / 2 by ring, sq_add_pi_div_two, mem_sq_swapXY]

lemma swap_preimage_sq :
    swapXY ⁻¹' (sq (swapXY c) (Real.pi / 2 - θ) 1) = sq c θ 1 := by
  ext p; exact mem_sq_swap p

lemma volume_cap_y (a : ℝ) :
    volume (sq c θ 1 ∩ {p | p.2 < a}) =
      volume (sq (swapXY c) (Real.pi / 2 - θ) 1 ∩ {p | p.1 < a}) := by
  have hmp : MeasurePreserving (swapXY : ℝ × ℝ → ℝ × ℝ) volume volume := by
    have : (swapXY : ℝ × ℝ → ℝ × ℝ) = Prod.swap := by funext p; rfl
    rw [this, Measure.volume_eq_prod]; exact Measure.measurePreserving_swap
  have hmeas : MeasurableSet (sq (swapXY c) (Real.pi / 2 - θ) 1 ∩ {p : ℝ × ℝ | p.1 < a}) :=
    (isClosed_sq' _ _ 1).measurableSet.inter (measurableSet_lt measurable_fst measurable_const)
  rw [← hmp.measure_preimage hmeas.nullMeasurableSet]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, mem_sq_swap]
  rfl

lemma segFrac_swap (a b : ℝ × ℝ) :
    segFrac (swapXY a) (swapXY b) (sq (swapXY c) (Real.pi / 2 - θ) 1) = segFrac a b (sq c θ 1) := by
  unfold segFrac
  congr 2
  ext t
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  rw [← mem_sq_swap (c := c) (θ := θ)]
  rfl

/-- **The other side**: the cap of `Q` below `y = a`, paid by horizontal pieces on the line
(the hypotheses read on the swapped square). -/
theorem side_y (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) {a : ℝ} (ha : a ≤ c.2) {we ρ dbar : ℝ}
    (hwe : 0 ≤ we) (hρ : 0 ≤ ρ)
    (hd : a - xmin (swapXY c) (Real.pi / 2 - θ) ≤ dbar) (hwd : we * dbar ≤ ρ)
    (pcs : List (ℝ × ℝ × ℝ)) {P : ℝ} (hch : ChainFrom P (pcs.map fun p => (p.1, p.2.1)))
    (hpos : ∀ p ∈ pcs, p.1 < p.2.1) (hden : ∀ p ∈ pcs, ρ * (p.2.1 - p.1) ≤ p.2.2)
    (hP : lo (swapXY c) (Real.pi / 2 - θ) a < hi (swapXY c) (Real.pi / 2 - θ) a →
      P ≤ lo (swapXY c) (Real.pi / 2 - θ) a ∧
        hi (swapXY c) (Real.pi / 2 - θ) a ≤ endOf P (pcs.map fun p => (p.1, p.2.1))) :
    we * (volume (sq c θ 1 ∩ {p | p.2 < a})).toReal ≤
      (pcs.map fun p => p.2.2 * segFrac (p.1, a) (p.2.1, a) (sq c θ 1)).sum := by
  have hs' : 0 < Real.sin (Real.pi / 2 - θ) := by rw [Real.sin_pi_div_two_sub]; exact hc
  have hc' : 0 < Real.cos (Real.pi / 2 - θ) := by rw [Real.cos_pi_div_two_sub]; exact hs
  have h := side_x (c := swapXY c) hs' hc' (a := a) ha hwe hρ hd hwd pcs hch hpos hden hP
  rw [volume_cap_y]
  refine h.trans (le_of_eq ?_)
  congr 1
  refine List.map_congr_left fun p _ => ?_
  rw [← segFrac_swap (c := c) (θ := θ) (p.1, a) (p.2.1, a)]
  rfl

end swap

section pose

open ZMTreeM

variable {c : ℝ × ℝ} {θ : ℝ}

/-- The segment mass of a sub-list of distinct entries is at most the whole segment mass. -/
lemma segMass_ge_sub {D : ℕ} {segs : List SegE} (l : List SegE) (hnd : l.Nodup)
    (hsub : ∀ x ∈ l, x ∈ segs) (Qs : Set (ℝ × ℝ)) :
    (l.map fun x => (x.2.2.2.2 : ℝ) * segFrac (segA D x) (segB D x) Qs).sum ≤ segMass D segs Qs := by
  unfold segMass
  rw [← List.sum_toFinset _ hnd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => List.mem_toFinset.mpr (hsub x (List.mem_toFinset.mp hx)))
    fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (segFrac_nonneg _ _ _)

/-- **Lemma K at one pose**: if the square lies left of and below the far sides of the rectangle `e`
(weight `we` per area) and its two caps are paid by distinct pieces of the cover, its mass is at
least `we`. -/
theorem lemmaK_pose {D : ℕ} (hD : 0 < D) {segs : List SegE} {rects : List RectE} {e : RectE}
    (he : e ∈ rects) (hQ : ∀ p ∈ sq c θ 1, p.1 ≤ (e.2.2.1 : ℝ) / D ∧ p.2 ≤ (e.2.2.2.1 : ℝ) / D)
    (chX chY : List SegE) (hnd : (chX ++ chY).Nodup) (hsegs : ∀ x ∈ chX ++ chY, x ∈ segs)
    (hX : (e.2.2.2.2 : ℝ) * (volume (sq c θ 1 ∩ {p | p.1 < (e.1 : ℝ) / D})).toReal ≤
      (chX.map fun x => (x.2.2.2.2 : ℝ) * segFrac (segA D x) (segB D x) (sq c θ 1)).sum)
    (hY : (e.2.2.2.2 : ℝ) * (volume (sq c θ 1 ∩ {p | p.2 < (e.2.1 : ℝ) / D})).toReal ≤
      (chY.map fun x => (x.2.2.2.2 : ℝ) * segFrac (segA D x) (segB D x) (sq c θ 1)).sum) :
    (e.2.2.2.2 : ℝ) ≤ segMass D segs (sq c θ 1) + rectMass D rects (sq c θ 1) := by
  set Qs := sq c θ 1
  set we : ℝ := (e.2.2.2.2 : ℝ)
  -- the area: `1 ≤ |Q ∩ R| + |Q ∩ {x < a}| + |Q ∩ {y < a'}|`
  have hcover : Qs ⊆ (Qs ∩ rectSet D e) ∪ (Qs ∩ {p | p.1 < (e.1 : ℝ) / D}) ∪
      (Qs ∩ {p | p.2 < (e.2.1 : ℝ) / D}) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hQ p hp
    by_cases hx : p.1 < (e.1 : ℝ) / D
    · exact Or.inl (Or.inr ⟨hp, hx⟩)
    by_cases hy : p.2 < (e.2.1 : ℝ) / D
    · exact Or.inr ⟨hp, hy⟩
    exact Or.inl (Or.inl ⟨hp, ⟨not_lt.mp hx, h1⟩, ⟨not_lt.mp hy, h2⟩⟩)
  have hfin : ∀ S : Set (ℝ × ℝ), volume (Qs ∩ S) ≠ ⊤ := fun S =>
    ne_top_of_le_ne_top (by rw [volume_sq]; exact ENNReal.one_ne_top) (measure_mono Set.inter_subset_left)
  have harea : (1 : ℝ) ≤ (volume (Qs ∩ rectSet D e)).toReal +
      (volume (Qs ∩ {p | p.1 < (e.1 : ℝ) / D})).toReal + (volume (Qs ∩ {p | p.2 < (e.2.1 : ℝ) / D})).toReal := by
    set A := Qs ∩ rectSet D e
    set B := Qs ∩ {p : ℝ × ℝ | p.1 < (e.1 : ℝ) / D}
    set C := Qs ∩ {p : ℝ × ℝ | p.2 < (e.2.1 : ℝ) / D}
    have h1 : volume Qs ≤ volume (A ∪ B ∪ C) := measure_mono hcover
    have h2 : volume (A ∪ B ∪ C) ≤ volume A + volume B + volume C :=
      (measure_union_le (A ∪ B) C).trans (by gcongr; exact measure_union_le A B)
    have h := h1.trans h2
    rw [volume_sq] at h
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩, hfin _⟩) h
    rwa [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩) (hfin _),
      ENNReal.toReal_add (hfin _) (hfin _), ENNReal.toReal_one] at this
  -- the rectangle's term of `rectMass`
  have hrect : we * (volume (Qs ∩ rectSet D e)).toReal ≤ rectMass D rects Qs := by
    unfold rectMass
    exact Finset.single_le_sum (f := fun e : RectE => (e.2.2.2.2 : ℝ) * (volume (Qs ∩ rectSet D e)).toReal)
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg) (List.mem_toFinset.mpr he)
  have hseg := segMass_ge_sub (D := D) (chX ++ chY) hnd hsegs Qs
  rw [List.map_append, List.sum_append] at hseg
  have hwe : 0 ≤ we := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left harea hwe]

end pose

end CapK

end SquarePacking
