import Sqpack.ChordE
import Sqpack.LebE
import Sqpack.PolyMin

/-!
# Lemma E at a fixed angle: the bound is least at a vertex of the arrangement

`search/QUADRANT_EXACT.md` §4.4.  Fix `θ` with `s = sin θ > 0`, `c = cos θ > 0`.  The lower bound

  `f(c) = Σ_segments κ · max(0, clampMin M forms c) + Σ_Lebesgue ρ · (1 − ĝ(d_x(c)) − ĝ(d_y(c)))`

(`fE`) is concave on every cell of the arrangement of a list of lines `Ls` in which every form of
every segment, and every `d` and `d − s` of every Lebesgue term, is a positive multiple of a line
(`Fixed`): on such a cell each form has a fixed sign (`ChordE.concaveOn_max0_clampMin`) and each `ĝ`
is in one regime (`convexOn_ghat`).  The cell of a centre `c` in the region `poly side` is a bounded
polygon, so by `PolyMin.exists_vertex_le` some vertex `v` of the arrangement of `side ++ Ls` lies in
`poly side` with `f v ≤ f c` (**`exists_vertex_le_fE`**).
-/

open MeasureTheory Set

namespace SquarePacking

namespace LemmaE

open ChordE PolyMin

/-! ## 1.  `ĝ` is convex in each regime -/

lemma aff_eq_val (F : ℝ × ℝ × ℝ) (p : ℝ × ℝ) : aff F p = F.1 * p.1 + F.2.1 * p.2 + F.2.2 := rfl

lemma convexOn_aff (K : Set (ℝ × ℝ)) (hK : Convex ℝ K) (F : ℝ × ℝ × ℝ) : ConvexOn ℝ K (aff F) := by
  refine ⟨hK, fun x _ y _ a b _ _ hab => ?_⟩
  simp only [aff, smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
  have : b = 1 - a := by linarith
  subst this
  nlinarith

lemma convexOn_aff_sq (K : Set (ℝ × ℝ)) (hK : Convex ℝ K) (F : ℝ × ℝ × ℝ) :
    ConvexOn ℝ K (fun p => aff F p ^ 2) := by
  refine ⟨hK, fun x _ y _ a b ha hb hab => ?_⟩
  have e : aff F (a • x + b • y) = a * aff F x + b * aff F y := by
    simp only [aff, smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add]
    have : b = 1 - a := by linarith
    subst this; ring
  simp only [smul_eq_mul]
  rw [e]
  have : b = 1 - a := by linarith
  subst this
  nlinarith [mul_nonneg ha hb, sq_nonneg (aff F x - aff F y)]

/-- In each regime of `d` (`d ≤ 0`, `0 ≤ d ≤ s`, `d ≥ s`) on `K`, `ĝ ∘ d` is convex on `K`. -/
theorem convexOn_ghat (K : Set (ℝ × ℝ)) (hK : Convex ℝ K) {s co : ℝ} (hs : 0 < s) (hc : 0 < co)
    (d : ℝ × ℝ × ℝ) (h0 : (∀ p ∈ K, aff d p ≤ 0) ∨ (∀ p ∈ K, 0 ≤ aff d p))
    (h1 : (∀ p ∈ K, aff d p ≤ s) ∨ (∀ p ∈ K, s ≤ aff d p)) :
    ConvexOn ℝ K (fun p => SqArea.ghat s co (aff d p)) := by
  rcases h0 with h0 | h0
  · refine (convexOn_const 0 hK).congr fun p hp => ?_
    simp [SqArea.ghat, h0 p hp]
  rcases h1 with h1 | h1
  · -- `ĝ = d²/(2sc)`
    have hconv := (convexOn_aff_sq K hK d).smul (show (0 : ℝ) ≤ 1 / (2 * s * co) by positivity)
    refine hconv.congr fun p hp => ?_
    simp only [SqArea.ghat, smul_eq_mul]
    split_ifs with h2 h3
    · have : aff d p = 0 := le_antisymm h2 (h0 p hp)
      rw [this]; ring
    · ring
    · exact absurd (h1 p hp) h3
  · -- `ĝ = (d − s/2)/c`
    have hconv := ((convexOn_aff K hK d).sub (concaveOn_const (s / 2) hK)).smul
      (show (0 : ℝ) ≤ 1 / co by positivity)
    refine hconv.congr fun p hp => ?_
    simp only [SqArea.ghat, smul_eq_mul, Pi.sub_apply]
    have hs' := h1 p hp
    split_ifs with h2 h3
    · linarith
    · have : aff d p = s := le_antisymm h3 hs'
      rw [this]; field_simp; ring
    · field_simp

/-! ## 2.  The bound, its cells, and the vertex -/

/-- A segment term `(κ, M, forms)`: `κ · max(0, clampMin M forms)`. -/
abbrev SegT := ℝ × ℝ × List (ℝ × ℝ × ℝ)
/-- A Lebesgue term `(ρ, d_x, d_y)`: `ρ · (1 − ĝ(d_x) − ĝ(d_y))`. -/
abbrev LebT := ℝ × (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ)

/-- The lower bound of Lemma E at a fixed angle. -/
noncomputable def fE (s co : ℝ) (sts : List SegT) (lts : List LebT) (p : ℝ × ℝ) : ℝ :=
  (sts.map fun t => t.1 * max 0 (clampMin t.2.1 t.2.2 p)).sum +
    (lts.map fun l => l.1 * (1 - SqArea.ghat s co (aff l.2.1 p) - SqArea.ghat s co (aff l.2.2 p))).sum

/-- `F` is a positive multiple of a line of `Ls`. -/
def PosMul (Ls : List (ℝ × ℝ × ℝ)) (F : ℝ × ℝ × ℝ) : Prop :=
  ∃ L ∈ Ls, ∃ k : ℝ, 0 < k ∧ ∀ p, aff F p = k * aff L p

/-- Every form of every term is fixed in sign on the cells of `Ls` (and the weights are `≥ 0`). -/
def Fixed (s : ℝ) (Ls : List (ℝ × ℝ × ℝ)) (sts : List SegT) (lts : List LebT) : Prop :=
  (∀ t ∈ sts, 0 ≤ t.1 ∧ 0 ≤ t.2.1 ∧ ∀ F ∈ t.2.2, PosMul Ls F) ∧
    (∀ l ∈ lts, 0 ≤ l.1 ∧ PosMul Ls l.2.1 ∧ PosMul Ls (subF l.2.1 (constF s)) ∧
      PosMul Ls l.2.2 ∧ PosMul Ls (subF l.2.2 (constF s)))

/-- The line `L` oriented to be `≥ 0` at `c`. -/
noncomputable def orient (c : ℝ × ℝ) (L : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  if 0 ≤ aff L c then L else (-L.1, -L.2.1, -L.2.2)

lemma aff_orient (c : ℝ × ℝ) (L : ℝ × ℝ × ℝ) (p : ℝ × ℝ) :
    aff (orient c L) p = if 0 ≤ aff L c then aff L p else -aff L p := by
  unfold orient; split_ifs <;> simp [aff]; ring

lemma convex_poly (cs : List (ℝ × ℝ × ℝ)) : Convex ℝ (poly cs) := by
  intro x hx y hy a b ha hb hab C hC
  have e : C.1 * (a • x + b • y).1 + C.2.1 * (a • x + b • y).2 + C.2.2 =
      a * (C.1 * x.1 + C.2.1 * x.2 + C.2.2) + b * (C.1 * y.1 + C.2.1 * y.2 + C.2.2) := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    have : b = 1 - a := by linarith
    subst this; ring
  rw [e]
  exact add_nonneg (mul_nonneg ha (hx C hC)) (mul_nonneg hb (hy C hC))

/-- On the cell of `c`, every line of `Ls` has a fixed sign. -/
lemma sign_fixed {side Ls : List (ℝ × ℝ × ℝ)} (c : ℝ × ℝ) {L : ℝ × ℝ × ℝ} (hL : L ∈ Ls) :
    (∀ p ∈ poly (side ++ Ls.map (orient c)), 0 ≤ aff L p) ∨
      (∀ p ∈ poly (side ++ Ls.map (orient c)), aff L p ≤ 0) := by
  have hmem : orient c L ∈ side ++ Ls.map (orient c) := List.mem_append_right _ (List.mem_map_of_mem hL)
  by_cases h : 0 ≤ aff L c
  · left; intro p hp
    have := hp _ hmem
    rw [← aff_eq_val, aff_orient, if_pos h] at this; exact this
  · right; intro p hp
    have := hp _ hmem
    rw [← aff_eq_val, aff_orient, if_neg h] at this; linarith

lemma sign_of_posMul {K : Set (ℝ × ℝ)} {Ls : List (ℝ × ℝ × ℝ)} {F : ℝ × ℝ × ℝ}
    (hsign : ∀ L ∈ Ls, (∀ p ∈ K, 0 ≤ aff L p) ∨ (∀ p ∈ K, aff L p ≤ 0)) (h : PosMul Ls F) :
    (∀ p ∈ K, 0 ≤ aff F p) ∨ (∀ p ∈ K, aff F p ≤ 0) := by
  obtain ⟨L, hL, k, hk, hF⟩ := h
  rcases hsign L hL with h | h
  · left; intro p hp; rw [hF]; exact mul_nonneg hk.le (h p hp)
  · right; intro p hp; rw [hF]; exact mul_nonpos_of_nonneg_of_nonpos hk.le (h p hp)

lemma concaveOn_list_sum {ι : Type*} (K : Set (ℝ × ℝ)) (hK : Convex ℝ K) (L : List ι)
    (f : ι → ℝ × ℝ → ℝ) (hf : ∀ i ∈ L, ConcaveOn ℝ K (f i)) :
    ConcaveOn ℝ K (fun p => (L.map fun i => f i p).sum) := by
  induction L with
  | nil => simpa using concaveOn_const (0 : ℝ) hK
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf a List.mem_cons_self).add (ih fun i hi => hf i (List.mem_cons_of_mem _ hi))

/-- `fE` is concave on every cell. -/
theorem concaveOn_fE {s co : ℝ} (hs : 0 < s) (hc : 0 < co) {Ls : List (ℝ × ℝ × ℝ)}
    {sts : List SegT} {lts : List LebT} (hfix : Fixed s Ls sts lts) (K : Set (ℝ × ℝ))
    (hK : Convex ℝ K) (hsign : ∀ L ∈ Ls, (∀ p ∈ K, 0 ≤ aff L p) ∨ (∀ p ∈ K, aff L p ≤ 0)) :
    ConcaveOn ℝ K (fE s co sts lts) := by
  obtain ⟨h1, h2⟩ := hfix
  refine (concaveOn_list_sum K hK sts _ fun t ht => ?_).add
    (concaveOn_list_sum K hK lts _ fun l hl => ?_)
  · obtain ⟨hk, hM, hF⟩ := h1 t ht
    exact (concaveOn_max0_clampMin K hK hM t.2.2 fun F hFm =>
      sign_of_posMul hsign (hF F hFm)).smul hk
  · obtain ⟨hρ, hx, hx', hy, hy'⟩ := h2 l hl
    have sx := sign_of_posMul hsign hx
    have sx' := sign_of_posMul hsign hx'
    have sy := sign_of_posMul hsign hy
    have sy' := sign_of_posMul hsign hy'
    have cx := convexOn_ghat K hK hs hc l.2.1 (Or.symm sx) (by
      rcases sx' with h | h
      · right; intro p hp; have := h p hp; simp only [aff_subF, aff_constF] at this; linarith
      · left; intro p hp; have := h p hp; simp only [aff_subF, aff_constF] at this; linarith)
    have cy := convexOn_ghat K hK hs hc l.2.2 (Or.symm sy) (by
      rcases sy' with h | h
      · right; intro p hp; have := h p hp; simp only [aff_subF, aff_constF] at this; linarith
      · left; intro p hp; have := h p hp; simp only [aff_subF, aff_constF] at this; linarith)
    exact (((concaveOn_const 1 hK).sub cx).sub cy).smul hρ

/-- **Lemma E's vertex reduction, at a fixed angle.**  On the bounded region `poly side`, `fE` at any
point is at least its value at some vertex of the arrangement of `side ++ Ls` inside the region. -/
theorem exists_vertex_le_fE {s co : ℝ} (hs : 0 < s) (hc : 0 < co) {side Ls : List (ℝ × ℝ × ℝ)}
    (hb : Bornology.IsBounded (poly side)) {sts : List SegT} {lts : List LebT}
    (hfix : Fixed s Ls sts lts) {c : ℝ × ℝ} (hcs : c ∈ poly side) :
    ∃ v ∈ poly side, (∃ C1 ∈ side ++ Ls, ∃ C2 ∈ side ++ Ls, C1.1 * C2.2.1 - C1.2.1 * C2.1 ≠ 0 ∧
      aff C1 v = 0 ∧ aff C2 v = 0) ∧ fE s co sts lts v ≤ fE s co sts lts c := by
  set cs := side ++ Ls.map (orient c)
  have hsub : poly cs ⊆ poly side := fun p hp C hC => hp C (List.mem_append_left _ hC)
  have hcK : c ∈ poly cs := by
    intro C hC
    rcases List.mem_append.mp hC with h | h
    · exact hcs C h
    · obtain ⟨L, _, rfl⟩ := List.mem_map.mp h
      rw [← aff_eq_val, aff_orient]
      split_ifs with h' <;> [exact h'; linarith]
  have hconc := concaveOn_fE hs hc hfix (poly cs) (convex_poly cs) fun L hL => sign_fixed c hL
  obtain ⟨v, hv, ⟨C1, hC1, C2, hC2, hdet, ht1, ht2⟩, hle⟩ :=
    exists_vertex_le cs (hb.subset hsub) _ hconc hcK
  -- a constraint of `cs` is a constraint of `side ++ Ls` up to sign
  have back : ∀ C ∈ cs, ∃ C' ∈ side ++ Ls, (C' = C ∨ C' = (-C.1, -C.2.1, -C.2.2)) := by
    intro C hC
    rcases List.mem_append.mp hC with h | h
    · exact ⟨C, List.mem_append_left _ h, Or.inl rfl⟩
    · obtain ⟨L, hL, rfl⟩ := List.mem_map.mp h
      refine ⟨L, List.mem_append_right _ hL, ?_⟩
      unfold orient; split_ifs
      · exact Or.inl rfl
      · right; simp
  obtain ⟨D1, hD1, e1⟩ := back C1 hC1
  obtain ⟨D2, hD2, e2⟩ := back C2 hC2
  refine ⟨v, hsub hv, ⟨D1, hD1, D2, hD2, ?_, ?_, ?_⟩, hle⟩
  · rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl
    · exact hdet
    · intro h; apply hdet; dsimp only at h; linarith
    · intro h; apply hdet; dsimp only at h; linarith
    · intro h; apply hdet; dsimp only at h; linarith
  · rcases e1 with rfl | rfl
    · exact ht1
    · simp only [aff]; linarith
  · rcases e2 with rfl | rfl
    · exact ht2
    · simp only [aff]; linarith

end LemmaE

end SquarePacking
