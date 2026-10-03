import Sqpack.CovMP
import Sqpack.LemmaEPoly

/-!
# A Lebesgue credit: strips inside every admissible square

For a box of centres `[x0/Q, x1/Q] × [y0/Q, y1/Q]` and angles `θ = 2 arctan u`, `u ∈ [U0/R, U1/R]`,
a list of horizontal strips `[xa/G, xb/G] × [yb/G, (yb + h)/G]`, each inside a Lebesgue rectangle `e`
of the cover and inside the closed unit square of every admissible pose, gives the credit
`amt ≤ w_e · Σ area` towards the rectangle's mass (`cred_sound`).

A point `p` is in the square of centre `c` iff both rotated coordinates are in `[-1/2, 1/2]`; times
`1 + u²` each bound is a polynomial of degree 2 in `u`, checked by Bernstein (`ptOk`) with `c` at
the box corners.  The coordinates are monotone in `c` and in `p` (`cos θ, sin θ ≥ 0`), so the corner
checks bound them on the whole box and the whole strip.
-/

open MeasureTheory

namespace SquarePacking

namespace LebCredit

open BernZ LemmaEPoly ZMTreeM

/-- `(xa, xb, yb)`: the strip `[xa/G, xb/G] × [yb/G, (yb + h)/G]`. -/
abbrev Strip := ℕ × ℕ × ℕ

/-- A credit: the rectangle, the denominator `G`, the strip height `h`, the amount (units of the
rectangle weight's scale, like `W`) and the strips (`yb` increasing by at least `h`). -/
structure Cred where
  e : RectE
  G : ℕ
  h : ℕ
  amt : ℕ
  strips : List Strip

/-! ## 1.  A point in every square -/

/-- The bounds of the point `(a/G, b/G)` against the centre `(x/Q, y/Q)`, times `2GQ(1 + u²)`:
`A cos + B sin ≤ 1/2`, `≥ -1/2`, `-A sin + B cos ≤ 1/2`, `≥ -1/2` (`A = a/G − x/Q`, `B = b/G − y/Q`). -/
def q0 (H dx dy : ℤ) : Poly := [H - 2 * dx, -4 * dy, H + 2 * dx]
def q1 (H dx dy : ℤ) : Poly := [H + 2 * dx, 4 * dy, H - 2 * dx]
def q2 (H dx dy : ℤ) : Poly := [H - 2 * dy, 4 * dx, H + 2 * dy]
def q3 (H dx dy : ℤ) : Poly := [H + 2 * dy, -4 * dx, H - 2 * dy]

/-- The four bounds at the centre `(x/Q, y/Q)`. -/
def cOk (G Q U0 U1 R a b x y : ℕ) : Bool :=
  let dx : ℤ := (a : ℤ) * Q - (x : ℤ) * G
  let dy : ℤ := (b : ℤ) * Q - (y : ℤ) * G
  let H : ℤ := (G : ℤ) * Q
  check (q0 H dx dy) 2 U0 U1 R && check (q1 H dx dy) 2 U0 U1 R &&
    check (q2 H dx dy) 2 U0 U1 R && check (q3 H dx dy) 2 U0 U1 R

/-- The point `(a/G, b/G)` passes the bounds at the four box corners. -/
def ptOk (G Q x0 x1 y0 y1 U0 U1 R a b : ℕ) : Bool :=
  cOk G Q U0 U1 R a b x0 y0 && cOk G Q U0 U1 R a b x0 y1 && cOk G Q U0 U1 R a b x1 y0 &&
    cOk G Q U0 U1 R a b x1 y1

/-- The rotated coordinates, with `co = cos θ`, `s = sin θ`. -/
def E1 (co s : ℝ) (p c : ℝ × ℝ) : ℝ := (p.1 - c.1) * co + (p.2 - c.2) * s
def E2 (co s : ℝ) (p c : ℝ × ℝ) : ℝ := -(p.1 - c.1) * s + (p.2 - c.2) * co

/-- The four bounds of a point at a centre, as real inequalities. -/
structure In4 (co s : ℝ) (p c : ℝ × ℝ) : Prop where
  h0 : E1 co s p c ≤ 1 / 2
  h1 : -(1 / 2) ≤ E1 co s p c
  h2 : E2 co s p c ≤ 1 / 2
  h3 : -(1 / 2) ≤ E2 co s p c

section point

variable {G Q R U0 U1 : ℕ} {u : ℝ}

lemma cOk_sound (hG : 0 < G) (hQ : 0 < Q) (hR : 0 < R) {a b x y : ℕ}
    (h : cOk G Q U0 U1 R a b x y = true)
    (hb0 : (U0 : ℝ) / R ≤ u) (hb1 : u ≤ (U1 : ℝ) / R) :
    In4 ((1 - u ^ 2) / (1 + u ^ 2)) (2 * u / (1 + u ^ 2)) ((a : ℝ) / G, (b : ℝ) / G)
      ((x : ℝ) / Q, (y : ℝ) / Q) := by
  simp only [cOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨c0, c1⟩, c2⟩, c3⟩ := h
  have e0 := nonneg_of_check c0 hR hb0 hb1
  have e1 := nonneg_of_check c1 hR hb0 hb1
  have e2 := nonneg_of_check c2 hR hb0 hb1
  have e3 := nonneg_of_check c3 hR hb0 hb1
  simp only [q0, q1, q2, q3, eval_cons, eval_nil, mul_zero, add_zero] at e0 e1 e2 e3
  push_cast at e0 e1 e2 e3
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hN : (0 : ℝ) < 1 + u ^ 2 := by positivity
  set A : ℝ := (a : ℝ) / G - (x : ℝ) / Q with hA
  set B : ℝ := (b : ℝ) / G - (y : ℝ) / Q with hB
  have dxA : (a : ℝ) * Q - x * G = G * Q * A := by rw [hA]; field_simp
  have dyB : (b : ℝ) * Q - y * G = G * Q * B := by rw [hB]; field_simp
  have hGQ : (0 : ℝ) < G * Q := by positivity
  rw [dxA, dyB] at e0 e1 e2 e3
  have key : ∀ T : ℝ, 0 ≤ G * Q * T → 0 ≤ T := fun T h => (mul_nonneg_iff_of_pos_left hGQ).mp h
  have g0 : G * Q * ((1 + u ^ 2) - 2 * A * (1 - u ^ 2) - 4 * B * u) = G * Q - 2 * (G * Q * A) +
      u * (-4 * (G * Q * B) + u * (G * Q + 2 * (G * Q * A))) := by ring
  have g1 : G * Q * ((1 + u ^ 2) + 2 * A * (1 - u ^ 2) + 4 * B * u) = G * Q + 2 * (G * Q * A) +
      u * (4 * (G * Q * B) + u * (G * Q - 2 * (G * Q * A))) := by ring
  have g2 : G * Q * ((1 + u ^ 2) - 2 * B * (1 - u ^ 2) + 4 * A * u) = G * Q - 2 * (G * Q * B) +
      u * (4 * (G * Q * A) + u * (G * Q + 2 * (G * Q * B))) := by ring
  have g3 : G * Q * ((1 + u ^ 2) + 2 * B * (1 - u ^ 2) - 4 * A * u) = G * Q + 2 * (G * Q * B) +
      u * (-4 * (G * Q * A) + u * (G * Q - 2 * (G * Q * B))) := by ring
  have k0 := key _ (g0 ▸ e0)
  have k1 := key _ (g1 ▸ e1)
  have k2 := key _ (g2 ▸ e2)
  have k3 := key _ (g3 ▸ e3)
  have f1 : E1 ((1 - u ^ 2) / (1 + u ^ 2)) (2 * u / (1 + u ^ 2)) ((a : ℝ) / G, (b : ℝ) / G)
      ((x : ℝ) / Q, (y : ℝ) / Q) = (A * (1 - u ^ 2) + B * (2 * u)) / (1 + u ^ 2) := by
    simp only [E1]; rw [hA, hB]; field_simp
  have f2 : E2 ((1 - u ^ 2) / (1 + u ^ 2)) (2 * u / (1 + u ^ 2)) ((a : ℝ) / G, (b : ℝ) / G)
      ((x : ℝ) / Q, (y : ℝ) / Q) = (-A * (2 * u) + B * (1 - u ^ 2)) / (1 + u ^ 2) := by
    simp only [E2]; rw [hA, hB]; field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [f1, div_le_iff₀ hN]; linarith
  · rw [f1, le_div_iff₀ hN]; linarith
  · rw [f2, div_le_iff₀ hN]; linarith
  · rw [f2, le_div_iff₀ hN]; linarith

lemma ptOk_sound (hG : 0 < G) (hQ : 0 < Q) (hR : 0 < R) {x0 x1 y0 y1 a b : ℕ}
    (h : ptOk G Q x0 x1 y0 y1 U0 U1 R a b = true) (hu0 : 0 < u) (hu1 : u < 1)
    (hb0 : (U0 : ℝ) / R ≤ u) (hb1 : u ≤ (U1 : ℝ) / R) {c : ℝ × ℝ}
    (hx0 : (x0 : ℝ) / Q ≤ c.1) (hx1 : c.1 ≤ (x1 : ℝ) / Q) (hy0 : (y0 : ℝ) / Q ≤ c.2)
    (hy1 : c.2 ≤ (y1 : ℝ) / Q) :
    In4 ((1 - u ^ 2) / (1 + u ^ 2)) (2 * u / (1 + u ^ 2)) ((a : ℝ) / G, (b : ℝ) / G) c := by
  simp only [ptOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨d00, d01⟩, d10⟩, d11⟩ := h
  have k00 := cOk_sound hG hQ hR d00 hb0 hb1
  have k01 := cOk_sound hG hQ hR d01 hb0 hb1
  have k10 := cOk_sound hG hQ hR d10 hb0 hb1
  have k11 := cOk_sound hG hQ hR d11 hb0 hb1
  have hN : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have hco : 0 ≤ (1 - u ^ 2) / (1 + u ^ 2) := div_nonneg (by nlinarith) hN.le
  have hs : 0 ≤ 2 * u / (1 + u ^ 2) := div_nonneg (by linarith) hN.le
  set co := (1 - u ^ 2) / (1 + u ^ 2)
  set t := 2 * u / (1 + u ^ 2)
  have m1 := k00.h0; have m2 := k11.h1; have m3 := k10.h2; have m4 := k01.h3
  simp only [E1, E2] at m1 m2 m3 m4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [E1, E2]
  · linarith [mul_le_mul_of_nonneg_right hx0 hco, mul_le_mul_of_nonneg_right hy0 hs]
  · linarith [mul_le_mul_of_nonneg_right hx1 hco, mul_le_mul_of_nonneg_right hy1 hs]
  · linarith [mul_le_mul_of_nonneg_right hx1 hs, mul_le_mul_of_nonneg_right hy0 hco]
  · linarith [mul_le_mul_of_nonneg_right hx0 hs, mul_le_mul_of_nonneg_right hy1 hco]

end point

/-! ## 2.  Strips -/

/-- The strip `[xa/G, xb/G] × [yb/G, (yb + h)/G)` (half-open in `y`, so consecutive strips are
disjoint). -/
def stripSet (G h : ℕ) (s : Strip) : Set (ℝ × ℝ) :=
  Set.Icc ((s.1 : ℝ) / G) ((s.2.1 : ℝ) / G) ×ˢ Set.Ico ((s.2.2 : ℝ) / G) (((s.2.2 + h : ℕ) : ℝ) / G)

/-- A strip inside the rectangle `e` (over `D`) with its four corners in every admissible square. -/
def stripOk (D G Q x0 x1 y0 y1 U0 U1 R h : ℕ) (e : RectE) (s : Strip) : Bool :=
  Nat.ble s.1 s.2.1 && Nat.ble (e.1 * G) (s.1 * D) && Nat.ble (s.2.1 * D) (e.2.2.1 * G) &&
    Nat.ble (e.2.1 * G) (s.2.2 * D) && Nat.ble ((s.2.2 + h) * D) (e.2.2.2.1 * G) &&
    ptOk G Q x0 x1 y0 y1 U0 U1 R s.1 s.2.2 && ptOk G Q x0 x1 y0 y1 U0 U1 R s.2.1 s.2.2 &&
    ptOk G Q x0 x1 y0 y1 U0 U1 R s.1 (s.2.2 + h) && ptOk G Q x0 x1 y0 y1 U0 U1 R s.2.1 (s.2.2 + h)

section strip

variable {D G Q R U0 U1 x0 x1 y0 y1 h : ℕ} {e : RectE} {s : Strip}

lemma strip_sub_rect (hD : 0 < D) (hG : 0 < G) (hs : stripOk D G Q x0 x1 y0 y1 U0 U1 R h e s = true) :
    stripSet G h s ⊆ rectSet D e := by
  simp only [stripOk, Bool.and_eq_true, Nat.ble_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, r1⟩, r2⟩, r3⟩, r4⟩, _⟩, _⟩, _⟩, _⟩ := hs
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  have q1 : (e.1 : ℝ) / D ≤ (s.1 : ℝ) / G := by
    rw [div_le_div_iff₀ hDr hGr]; exact_mod_cast r1
  have q2 : (s.2.1 : ℝ) / G ≤ (e.2.2.1 : ℝ) / D := by
    rw [div_le_div_iff₀ hGr hDr]; exact_mod_cast r2
  have q3 : (e.2.1 : ℝ) / D ≤ (s.2.2 : ℝ) / G := by
    rw [div_le_div_iff₀ hDr hGr]; exact_mod_cast r3
  have q4 : (((s.2.2 + h : ℕ) : ℝ)) / G ≤ (e.2.2.2.1 : ℝ) / D := by
    rw [div_le_div_iff₀ hGr hDr]; exact_mod_cast r4
  rintro p ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
  exact ⟨⟨q1.trans a1, a2.trans q2⟩, ⟨q3.trans b1, b2.le.trans q4⟩⟩

lemma strip_sub_sq (hG : 0 < G) (hQ : 0 < Q) (hR : 0 < R)
    (hs : stripOk D G Q x0 x1 y0 y1 U0 U1 R h e s = true) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hb0 : (U0 : ℝ) / R ≤ u) (hb1 : u ≤ (U1 : ℝ) / R) {c : ℝ × ℝ}
    (hx0 : (x0 : ℝ) / Q ≤ c.1) (hx1 : c.1 ≤ (x1 : ℝ) / Q) (hy0 : (y0 : ℝ) / Q ≤ c.2)
    (hy1 : c.2 ≤ (y1 : ℝ) / Q) :
    stripSet G h s ⊆ sq c (2 * Real.arctan u) 1 := by
  simp only [stripOk, Bool.and_eq_true, Nat.ble_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, p00⟩, p10⟩, p01⟩, p11⟩ := hs
  have k00 := ptOk_sound hG hQ hR p00 hu0 hu1 hb0 hb1 hx0 hx1 hy0 hy1
  have k10 := ptOk_sound hG hQ hR p10 hu0 hu1 hb0 hb1 hx0 hx1 hy0 hy1
  have k01 := ptOk_sound hG hQ hR p01 hu0 hu1 hb0 hb1 hx0 hx1 hy0 hy1
  have k11 := ptOk_sound hG hQ hR p11 hu0 hu1 hb0 hb1 hx0 hx1 hy0 hy1
  have hN : (0 : ℝ) < 1 + u ^ 2 := by positivity
  have hco : 0 ≤ (1 - u ^ 2) / (1 + u ^ 2) := div_nonneg (by nlinarith) hN.le
  have hsn : 0 ≤ 2 * u / (1 + u ^ 2) := div_nonneg (by linarith) hN.le
  rintro p ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
  have b2' := b2.le
  have m1 := k11.h0; have m2 := k00.h1; have m3 := k01.h2; have m4 := k10.h3
  simp only [E1, E2] at m1 m2 m3 m4
  simp only [sq, coord, (trig u).1, (trig u).2, abs_le]
  set co := (1 - u ^ 2) / (1 + u ^ 2)
  set t := 2 * u / (1 + u ^ 2)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_right a1 hco, mul_le_mul_of_nonneg_right b1 hsn]
  · linarith [mul_le_mul_of_nonneg_right a2 hco, mul_le_mul_of_nonneg_right b2' hsn]
  · linarith [mul_le_mul_of_nonneg_right a2 hsn, mul_le_mul_of_nonneg_right b1 hco]
  · linarith [mul_le_mul_of_nonneg_right a1 hsn, mul_le_mul_of_nonneg_right b2' hco]

end strip

end LebCredit

end SquarePacking
