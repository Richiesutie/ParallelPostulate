/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import LeanCodeParallel.HyperbolicPlane.Motions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angles in the plane of a bound

The inner product at a pair, `kleinInner`, and the angle it gives, `kleinAngle`. The motions
keep it (Theorem H13). They take every point to `(0, 0)`, where it is the angle of Euclid, so it
is the only angle with these two properties (Theorem H15).

## Contents

* Theorem H13, the motions keep angles: `kleinInner`, `kleinInner_zero_bound`,
  `kleinInner_centre`, `kleinInner_self_pos`, `shift_kleinInner`, `rot_kleinInner`, `kleinAngle`,
  `kleinAngle_zero_bound`, `kleinAngle_centre`, `shift_kleinAngle`, `rot_kleinAngle`
* Theorem H15, the motions take every point to `(0, 0)`, and the angle they keep:
  `exists_motion_to_centre`, `kleinAngle_unique`
* steps of the proofs: `kleinInner_aux`, `kleinAngle_aux`
-/

namespace HyperbolicPlane

open Pairs

/-! ## The inner product at a pair -/

section InnerAlgebra

variable {K : Type*} [Field K]

/-- **The inner product at a pair**, under the bound `κ`: at the pair `P`, of the direction from
`P` to `A` and the direction from `P` to `B`. It is the inner product of Euclid and one more
term, `κ` times two cross products. With the bound 0, or at `(0, 0)`, that term is zero.
Divided by `(1 + κ (P.1² + P.2²))²` it is Klein's metric at `P`, on the directions `A - P` and
`B - P`: `kleinMetric_sub`. -/
def kleinInner (κ : K) (P A B : K × K) : K :=
  (A.1 - P.1) * (B.1 - P.1) + (A.2 - P.2) * (B.2 - P.2) + κ * cross P A * cross P B

/-- With the bound 0 it is the inner product of Euclid. -/
theorem kleinInner_zero_bound (P A B : K × K) :
    kleinInner 0 P A B = (A.1 - P.1) * (B.1 - P.1) + (A.2 - P.2) * (B.2 - P.2) := by
  simp [kleinInner]

/-- At `(0, 0)` it is the inner product of Euclid, under any bound. -/
theorem kleinInner_centre (κ : K) (A B : K × K) :
    kleinInner κ (0, 0) A B = A.1 * B.1 + A.2 * B.2 := by
  simp [kleinInner, cross]

/-- The algebra of the next theorem, with the divisions taken out. -/
theorem kleinInner_aux (κ a w xP yP xA yA xB yB XP YP XA YA XB YB : K)
    (hw : w ^ 2 = 1 + κ * a ^ 2)
    (hXP : XP * (1 - κ * a * xP) = xP + a) (hYP : YP * (1 - κ * a * xP) = w * yP)
    (hXA : XA * (1 - κ * a * xA) = xA + a) (hYA : YA * (1 - κ * a * xA) = w * yA)
    (hXB : XB * (1 - κ * a * xB) = xB + a) (hYB : YB * (1 - κ * a * xB) = w * yB) :
    ((XA - XP) * (XB - XP) + (YA - YP) * (YB - YP)
        + κ * (XP * YA - YP * XA) * (XP * YB - YP * XB))
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xA) * (1 - κ * a * xB))
      = w ^ 4 * ((xA - xP) * (xB - xP) + (yA - yP) * (yB - yP)
        + κ * (xP * yA - yP * xA) * (xP * yB - yP * xB)) := by
  have e1 : (XA - XP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
      = (xA + a) * (1 - κ * a * xP) - (xP + a) * (1 - κ * a * xA) := by
    linear_combination (1 - κ * a * xP) * hXA - (1 - κ * a * xA) * hXP
  have e2 : (XB - XP) * ((1 - κ * a * xB) * (1 - κ * a * xP))
      = (xB + a) * (1 - κ * a * xP) - (xP + a) * (1 - κ * a * xB) := by
    linear_combination (1 - κ * a * xP) * hXB - (1 - κ * a * xB) * hXP
  have e3 : (YA - YP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
      = w * (yA * (1 - κ * a * xP) - yP * (1 - κ * a * xA)) := by
    linear_combination (1 - κ * a * xP) * hYA - (1 - κ * a * xA) * hYP
  have e4 : (YB - YP) * ((1 - κ * a * xB) * (1 - κ * a * xP))
      = w * (yB * (1 - κ * a * xP) - yP * (1 - κ * a * xB)) := by
    linear_combination (1 - κ * a * xP) * hYB - (1 - κ * a * xB) * hYP
  have e5 : (XP * YA - YP * XA) * ((1 - κ * a * xP) * (1 - κ * a * xA))
      = w * ((xP + a) * yA - yP * (xA + a)) := by
    linear_combination (YA * (1 - κ * a * xA)) * hXP + (xP + a) * hYA
      - (XA * (1 - κ * a * xA)) * hYP - (w * yP) * hXA
  have e6 : (XP * YB - YP * XB) * ((1 - κ * a * xP) * (1 - κ * a * xB))
      = w * ((xP + a) * yB - yP * (xB + a)) := by
    linear_combination (YB * (1 - κ * a * xB)) * hXP + (xP + a) * hYB
      - (XB * (1 - κ * a * xB)) * hYP - (w * yP) * hXB
  have e : ((XA - XP) * (XB - XP) + (YA - YP) * (YB - YP)
        + κ * (XP * YA - YP * XA) * (XP * YB - YP * XB))
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xA) * (1 - κ * a * xB))
      = (XA - XP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
          * ((XB - XP) * ((1 - κ * a * xB) * (1 - κ * a * xP)))
        + (YA - YP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
          * ((YB - YP) * ((1 - κ * a * xB) * (1 - κ * a * xP)))
        + κ * ((XP * YA - YP * XA) * ((1 - κ * a * xP) * (1 - κ * a * xA)))
          * ((XP * YB - YP * XB) * ((1 - κ * a * xP) * (1 - κ * a * xB))) := by ring
  rw [e, e1, e2, e3, e4, e5, e6]
  linear_combination
    ((yA * (1 - κ * a * xP) - yP * (1 - κ * a * xA))
        * (yB * (1 - κ * a * xP) - yP * (1 - κ * a * xB))
      + κ * ((xP + a) * yA - yP * (xA + a)) * ((xP + a) * yB - yP * (xB + a))
      - (w ^ 2 + 1 + κ * a ^ 2) * ((xA - xP) * (xB - xP) + (yA - yP) * (yB - yP)
        + κ * (xP * yA - yP * xA) * (xP * yB - yP * xB))) * hw

/-- **The motion along the first axis keeps the inner product at a pair**, up to a factor. The
factor is the same for every direction from the pair once each direction is divided by its
own denominator, and so the motion keeps angles: see `shift_kleinAngle`. -/
theorem shift_kleinInner {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) {P A B : K × K}
    (hP : 1 - κ * a * P.1 ≠ 0) (hA : 1 - κ * a * A.1 ≠ 0) (hB : 1 - κ * a * B.1 ≠ 0) :
    kleinInner κ (shift κ a w P) (shift κ a w A) (shift κ a w B)
      = w ^ 4 * kleinInner κ P A B
          / ((1 - κ * a * P.1) ^ 2 * (1 - κ * a * A.1) * (1 - κ * a * B.1)) := by
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hP) hA) hB)]
  have h := kleinInner_aux κ a w P.1 P.2 A.1 A.2 B.1 B.2 _ _ _ _ _ _ hw
    (div_mul_cancel₀ (P.1 + a) hP) (div_mul_cancel₀ (w * P.2) hP)
    (div_mul_cancel₀ (A.1 + a) hA) (div_mul_cancel₀ (w * A.2) hA)
    (div_mul_cancel₀ (B.1 + a) hB) (div_mul_cancel₀ (w * B.2) hB)
  simp only [kleinInner, shift, cross]
  linear_combination h

/-- **Turning keeps the inner product at a pair.** -/
theorem rot_kleinInner {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (P A B : K × K) :
    kleinInner κ (rot c s P) (rot c s A) (rot c s B) = kleinInner κ P A B := by
  simp only [kleinInner, rot, cross]
  linear_combination ((A.1 - P.1) * (B.1 - P.1) + (A.2 - P.2) * (B.2 - P.2)
    + κ * (P.1 * A.2 - P.2 * A.1) * (P.1 * B.2 - P.2 * B.1) * (c ^ 2 + s ^ 2 + 1)) * h

end InnerAlgebra

section InnerOrder

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **At a point of the plane the inner product is positive** on every direction that is not
zero. So it is an inner product, under any bound. -/
theorem kleinInner_self_pos {κ : K} {P A : K × K} (hP : P ∈ plane κ) (hA : A ≠ P) :
    0 < kleinInner κ P A A := by
  have hv : (A.1 - P.1, A.2 - P.2) ≠ ((0 : K), (0 : K)) := by
    intro h
    apply hA
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [] at h1 h2
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  have hd : 0 < (A.1 - P.1) ^ 2 + (A.2 - P.2) ^ 2 := sq_add_sq_pos hv
  rcases le_or_gt 0 κ with hκ | hκ
  · have e : kleinInner κ P A A = (A.1 - P.1) ^ 2 + (A.2 - P.2) ^ 2 + κ * cross P A ^ 2 := by
      simp only [kleinInner]
      ring
    rw [e]
    have h := mul_nonneg hκ (sq_nonneg (cross P A))
    linarith
  · have e : kleinInner κ P A A
        = ((A.1 - P.1) ^ 2 + (A.2 - P.2) ^ 2) * (1 + κ * (P.1 ^ 2 + P.2 ^ 2))
          + -κ * (P.1 * (A.1 - P.1) + P.2 * (A.2 - P.2)) ^ 2 := by
      simp only [kleinInner, cross]
      ring
    rw [e]
    have h1 := mul_pos hd (mem_plane.mp hP)
    have h2 := mul_nonneg (neg_nonneg.mpr hκ.le)
      (sq_nonneg (P.1 * (A.1 - P.1) + P.2 * (A.2 - P.2)))
    linarith

end InnerOrder

/-! ## Angles

With the real numbers for numbers, the inner product at a pair gives an angle, as the inner
product of Euclid gives the angle of Mathlib. -/

section Angles

open Real

/-- **The angle at a pair**, under the bound `κ`: the angle at `P` between the direction from
`P` to `A` and the direction from `P` to `B`. It is made from `kleinInner` as Mathlib makes the
angle of Euclid from the inner product. -/
noncomputable def kleinAngle (κ : ℝ) (P A B : ℝ × ℝ) : ℝ :=
  arccos (kleinInner κ P A B / (√(kleinInner κ P A A) * √(kleinInner κ P B B)))

/-- **With the bound 0 it is the angle of Euclid**, in Mathlib's sense. -/
theorem kleinAngle_zero_bound (P A B : ℝ × ℝ) :
    kleinAngle 0 P A B
      = InnerProductGeometry.angle (!₂[A.1 - P.1, A.2 - P.2] : EuclideanSpace ℝ (Fin 2))
          !₂[B.1 - P.1, B.2 - P.2] := by
  have hi : inner ℝ (!₂[A.1 - P.1, A.2 - P.2] : EuclideanSpace ℝ (Fin 2))
      !₂[B.1 - P.1, B.2 - P.2] = kleinInner 0 P A B := by
    rw [kleinInner_zero_bound]
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hn : ∀ X : ℝ × ℝ, ‖(!₂[X.1 - P.1, X.2 - P.2] : EuclideanSpace ℝ (Fin 2))‖
      = √(kleinInner 0 P X X) := by
    intro X
    rw [kleinInner_zero_bound]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, sq]
  rw [InnerProductGeometry.angle, hi, hn, hn]
  rfl

/-- **At `(0, 0)` it is the angle of Euclid, under any bound.** -/
theorem kleinAngle_centre (κ : ℝ) (A B : ℝ × ℝ) :
    kleinAngle κ (0, 0) A B
      = InnerProductGeometry.angle (!₂[A.1, A.2] : EuclideanSpace ℝ (Fin 2)) !₂[B.1, B.2] := by
  have h : kleinAngle κ (0, 0) A B = kleinAngle 0 (0, 0) A B := by
    simp only [kleinAngle, kleinInner_centre]
  rw [h, kleinAngle_zero_bound]
  simp

/-- The last step of the next theorem: an angle does not change when the inner products are
multiplied as a motion multiplies them. -/
theorem kleinAngle_aux {g g₁ g₂ m u v : ℝ} (hm : 0 < m) (huv : 0 < u * v) :
    arccos (m * u * v * g / (√(m * u ^ 2 * g₁) * √(m * v ^ 2 * g₂)))
      = arccos (g / (√g₁ * √g₂)) := by
  have hsq : √m * √m = m := mul_self_sqrt hm.le
  have habs : |u| * |v| = u * v := by rw [← abs_mul, abs_of_pos huv]
  have h1 : √(m * u ^ 2 * g₁) = √m * |u| * √g₁ := by
    rw [sqrt_mul (by positivity : (0 : ℝ) ≤ m * u ^ 2), sqrt_mul hm.le, sqrt_sq_eq_abs]
  have h2 : √(m * v ^ 2 * g₂) = √m * |v| * √g₂ := by
    rw [sqrt_mul (by positivity : (0 : ℝ) ≤ m * v ^ 2), sqrt_mul hm.le, sqrt_sq_eq_abs]
  have hden : √(m * u ^ 2 * g₁) * √(m * v ^ 2 * g₂) = m * u * v * (√g₁ * √g₂) := by
    rw [h1, h2]
    linear_combination (|u| * |v| * √g₁ * √g₂) * hsq + (m * √g₁ * √g₂) * habs
  have hmuv : m * u * v ≠ 0 := by
    rw [mul_assoc]
    exact (mul_pos hm huv).ne'
  rw [hden, mul_div_mul_left _ _ hmuv]

/-- **Theorem H13. The motion along the first axis keeps angles.** For three points of the
plane, the angle at the first between the two others is the same after the motion. -/
theorem shift_kleinAngle {κ a w : ℝ} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {P A B : ℝ × ℝ} (hP : P ∈ plane κ) (hA : A ∈ plane κ) (hB : B ∈ plane κ) :
    kleinAngle κ (shift κ a w P) (shift κ a w A) (shift κ a w B) = kleinAngle κ P A B := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  have hDP := shift_den_pos hκ ha hP
  have hDA := shift_den_pos hκ ha hA
  have hDB := shift_den_pos hκ ha hB
  have hw4 : 0 < w ^ 4 := by
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring]
    exact pow_pos hw2 2
  have hm : 0 < w ^ 4 / (1 - κ * a * P.1) ^ 2 := div_pos hw4 (pow_pos hDP 2)
  have huv : 0 < 1 / (1 - κ * a * A.1) * (1 / (1 - κ * a * B.1)) :=
    mul_pos (one_div_pos.mpr hDA) (one_div_pos.mpr hDB)
  have e1 : kleinInner κ (shift κ a w P) (shift κ a w A) (shift κ a w B)
      = w ^ 4 / (1 - κ * a * P.1) ^ 2 * (1 / (1 - κ * a * A.1)) * (1 / (1 - κ * a * B.1))
        * kleinInner κ P A B := by
    rw [shift_kleinInner hw hDP.ne' hDA.ne' hDB.ne']
    field_simp
  have e2 : kleinInner κ (shift κ a w P) (shift κ a w A) (shift κ a w A)
      = w ^ 4 / (1 - κ * a * P.1) ^ 2 * (1 / (1 - κ * a * A.1)) ^ 2 * kleinInner κ P A A := by
    rw [shift_kleinInner hw hDP.ne' hDA.ne' hDA.ne']
    field_simp
  have e3 : kleinInner κ (shift κ a w P) (shift κ a w B) (shift κ a w B)
      = w ^ 4 / (1 - κ * a * P.1) ^ 2 * (1 / (1 - κ * a * B.1)) ^ 2 * kleinInner κ P B B := by
    rw [shift_kleinInner hw hDP.ne' hDB.ne' hDB.ne']
    field_simp
  unfold kleinAngle
  rw [e1, e2, e3]
  exact kleinAngle_aux hm huv

/-- **Theorem H13. Turning keeps angles.** -/
theorem rot_kleinAngle {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (κ : ℝ) (P A B : ℝ × ℝ) :
    kleinAngle κ (rot c s P) (rot c s A) (rot c s B) = kleinAngle κ P A B := by
  simp only [kleinAngle, rot_kleinInner h]

/-- **Theorem H15. The motions take every point of the plane to `(0, 0)`.** A turn takes the
point to the number `r` of the first axis, where `r` is its distance from `(0, 0)` in Euclid's
sense, and the motion along the first axis with `a = -r` takes it on to `(0, 0)`. -/
theorem exists_motion_to_centre {κ : ℝ} {P : ℝ × ℝ} (hP : P ∈ plane κ) :
    ∃ c s a w : ℝ, c ^ 2 + s ^ 2 = 1 ∧ w ^ 2 = 1 + κ * a ^ 2 ∧ 0 < w ∧
      shift κ a w (rot c s P) = (0, 0) := by
  by_cases h0 : P.1 ^ 2 + P.2 ^ 2 = 0
  · have h1 : P.1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg P.2])
    have h2 : P.2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg P.1])
    refine ⟨1, 0, 0, 1, by norm_num, by ring, one_pos, ?_⟩
    apply Prod.ext <;> simp [shift, rot, h1, h2]
  · have hpos : 0 < P.1 ^ 2 + P.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    obtain ⟨r, hr0, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = P.1 ^ 2 + P.2 ^ 2 :=
      ⟨√(P.1 ^ 2 + P.2 ^ 2), sqrt_pos.mpr hpos, sq_sqrt hpos.le⟩
    have hw : 0 < 1 + κ * r ^ 2 := by
      rw [hr2]
      exact mem_plane.mp hP
    have hrot : rot (P.1 / r) (-P.2 / r) P = (r, 0) := by
      apply Prod.ext
      · simp only [rot]
        field_simp
        linear_combination -hr2
      · simp only [rot]
        ring
    refine ⟨P.1 / r, -P.2 / r, -r, √(1 + κ * r ^ 2), ?_, ?_, sqrt_pos.mpr hw, ?_⟩
    · field_simp
      linear_combination -hr2
    · rw [sq_sqrt hw.le]
      ring
    · rw [hrot]
      apply Prod.ext <;> simp [shift]

/-- **`kleinAngle` is the only angle that the motions keep and that is the angle of Euclid at
`(0, 0)`.** Let `θ` give a number to three points of the plane. If turning and the motion along
the first axis keep `θ`, and at `(0, 0)` it is the angle of Euclid in Mathlib's sense, then it
is `kleinAngle`. The proof moves the vertex to `(0, 0)` with Theorem H15. -/
theorem kleinAngle_unique {κ : ℝ} (hκ : κ ≤ 0) (θ : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ → ℝ)
    (hshift : ∀ a w : ℝ, w ^ 2 = 1 + κ * a ^ 2 → 0 < w → ∀ P A B : ℝ × ℝ,
      P ∈ plane κ → A ∈ plane κ → B ∈ plane κ →
        θ (shift κ a w P) (shift κ a w A) (shift κ a w B) = θ P A B)
    (hrot : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → ∀ P A B : ℝ × ℝ,
      P ∈ plane κ → A ∈ plane κ → B ∈ plane κ →
        θ (rot c s P) (rot c s A) (rot c s B) = θ P A B)
    (hcentre : ∀ A B : ℝ × ℝ, A ∈ plane κ → B ∈ plane κ →
      θ (0, 0) A B
        = InnerProductGeometry.angle (!₂[A.1, A.2] : EuclideanSpace ℝ (Fin 2)) !₂[B.1, B.2])
    {P A B : ℝ × ℝ} (hP : P ∈ plane κ) (hA : A ∈ plane κ) (hB : B ∈ plane κ) :
    θ P A B = kleinAngle κ P A B := by
  obtain ⟨c, s, a, w, hcs, hw, hw0, hPc⟩ := exists_motion_to_centre hP
  have hr : ∀ X : ℝ × ℝ, X ∈ plane κ → rot c s X ∈ plane κ :=
    fun X hX => (rot_mem_plane hcs).mpr hX
  have hm : ∀ X : ℝ × ℝ, X ∈ plane κ → shift κ a w (rot c s X) ∈ plane κ :=
    fun X hX => shift_mem_plane hκ hw hw0.ne' (hr X hX)
  calc θ P A B = θ (rot c s P) (rot c s A) (rot c s B) := (hrot c s hcs P A B hP hA hB).symm
    _ = θ (shift κ a w (rot c s P)) (shift κ a w (rot c s A)) (shift κ a w (rot c s B)) :=
      (hshift a w hw hw0 _ _ _ (hr P hP) (hr A hA) (hr B hB)).symm
    _ = θ (0, 0) (shift κ a w (rot c s A)) (shift κ a w (rot c s B)) := by rw [hPc]
    _ = kleinAngle κ (0, 0) (shift κ a w (rot c s A)) (shift κ a w (rot c s B)) := by
      rw [hcentre _ _ (hm A hA) (hm B hB), kleinAngle_centre]
    _ = kleinAngle κ (shift κ a w (rot c s P)) (shift κ a w (rot c s A))
          (shift κ a w (rot c s B)) := by rw [hPc]
    _ = kleinAngle κ (rot c s P) (rot c s A) (rot c s B) :=
      shift_kleinAngle hκ hw hw0.ne' (hr P hP) (hr A hA) (hr B hB)
    _ = kleinAngle κ P A B := rot_kleinAngle hcs κ P A B

end Angles

end HyperbolicPlane
