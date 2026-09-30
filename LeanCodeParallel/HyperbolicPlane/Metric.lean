/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import LeanCodeParallel.HyperbolicPlane.Angles
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Klein's metric

`kleinMetric` is the metric of Klein's model, as the books write it. The two motions keep it:
moved by the derivative of a motion, in Mathlib's sense, two directions have the metric they had
before (Theorem H16). `kleinAngle` is the angle of this metric.

## Contents

* Theorem H16, Klein's metric, and the motions keep it: `kleinMetric`, `kleinMetric_zero_bound`,
  `kleinMetric_sub`, `kleinMetric_pos`, `shiftDeriv`, `shift_kleinMetric`, `rot_kleinMetric`,
  `shift_differentiableAt`, `shift_hasLineDerivAt`, `fderiv_shift`, `fderiv_rot`,
  `shift_kleinMetric_fderiv`, `rot_kleinMetric_fderiv`, `kleinAngle_eq_metric`
* a step of the proofs: `kleinMetric_aux`
-/

namespace HyperbolicPlane

open Pairs

/-! ## The metric -/

section MetricAlgebra

variable {K : Type*} [Field K]

/-- **Klein's metric**, under the bound `κ`: at the pair `P`, of the directions `u` and `v`.
It is the metric of Klein's model as the books write it: under the bound `-1`,
`ds² = (|dx|² (1 - |x|²) + (x · dx)²) / (1 - |x|²)²`. With the bound 0 it is the inner product
of Euclid. -/
def kleinMetric (κ : K) (P u v : K × K) : K :=
  (u.1 * v.1 + u.2 * v.2 + κ * cross P u * cross P v) / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2

/-- With the bound 0 it is the inner product of Euclid, at every pair. -/
theorem kleinMetric_zero_bound (P u v : K × K) : kleinMetric 0 P u v = u.1 * v.1 + u.2 * v.2 := by
  simp [kleinMetric]

/-- On the directions from `P` to `A` and from `P` to `B`, it is the inner product at `P`,
divided by the square of the bound at `P`. -/
theorem kleinMetric_sub (κ : K) (P A B : K × K) :
    kleinMetric κ P (A - P) (B - P)
      = kleinInner κ P A B / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 := by
  simp only [kleinMetric, kleinInner, cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The derivative of the motion along the first axis** at the pair `P`, on the direction
`u`. That it is the derivative in Mathlib's sense is `fderiv_shift`. -/
def shiftDeriv (κ a w : K) (P u : K × K) : K × K :=
  ((1 + κ * a ^ 2) * u.1 / (1 - κ * a * P.1) ^ 2,
    w * (κ * a * P.2 * u.1 + (1 - κ * a * P.1) * u.2) / (1 - κ * a * P.1) ^ 2)

/-- The algebra of the next theorem, with the divisions taken out. -/
theorem kleinMetric_aux (κ a w x y u1 u2 v1 v2 : K) (hw : w ^ 2 = 1 + κ * a ^ 2) :
    (1 + κ * a ^ 2) ^ 2 * (u1 * v1)
        + w ^ 2 * ((κ * a * y * u1 + (1 - κ * a * x) * u2)
          * (κ * a * y * v1 + (1 - κ * a * x) * v2))
        + κ * w ^ 2 * (((x + a) * u2 - y * u1) * ((x + a) * v2 - y * v1))
      = w ^ 4 * (u1 * v1 + u2 * v2 + κ * (x * u2 - y * u1) * (x * v2 - y * v1)) := by
  rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hw]
  ring

/-- **The motion along the first axis keeps Klein's metric.** At the pair to which it moves
`P`, the metric of the two directions to which its derivative moves `u` and `v` is the metric
of `u` and `v` at `P`. -/
theorem shift_kleinMetric {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) {P : K × K}
    (hD : 1 - κ * a * P.1 ≠ 0) (hP : 1 + κ * (P.1 ^ 2 + P.2 ^ 2) ≠ 0) (u v : K × K) :
    kleinMetric κ (shift κ a w P) (shiftDeriv κ a w P u) (shiftDeriv κ a w P v)
      = kleinMetric κ P u v := by
  have h1 : ((shiftDeriv κ a w P u).1 * (shiftDeriv κ a w P v).1
        + (shiftDeriv κ a w P u).2 * (shiftDeriv κ a w P v).2
        + κ * cross (shift κ a w P) (shiftDeriv κ a w P u)
          * cross (shift κ a w P) (shiftDeriv κ a w P v)) * (1 - κ * a * P.1) ^ 4
      = (1 + κ * a ^ 2) ^ 2 * (u.1 * v.1)
        + w ^ 2 * ((κ * a * P.2 * u.1 + (1 - κ * a * P.1) * u.2)
          * (κ * a * P.2 * v.1 + (1 - κ * a * P.1) * v.2))
        + κ * w ^ 2 * (((P.1 + a) * u.2 - P.2 * u.1) * ((P.1 + a) * v.2 - P.2 * v.1)) := by
    simp only [shift, shiftDeriv, cross]
    field_simp
    ring
  have h2 : (shiftDeriv κ a w P u).1 * (shiftDeriv κ a w P v).1
        + (shiftDeriv κ a w P u).2 * (shiftDeriv κ a w P v).2
        + κ * cross (shift κ a w P) (shiftDeriv κ a w P u)
          * cross (shift κ a w P) (shiftDeriv κ a w P v)
      = w ^ 4 * (u.1 * v.1 + u.2 * v.2 + κ * cross P u * cross P v) / (1 - κ * a * P.1) ^ 4 := by
    rw [eq_div_iff (pow_ne_zero 4 hD), h1, kleinMetric_aux κ a w P.1 P.2 u.1 u.2 v.1 v.2 hw]
    simp only [cross]
  unfold kleinMetric
  rw [h2, shift_bound hw hD]
  field_simp

/-- **Turning keeps Klein's metric.** Turning is its own derivative. -/
theorem rot_kleinMetric {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (P u v : K × K) :
    kleinMetric κ (rot c s P) (rot c s u) (rot c s v) = kleinMetric κ P u v := by
  unfold kleinMetric
  rw [rot_bound h]
  congr 1
  simp only [rot, cross]
  linear_combination (u.1 * v.1 + u.2 * v.2
    + κ * (P.1 * u.2 - P.2 * u.1) * (P.1 * v.2 - P.2 * v.1) * (c ^ 2 + s ^ 2 + 1)) * h

end MetricAlgebra

section MetricOrder

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **At a point of the plane Klein's metric is positive** on every direction that is not
zero. -/
theorem kleinMetric_pos {κ : K} {P u : K × K} (hP : P ∈ plane κ) (hu : u ≠ 0) :
    0 < kleinMetric κ P u u := by
  have hA : P + u ≠ P := fun h => hu (add_eq_left.mp h)
  have e : kleinMetric κ P u u = kleinMetric κ P (P + u - P) (P + u - P) := by
    rw [add_sub_cancel_left]
  rw [e, kleinMetric_sub]
  exact div_pos (kleinInner_self_pos hP hA) (pow_pos (mem_plane.mp hP) 2)

end MetricOrder

/-! ## The motions keep Klein's metric

With the real numbers for numbers, the derivatives of the two motions are derivatives in
Mathlib's sense, and the motions keep Klein's metric. -/

section Metric

open Real

/-- The motion along the first axis has a derivative wherever it is defined. -/
theorem shift_differentiableAt {κ a w : ℝ} {P : ℝ × ℝ} (hD : 1 - κ * a * P.1 ≠ 0) :
    DifferentiableAt ℝ (shift κ a w) P := by
  unfold shift
  simp only [div_eq_mul_inv]
  fun_prop (disch := exact hD)

/-- Along the direction `u` from `P`, the motion along the first axis has the derivative
`shiftDeriv`. -/
theorem shift_hasLineDerivAt {κ a w : ℝ} {P : ℝ × ℝ} (hD : 1 - κ * a * P.1 ≠ 0) (u : ℝ × ℝ) :
    HasLineDerivAt ℝ (shift κ a w) (shiftDeriv κ a w P u) P u := by
  have e : (fun t : ℝ => shift κ a w (P + t • u)) = fun t : ℝ =>
      ((P.1 + t * u.1 + a) / (1 - κ * a * (P.1 + t * u.1)),
        w * (P.2 + t * u.2) / (1 - κ * a * (P.1 + t * u.1))) := by
    funext t
    simp [shift]
  have hx : HasDerivAt (fun t : ℝ => P.1 + t * u.1) u.1 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.1).const_add P.1
  have hy : HasDerivAt (fun t : ℝ => P.2 + t * u.2) u.2 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.2).const_add P.2
  have hd : HasDerivAt (fun t : ℝ => 1 - κ * a * (P.1 + t * u.1)) (-(κ * a * u.1)) 0 :=
    (hx.const_mul (κ * a)).const_sub 1
  have hD0 : 1 - κ * a * (P.1 + 0 * u.1) ≠ 0 := by simpa using hD
  have h := ((hx.add_const a).div hd hD0).prodMk ((hy.const_mul w).div hd hD0)
  unfold HasLineDerivAt
  rw [e]
  convert h using 1
  simp only [shiftDeriv, zero_mul, add_zero]
  apply Prod.ext
  · field_simp
    ring
  · field_simp
    ring

/-- **`shiftDeriv` is the derivative of the motion along the first axis**, in Mathlib's
sense. -/
theorem fderiv_shift {κ a w : ℝ} {P : ℝ × ℝ} (hD : 1 - κ * a * P.1 ≠ 0) (u : ℝ × ℝ) :
    fderiv ℝ (shift κ a w) P u = shiftDeriv κ a w P u := by
  rw [← (shift_differentiableAt hD).lineDeriv_eq_fderiv]
  exact (shift_hasLineDerivAt hD u).lineDeriv

/-- **Turning is its own derivative**, in Mathlib's sense. -/
theorem fderiv_rot (c s : ℝ) (P u : ℝ × ℝ) : fderiv ℝ (rot c s) P u = rot c s u := by
  have hdiff : DifferentiableAt ℝ (rot c s) P := by
    unfold rot
    fun_prop
  have e : (fun t : ℝ => rot c s (P + t • u)) = fun t : ℝ =>
      (c * (P.1 + t * u.1) - s * (P.2 + t * u.2), s * (P.1 + t * u.1) + c * (P.2 + t * u.2)) := by
    funext t
    simp [rot]
  have hx : HasDerivAt (fun t : ℝ => P.1 + t * u.1) u.1 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.1).const_add P.1
  have hy : HasDerivAt (fun t : ℝ => P.2 + t * u.2) u.2 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const u.2).const_add P.2
  have h : HasLineDerivAt ℝ (rot c s) (rot c s u) P u := by
    unfold HasLineDerivAt
    rw [e]
    exact ((hx.const_mul c).sub (hy.const_mul s)).prodMk ((hx.const_mul s).add (hy.const_mul c))
  rw [← hdiff.lineDeriv_eq_fderiv]
  exact h.lineDeriv

/-- **Theorem H16. The motion along the first axis keeps Klein's metric.** At every point of
the plane, the metric of two directions after the motion, moved by the derivative of the
motion in Mathlib's sense, is their metric before it. -/
theorem shift_kleinMetric_fderiv {κ a w : ℝ} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2)
    (hw0 : w ≠ 0) {P : ℝ × ℝ} (hP : P ∈ plane κ) (u v : ℝ × ℝ) :
    kleinMetric κ (shift κ a w P) (fderiv ℝ (shift κ a w) P u) (fderiv ℝ (shift κ a w) P v)
      = kleinMetric κ P u v := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have hD := (shift_den_pos hκ (hw ▸ hw2) hP).ne'
  rw [fderiv_shift hD, fderiv_shift hD]
  exact shift_kleinMetric hw hw0 hD (mem_plane.mp hP).ne' u v

/-- **Theorem H16. Turning keeps Klein's metric.** -/
theorem rot_kleinMetric_fderiv {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (κ : ℝ) (P u v : ℝ × ℝ) :
    kleinMetric κ (rot c s P) (fderiv ℝ (rot c s) P u) (fderiv ℝ (rot c s) P v)
      = kleinMetric κ P u v := by
  rw [fderiv_rot, fderiv_rot]
  exact rot_kleinMetric h κ P u v

/-- **`kleinAngle` is the angle of Klein's metric.** At a point of the plane, the angle
between the directions to `A` and to `B` is made from `kleinMetric` as Mathlib makes the angle
of Euclid from the inner product. -/
theorem kleinAngle_eq_metric {κ : ℝ} {P : ℝ × ℝ} (hP : P ∈ plane κ) (A B : ℝ × ℝ) :
    kleinAngle κ P A B = arccos (kleinMetric κ P (A - P) (B - P)
      / (√(kleinMetric κ P (A - P) (A - P)) * √(kleinMetric κ P (B - P) (B - P)))) := by
  have hm : 0 < 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 :=
    one_div_pos.mpr (pow_pos (mem_plane.mp hP) 2)
  have e1 : kleinMetric κ P (A - P) (B - P)
      = 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * 1 * 1 * kleinInner κ P A B := by
    rw [kleinMetric_sub]
    ring
  have e2 : kleinMetric κ P (A - P) (A - P)
      = 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * 1 ^ 2 * kleinInner κ P A A := by
    rw [kleinMetric_sub]
    ring
  have e3 : kleinMetric κ P (B - P) (B - P)
      = 1 / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * 1 ^ 2 * kleinInner κ P B B := by
    rw [kleinMetric_sub]
    ring
  rw [kleinAngle, e1, e2, e3, kleinAngle_aux hm (by norm_num : (0 : ℝ) < 1 * 1)]

end Metric

end HyperbolicPlane
