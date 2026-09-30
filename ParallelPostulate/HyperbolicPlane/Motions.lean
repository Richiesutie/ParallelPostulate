/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import ParallelPostulate.HyperbolicPlane.Plane

/-!
# Steps and motions

What becomes of adding under a bound: the step `step κ t u = (t + u) / (1 - κ t u)`, the motion
along the first axis `shift`, turning `rot`, and `apart`, a number that both motions keep.

## Contents

* Proposition H8, steps: `step`, `step_zero_bound`, `step_comm`, `step_zero_right`, `step_neg`,
  `within_zero`, `within_neg`, `step_den_pos`, `step_within`, `step_assoc`, `step_bound`,
  `step_edge`, `step_edge_self`
* Theorem H9, the motion along the first axis: `shift`, `shift_zero_bound`, `shift_centre`,
  `shift_axis`, `shift_den_pos`, `shift_bound`, `shift_mem_plane`, `shift_shift_neg`,
  `shift_neg_shift`, `shift_bijOn`, `shift_cross`, `shift_isLine`, `shift_keeps_left`,
  `shift_apart`, `shift_apart_plane`
* Theorem H9, turning: `rot`, `rot_rot_neg`, `rot_bound`, `rot_mem_plane`, `rot_bijOn`, `rot_pt`,
  `rot_isLine`, `rot_cross`, `rot_apart`
* Theorem H9, how far apart: `apart`, `apart_zero_bound`, `apart_self`, `apart_comm`,
  `apart_centre`, `apart_pos`
* the algebra of the motions, with the divisions taken out: `cross_aux`, `apart_aux`, `apart_aux'`
-/

namespace HyperbolicPlane

open Pairs

/-! ## What becomes of adding: steps and motions -/

section StepsAlgebra

variable {K : Type*} [Field K]

/-- **The step.** Under the bound `κ`, the number `t` and then the number `u`, along a
dimension through `(0, 0)`. -/
def step (κ t u : K) : K := (t + u) / (1 - κ * t * u)

/-- With the bound 0 a step is a sum. -/
theorem step_zero_bound (t u : K) : step 0 t u = t + u := by
  simp [step]

theorem step_comm (κ t u : K) : step κ t u = step κ u t := by
  simp only [step]
  rw [add_comm t u, mul_assoc κ t u, mul_comm t u, ← mul_assoc]

theorem step_zero_right (κ t : K) : step κ t 0 = t := by
  simp [step]

theorem step_neg (κ t : K) : step κ t (-t) = 0 := by
  simp [step]

/-- The bound at a step. -/
theorem step_bound {κ t u : K} (h : 1 - κ * t * u ≠ 0) :
    1 + κ * step κ t u ^ 2 = (1 + κ * t ^ 2) * (1 + κ * u ^ 2) / (1 - κ * t * u) ^ 2 := by
  have hX : step κ t u * (1 - κ * t * u) = t + u := div_mul_cancel₀ _ h
  rw [eq_div_iff (pow_ne_zero 2 h)]
  linear_combination κ * (step κ t u * (1 - κ * t * u) + (t + u)) * hX

/-- **A number on the edge swallows every step.** -/
theorem step_edge {κ e t : K} (he : 1 + κ * e ^ 2 = 0) (h : 1 - κ * e * t ≠ 0) :
    step κ e t = e := by
  simp only [step]
  rw [div_eq_iff h]
  linear_combination t * he

/-- **The motion along the first axis** that takes `(0, 0)` to the number `a` of that axis.
Here `w` is a number with `w² = 1 + κ a²`. -/
def shift (κ a w : K) (p : K × K) : K × K :=
  ((p.1 + a) / (1 - κ * a * p.1), w * p.2 / (1 - κ * a * p.1))

/-- With the bound 0 the motion is adding. -/
theorem shift_zero_bound (a : K) (p : K × K) : shift 0 a 1 p = (p.1 + a, p.2) := by
  simp [shift]

theorem shift_centre (κ a w : K) : shift κ a w (0, 0) = (a, 0) := by
  simp [shift]

/-- On the first axis the motion is the step. -/
theorem shift_axis (κ a w t : K) : shift κ a w (t, 0) = (step κ t a, 0) := by
  simp only [shift, step, mul_zero, zero_div]
  rw [mul_assoc κ a t, mul_comm a t, ← mul_assoc]

/-- The bound at the pair to which a pair is moved. -/
theorem shift_bound {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) {p : K × K}
    (hD : 1 - κ * a * p.1 ≠ 0) :
    1 + κ * ((shift κ a w p).1 ^ 2 + (shift κ a w p).2 ^ 2)
      = w ^ 2 * (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) / (1 - κ * a * p.1) ^ 2 := by
  have hX : (p.1 + a) / (1 - κ * a * p.1) * (1 - κ * a * p.1) = p.1 + a :=
    div_mul_cancel₀ _ hD
  have hY : w * p.2 / (1 - κ * a * p.1) * (1 - κ * a * p.1) = w * p.2 :=
    div_mul_cancel₀ _ hD
  rw [eq_div_iff (pow_ne_zero 2 hD)]
  simp only [shift]
  linear_combination
    κ * ((p.1 + a) / (1 - κ * a * p.1) * (1 - κ * a * p.1) + (p.1 + a)) * hX
    + κ * (w * p.2 / (1 - κ * a * p.1) * (1 - κ * a * p.1) + w * p.2) * hY
    - (1 + κ * p.1 ^ 2) * hw

/-- The motion back. -/
theorem shift_shift_neg {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) {p : K × K}
    (hD : 1 - κ * a * p.1 ≠ 0) : shift κ (-a) w (shift κ a w p) = p := by
  have hX : (p.1 + a) / (1 - κ * a * p.1) * (1 - κ * a * p.1) = p.1 + a :=
    div_mul_cancel₀ _ hD
  have hY : w * p.2 / (1 - κ * a * p.1) * (1 - κ * a * p.1) = w * p.2 :=
    div_mul_cancel₀ _ hD
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw0
  have hDD : (1 - κ * -a * ((p.1 + a) / (1 - κ * a * p.1))) * (1 - κ * a * p.1) = w ^ 2 := by
    linear_combination κ * a * hX - hw
  have hD' : 1 - κ * -a * ((p.1 + a) / (1 - κ * a * p.1)) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hDD
    exact hw2 hDD.symm
  apply Prod.ext
  · simp only [shift]
    rw [div_eq_iff hD']
    apply mul_right_cancel₀ hD
    linear_combination hX - p.1 * hDD - p.1 * hw
  · simp only [shift]
    rw [div_eq_iff hD']
    apply mul_right_cancel₀ hD
    linear_combination w * hY - p.2 * hDD

/-- The algebra of the next theorem, with the divisions taken out. -/
theorem cross_aux (κ a w xA yA xB yB xC yC XA YA XB YB XC YC : K)
    (hXA : XA * (1 - κ * a * xA) = xA + a) (hYA : YA * (1 - κ * a * xA) = w * yA)
    (hXB : XB * (1 - κ * a * xB) = xB + a) (hYB : YB * (1 - κ * a * xB) = w * yB)
    (hXC : XC * (1 - κ * a * xC) = xC + a) (hYC : YC * (1 - κ * a * xC) = w * yC) :
    ((XB - XA) * (YC - YA) - (YB - YA) * (XC - XA))
        * ((1 - κ * a * xA) * (1 - κ * a * xB) * (1 - κ * a * xC))
      = w * (1 + κ * a ^ 2) * ((xB - xA) * (yC - yA) - (yB - yA) * (xC - xA)) := by
  linear_combination
    ((1 - κ * a * xA) * (YC * (1 - κ * a * xC))
      - (1 - κ * a * xC) * (YA * (1 - κ * a * xA))) * hXB
    + (-(1 - κ * a * xB) * (YC * (1 - κ * a * xC))
      + (1 - κ * a * xC) * (YB * (1 - κ * a * xB))) * hXA
    + (-(1 - κ * a * xA) * (YB * (1 - κ * a * xB))
      + (1 - κ * a * xB) * (YA * (1 - κ * a * xA))) * hXC
    + ((1 - κ * a * xA) * (xB + a) - (1 - κ * a * xB) * (xA + a)) * hYC
    + (-(1 - κ * a * xC) * (xB + a) + (1 - κ * a * xB) * (xC + a)) * hYA
    + (-(1 - κ * a * xA) * (xC + a) + (1 - κ * a * xC) * (xA + a)) * hYB

/-- **A motion keeps three pairs of a dimension on a dimension.** If `w (1 + κ a²)` is not
zero, it keeps three pairs that are not on one dimension off it as well. -/
theorem shift_cross (κ a w : K) {A B C : K × K} (hA : 1 - κ * a * A.1 ≠ 0)
    (hB : 1 - κ * a * B.1 ≠ 0) (hC : 1 - κ * a * C.1 ≠ 0) :
    cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2)
      = w * (1 + κ * a ^ 2) * cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2)
          / ((1 - κ * a * A.1) * (1 - κ * a * B.1) * (1 - κ * a * C.1)) := by
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero hA hB) hC)]
  have h := cross_aux κ a w A.1 A.2 B.1 B.2 C.1 C.2 _ _ _ _ _ _
    (div_mul_cancel₀ (A.1 + a) hA) (div_mul_cancel₀ (w * A.2) hA)
    (div_mul_cancel₀ (B.1 + a) hB) (div_mul_cancel₀ (w * B.2) hB)
    (div_mul_cancel₀ (C.1 + a) hC) (div_mul_cancel₀ (w * C.2) hC)
  simp only [shift, cross]
  linear_combination h

/-- **How far apart two pairs are**, under the bound `κ`. -/
def apart (κ : K) (P Q : K × K) : K :=
  ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2)
    / ((1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * (1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)))

/-- With the bound 0 it is the square of Euclid's distance. -/
theorem apart_zero_bound (P Q : K × K) :
    apart 0 P Q = (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 := by
  simp [apart]

theorem apart_self (κ : K) (P : K × K) : apart κ P P = 0 := by
  have h : (P.1 - P.1) ^ 2 + (P.2 - P.2) ^ 2 + κ * (P.1 * P.2 - P.2 * P.1) ^ 2 = 0 := by ring
  simp only [apart, h, zero_div]

theorem apart_comm (κ : K) (P Q : K × K) : apart κ P Q = apart κ Q P := by
  have h : (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2
      = (Q.1 - P.1) ^ 2 + (Q.2 - P.2) ^ 2 + κ * (Q.1 * P.2 - Q.2 * P.1) ^ 2 := by ring
  simp only [apart]
  rw [h, mul_comm (1 + κ * (P.1 ^ 2 + P.2 ^ 2))]

/-- From `(0, 0)` to the number `t` of the first axis. -/
theorem apart_centre (κ t : K) : apart κ (0, 0) (t, 0) = t ^ 2 / (1 + κ * t ^ 2) := by
  simp [apart]

/-- The algebra of the next theorem, with the divisions taken out. -/
theorem apart_aux (κ a w xP yP xQ yQ XP YP XQ YQ : K) (hw : w ^ 2 = 1 + κ * a ^ 2)
    (hXP : XP * (1 - κ * a * xP) = xP + a) (hYP : YP * (1 - κ * a * xP) = w * yP)
    (hXQ : XQ * (1 - κ * a * xQ) = xQ + a) (hYQ : YQ * (1 - κ * a * xQ) = w * yQ) :
    ((XP - XQ) ^ 2 + (YP - YQ) ^ 2 + κ * (XP * YQ - YP * XQ) ^ 2)
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xQ) ^ 2)
      = w ^ 4 * ((xP - xQ) ^ 2 + (yP - yQ) ^ 2 + κ * (xP * yQ - yP * xQ) ^ 2) := by
  have e1 : (XP - XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ)) = w ^ 2 * (xP - xQ) := by
    linear_combination (1 - κ * a * xQ) * hXP - (1 - κ * a * xP) * hXQ - (xP - xQ) * hw
  have e2 : (YP - YQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))
      = w * ((yP - yQ) + κ * a * (xP * yQ - yP * xQ)) := by
    linear_combination (1 - κ * a * xQ) * hYP - (1 - κ * a * xP) * hYQ
  have e3 : (XP * YQ - YP * XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))
      = w * ((xP * yQ - yP * xQ) - a * (yP - yQ)) := by
    linear_combination (YQ * (1 - κ * a * xQ)) * hXP + (xP + a) * hYQ
      - (XQ * (1 - κ * a * xQ)) * hYP - (w * yP) * hXQ
  have e : ((XP - XQ) ^ 2 + (YP - YQ) ^ 2 + κ * (XP * YQ - YP * XQ) ^ 2)
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xQ) ^ 2)
      = ((XP - XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))) ^ 2
        + ((YP - YQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))) ^ 2
        + κ * ((XP * YQ - YP * XQ) * ((1 - κ * a * xP) * (1 - κ * a * xQ))) ^ 2 := by ring
  rw [e, e1, e2, e3]
  linear_combination (-(w ^ 2 * ((yP - yQ) ^ 2 + κ * (xP * yQ - yP * xQ) ^ 2))) * hw

/-- The last step of the next theorem. -/
theorem apart_aux' (N N' BP BQ VP VQ DP DQ w : K) (hw : w ≠ 0) (hDP : DP ≠ 0) (hDQ : DQ ≠ 0)
    (hBP : BP ≠ 0) (hBQ : BQ ≠ 0) (hN : N' * (DP ^ 2 * DQ ^ 2) = w ^ 4 * N)
    (hVP : VP * DP ^ 2 = w ^ 2 * BP) (hVQ : VQ * DQ ^ 2 = w ^ 2 * BQ) :
    N' / (VP * VQ) = N / (BP * BQ) := by
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hVP0 : VP ≠ 0 := by
    intro h
    rw [h, zero_mul] at hVP
    exact mul_ne_zero hw2 hBP hVP.symm
  have hVQ0 : VQ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hVQ
    exact mul_ne_zero hw2 hBQ hVQ.symm
  rw [div_eq_div_iff (mul_ne_zero hVP0 hVQ0) (mul_ne_zero hBP hBQ)]
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hDP) (pow_ne_zero 2 hDQ))
  linear_combination (BP * BQ) * hN - N * (VQ * DQ ^ 2) * hVP - N * (w ^ 2 * BP) * hVQ

/-- **The motion along the first axis keeps how far apart two pairs are.** -/
theorem shift_apart {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) {P Q : K × K}
    (hDP : 1 - κ * a * P.1 ≠ 0) (hDQ : 1 - κ * a * Q.1 ≠ 0)
    (hP : 1 + κ * (P.1 ^ 2 + P.2 ^ 2) ≠ 0) (hQ : 1 + κ * (Q.1 ^ 2 + Q.2 ^ 2) ≠ 0) :
    apart κ (shift κ a w P) (shift κ a w Q) = apart κ P Q := by
  have hN : (((shift κ a w P).1 - (shift κ a w Q).1) ^ 2
      + ((shift κ a w P).2 - (shift κ a w Q).2) ^ 2
      + κ * ((shift κ a w P).1 * (shift κ a w Q).2
        - (shift κ a w P).2 * (shift κ a w Q).1) ^ 2)
        * ((1 - κ * a * P.1) ^ 2 * (1 - κ * a * Q.1) ^ 2)
      = w ^ 4 * ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2) :=
    apart_aux κ a w P.1 P.2 Q.1 Q.2 _ _ _ _ hw
      (div_mul_cancel₀ (P.1 + a) hDP) (div_mul_cancel₀ (w * P.2) hDP)
      (div_mul_cancel₀ (Q.1 + a) hDQ) (div_mul_cancel₀ (w * Q.2) hDQ)
  unfold apart
  exact apart_aux' _ _ _ _ _ _ _ _ w hw0 hDP hDQ hP hQ hN
    ((eq_div_iff (pow_ne_zero 2 hDP)).mp (shift_bound hw hDP))
    ((eq_div_iff (pow_ne_zero 2 hDQ)).mp (shift_bound hw hDQ))

/-- **Turning about `(0, 0)`.** Here `c` and `s` are numbers with `c² + s² = 1`. -/
def rot (c s : K) (p : K × K) : K × K := (c * p.1 - s * p.2, s * p.1 + c * p.2)

/-- Turning back. -/
theorem rot_rot_neg {c s : K} (h : c ^ 2 + s ^ 2 = 1) (p : K × K) :
    rot c (-s) (rot c s p) = p := by
  apply Prod.ext
  · simp only [rot]
    linear_combination p.1 * h
  · simp only [rot]
    linear_combination p.2 * h

/-- Turning keeps the bound of a pair. -/
theorem rot_bound {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (p : K × K) :
    1 + κ * ((rot c s p).1 ^ 2 + (rot c s p).2 ^ 2) = 1 + κ * (p.1 ^ 2 + p.2 ^ 2) := by
  simp only [rot]
  linear_combination κ * (p.1 ^ 2 + p.2 ^ 2) * h

/-- **Turning keeps how far apart two pairs are.** -/
theorem rot_apart {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (P Q : K × K) :
    apart κ (rot c s P) (rot c s Q) = apart κ P Q := by
  have hN : ((rot c s P).1 - (rot c s Q).1) ^ 2 + ((rot c s P).2 - (rot c s Q).2) ^ 2
      + κ * ((rot c s P).1 * (rot c s Q).2 - (rot c s P).2 * (rot c s Q).1) ^ 2
      = (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2 := by
    simp only [rot]
    linear_combination ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2
      + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2 * (c ^ 2 + s ^ 2 + 1)) * h
  simp only [apart]
  rw [hN, rot_bound h, rot_bound h]

/-- **Turning keeps left and right**: it keeps the cross product. -/
theorem rot_cross {c s : K} (h : c ^ 2 + s ^ 2 = 1) (A B C : K × K) :
    cross ((rot c s B).1 - (rot c s A).1, (rot c s B).2 - (rot c s A).2)
        ((rot c s C).1 - (rot c s A).1, (rot c s C).2 - (rot c s A).2)
      = cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) := by
  simp only [rot, cross]
  linear_combination ((B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)) * h

/-- Turning takes the numbers of a dimension to the numbers of a dimension. -/
theorem rot_pt (c s : K) (M : Dim K) (t : K) :
    rot c s (M.pt t) = (Dim.mk (rot c s M.zero) (rot c s M.one)).pt t := by
  apply Prod.ext
  · simp only [rot, Dim.pt]
    ring
  · simp only [rot, Dim.pt]
    ring

end StepsAlgebra

section StepsOrder

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Under a bound that is not positive, two numbers within the bound have a step. -/
theorem step_den_pos {κ t u : K} (hκ : κ ≤ 0) (ht : 0 < 1 + κ * t ^ 2)
    (hu : 0 < 1 + κ * u ^ 2) : 0 < 1 - κ * t * u := by
  nlinarith [mul_nonneg (neg_nonneg.mpr hκ) (sq_nonneg (t + u))]

/-- **The step of two numbers within the bound is within the bound.** -/
theorem step_within {κ t u : K} (hκ : κ ≤ 0) (ht : 0 < 1 + κ * t ^ 2)
    (hu : 0 < 1 + κ * u ^ 2) : 0 < 1 + κ * step κ t u ^ 2 := by
  have h := step_den_pos hκ ht hu
  rw [step_bound h.ne']
  exact div_pos (mul_pos ht hu) (pow_pos h 2)

omit [IsStrictOrderedRing K] in
/-- The step back of a number within the bound is within the bound. -/
theorem within_neg {κ t : K} (ht : 0 < 1 + κ * t ^ 2) : 0 < 1 + κ * (-t) ^ 2 := by
  have h : 1 + κ * (-t) ^ 2 = 1 + κ * t ^ 2 := by ring
  rw [h]
  exact ht

/-- The zero is within the bound. -/
theorem within_zero (κ : K) : 0 < 1 + κ * (0 : K) ^ 2 := by
  have h : 1 + κ * (0 : K) ^ 2 = 1 := by ring
  rw [h]
  exact one_pos

/-- **Steps can be taken in any grouping.** -/
theorem step_assoc {κ t u v : K} (hκ : κ ≤ 0) (ht : 0 < 1 + κ * t ^ 2)
    (hu : 0 < 1 + κ * u ^ 2) (hv : 0 < 1 + κ * v ^ 2) :
    step κ (step κ t u) v = step κ t (step κ u v) := by
  have h1 := (step_den_pos hκ ht hu).ne'
  have h2 := (step_den_pos hκ hu hv).ne'
  have h3 := (step_den_pos hκ (step_within hκ ht hu) hv).ne'
  have h4 := (step_den_pos hκ ht (step_within hκ hu hv)).ne'
  have hX : step κ t u * (1 - κ * t * u) = t + u := div_mul_cancel₀ _ h1
  have hY : step κ u v * (1 - κ * u * v) = u + v := div_mul_cancel₀ _ h2
  have hL : step κ (step κ t u) v * (1 - κ * step κ t u * v) = step κ t u + v :=
    div_mul_cancel₀ _ h3
  have hR : step κ t (step κ u v) * (1 - κ * t * step κ u v) = t + step κ u v :=
    div_mul_cancel₀ _ h4
  have e3 : (1 - κ * step κ t u * v) * (1 - κ * t * u)
      = 1 - κ * (t * u + t * v + u * v) := by
    linear_combination -κ * v * hX
  have e4 : (1 - κ * t * step κ u v) * (1 - κ * u * v)
      = 1 - κ * (t * u + t * v + u * v) := by
    linear_combination -κ * t * hY
  have eL : step κ (step κ t u) v * (1 - κ * (t * u + t * v + u * v))
      = t + u + v - κ * t * u * v := by
    rw [← e3]
    linear_combination (1 - κ * t * u) * hL + hX
  have eR : step κ t (step κ u v) * (1 - κ * (t * u + t * v + u * v))
      = t + u + v - κ * t * u * v := by
    rw [← e4]
    linear_combination (1 - κ * u * v) * hR + hY
  have hE : 1 - κ * (t * u + t * v + u * v) ≠ 0 := by
    rw [← e3]
    exact mul_ne_zero h3 h1
  exact mul_right_cancel₀ hE (eL.trans eR.symm)

/-- **A number on the edge is its own double.** -/
theorem step_edge_self {κ e : K} (he : 1 + κ * e ^ 2 = 0) : step κ e e = e := by
  apply step_edge he
  have h : 1 - κ * e * e = 2 := by linear_combination -he
  rw [h]
  exact two_ne_zero

/-- **Two different points of the plane are apart.** -/
theorem apart_pos {κ : K} {P Q : K × K} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) (hPQ : P ≠ Q) :
    0 < apart κ P Q := by
  have hv : (P.1 - Q.1, P.2 - Q.2) ≠ ((0 : K), (0 : K)) := by
    intro h
    apply hPQ
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [] at h1 h2
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  have hd : 0 < (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 := sq_add_sq_pos hv
  apply div_pos _ (mul_pos (mem_plane.mp hP) (mem_plane.mp hQ))
  rcases le_or_gt 0 κ with hκ | hκ
  · have h := mul_nonneg hκ (sq_nonneg (P.1 * Q.2 - P.2 * Q.1))
    linarith
  · have e : (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 + κ * (P.1 * Q.2 - P.2 * Q.1) ^ 2
        = ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2) * (1 + κ * (P.1 ^ 2 + P.2 ^ 2))
          + -κ * (P.1 * (Q.1 - P.1) + P.2 * (Q.2 - P.2)) ^ 2 := by ring
    rw [e]
    have h1 := mul_pos hd (mem_plane.mp hP)
    have h2 := mul_nonneg (neg_nonneg.mpr hκ.le)
      (sq_nonneg (P.1 * (Q.1 - P.1) + P.2 * (Q.2 - P.2)))
    linarith

/-- Under a bound that is not positive, the motion is defined at every point of the plane. -/
theorem shift_den_pos {κ a : K} (hκ : κ ≤ 0) (ha : 0 < 1 + κ * a ^ 2) {p : K × K}
    (hp : p ∈ plane κ) : 0 < 1 - κ * a * p.1 := by
  have hx : 0 < 1 + κ * p.1 ^ 2 := by
    have h := mem_plane.mp hp
    nlinarith [mul_nonneg (neg_nonneg.mpr hκ) (sq_nonneg p.2)]
  exact step_den_pos hκ ha hx

/-- **The motion takes points of the plane to points of the plane.** -/
theorem shift_mem_plane {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {p : K × K} (hp : p ∈ plane κ) : shift κ a w p ∈ plane κ := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have hD := shift_den_pos hκ (hw ▸ hw2) hp
  rw [mem_plane, shift_bound hw hD.ne']
  exact div_pos (mul_pos hw2 (mem_plane.mp hp)) (pow_pos hD 2)

/-- The motion back, at a point of the plane. -/
theorem shift_neg_shift {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {p : K × K} (hp : p ∈ plane κ) : shift κ (-a) w (shift κ a w p) = p := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  exact shift_shift_neg hw hw0 (shift_den_pos hκ (hw ▸ hw2) hp).ne'

/-- **The motion takes the plane onto itself, and different points to different points.** -/
theorem shift_bijOn {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0) :
    Set.BijOn (shift κ a w) (plane κ) (plane κ) := by
  have hw' : w ^ 2 = 1 + κ * (-a) ^ 2 := by
    rw [hw]
    ring
  refine ⟨fun p hp => shift_mem_plane hκ hw hw0 hp, ?_, ?_⟩
  · intro p hp q hq h
    have h' := congrArg (shift κ (-a) w) h
    rwa [shift_neg_shift hκ hw hw0 hp, shift_neg_shift hκ hw hw0 hq] at h'
  · intro q hq
    refine ⟨shift κ (-a) w q, shift_mem_plane hκ hw' hw0 hq, ?_⟩
    have h := shift_neg_shift hκ hw' hw0 hq
    rwa [neg_neg] at h

/-- **With `w` positive the motion keeps left and right.** For three points of the plane, the
cross product is positive, negative or zero after the motion as it was before. -/
theorem shift_keeps_left {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : 0 < w)
    {A B C : K × K} (hA : A ∈ plane κ) (hB : B ∈ plane κ) (hC : C ∈ plane κ) :
    (0 < cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) ↔
      0 < cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2)) ∧
    (cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) < 0 ↔
      cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) < 0) ∧
    (cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2) = 0 ↔
      cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2) = 0) := by
  have ha : 0 < 1 + κ * a ^ 2 := by
    rw [← hw]
    exact pow_pos hw0 2
  have hDA := shift_den_pos hκ ha hA
  have hDB := shift_den_pos hκ ha hB
  have hDC := shift_den_pos hκ ha hC
  have hden : 0 < (1 - κ * a * A.1) * (1 - κ * a * B.1) * (1 - κ * a * C.1) :=
    mul_pos (mul_pos hDA hDB) hDC
  have hfac : 0 < w * (1 + κ * a ^ 2) := mul_pos hw0 ha
  have hr : 0 < w * (1 + κ * a ^ 2)
      / ((1 - κ * a * A.1) * (1 - κ * a * B.1) * (1 - κ * a * C.1)) := div_pos hfac hden
  rw [shift_cross κ a w hDA.ne' hDB.ne' hDC.ne', mul_div_right_comm]
  refine ⟨mul_pos_iff_of_pos_left hr, ?_, ?_⟩
  · constructor
    · intro h
      by_contra hcon
      exact absurd h (not_lt.mpr (mul_nonneg hr.le (not_lt.mp hcon)))
    · intro h
      exact mul_neg_of_pos_of_neg hr h
  · constructor
    · intro h
      exact (mul_eq_zero.mp h).resolve_left hr.ne'
    · intro h
      rw [h, mul_zero]

/-- The motion along the first axis keeps how far apart two points of the plane are. -/
theorem shift_apart_plane {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {P Q : K × K} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    apart κ (shift κ a w P) (shift κ a w Q) = apart κ P Q := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  exact shift_apart hw hw0 (shift_den_pos hκ ha hP).ne' (shift_den_pos hκ ha hQ).ne'
    (mem_plane.mp hP).ne' (mem_plane.mp hQ).ne'

/-- **The motion takes lines of the plane to lines of the plane.** -/
theorem shift_isLine {κ a w : K} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {S : Set (K × K)} (hS : IsLine (plane κ) S) :
    IsLine (plane κ) (shift κ a w '' S) := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  have hw' : w ^ 2 = 1 + κ * (-a) ^ 2 := by
    rw [hw]
    ring
  have ha' : 0 < 1 + κ * (-a) ^ 2 := hw' ▸ hw2
  obtain ⟨M, hA, hB, hAB, rfl⟩ := hS.exists_within (plane_openAlong κ)
  have hDA := (shift_den_pos hκ ha hA).ne'
  have hDB := (shift_den_pos hκ ha hB).ne'
  have hτA : shift κ a w M.zero ∈ plane κ := shift_mem_plane hκ hw hw0 hA
  have hne : shift κ a w M.zero ≠ shift κ a w M.one := by
    intro h
    apply hAB
    have h' := congrArg (shift κ (-a) w) h
    rwa [shift_shift_neg hw hw0 hDA, shift_shift_neg hw hw0 hDB] at h'
  have hfactor : w * (1 + κ * a ^ 2) ≠ 0 := mul_ne_zero hw0 ha.ne'
  refine ⟨⟨shift κ a w M.zero, shift κ a w M.one⟩, hne, ?_,
    ⟨shift κ a w M.zero, M.zero, ⟨M.zero_mem, hA⟩, rfl⟩⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨X, ⟨hXM, hX⟩, rfl⟩
    refine ⟨?_, shift_mem_plane hκ hw hw0 hX⟩
    apply Dim.mem_points_of_side_eq_zero _ hne
    have hDX := (shift_den_pos hκ ha hX).ne'
    have hside := M.side_eq_zero_of_mem hXM
    simp only [Dim.side, Dim.dir] at hside ⊢
    rw [shift_cross κ a w hDA hDB hDX, hside, mul_zero, zero_div]
  · rintro Y ⟨hYN, hY⟩
    have hDY := (shift_den_pos hκ ha' hY).ne'
    have hX : shift κ (-a) w Y ∈ plane κ := shift_mem_plane hκ hw' hw0 hY
    have hback : shift κ a w (shift κ (-a) w Y) = Y := by
      have h := shift_shift_neg hw' hw0 hDY
      rwa [neg_neg] at h
    have hDX := (shift_den_pos hκ ha hX).ne'
    refine ⟨shift κ (-a) w Y, ⟨?_, hX⟩, hback⟩
    apply Dim.mem_points_of_side_eq_zero _ hAB
    have hside := Dim.side_eq_zero_of_mem _ hYN
    rw [← hback] at hside
    simp only [Dim.side, Dim.dir] at hside ⊢
    rw [shift_cross κ a w hDA hDB hDX] at hside
    have hden : (1 - κ * a * M.zero.1) * (1 - κ * a * M.one.1)
        * (1 - κ * a * (shift κ (-a) w Y).1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hDA hDB) hDX
    rcases div_eq_zero_iff.mp hside with h | h
    · exact (mul_eq_zero.mp h).resolve_left hfactor
    · exact absurd h hden

omit [IsStrictOrderedRing K] in
/-- **Turning takes points of the plane to points of the plane**, and no others. -/
theorem rot_mem_plane {c s : K} (h : c ^ 2 + s ^ 2 = 1) {κ : K} {p : K × K} :
    rot c s p ∈ plane κ ↔ p ∈ plane κ := by
  rw [mem_plane, mem_plane, rot_bound h]

omit [IsStrictOrderedRing K] in
/-- **Turning takes the plane onto itself, and different points to different points.** -/
theorem rot_bijOn {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) :
    Set.BijOn (rot c s) (plane κ) (plane κ) := by
  have h' : c ^ 2 + (-s) ^ 2 = 1 := by
    rw [← h]
    ring
  refine ⟨fun p hp => (rot_mem_plane h).mpr hp, ?_, ?_⟩
  · intro p _ q _ hpq
    have h2 := congrArg (rot c (-s)) hpq
    rwa [rot_rot_neg h, rot_rot_neg h] at h2
  · intro q hq
    refine ⟨rot c (-s) q, (rot_mem_plane h').mpr hq, ?_⟩
    have h2 := rot_rot_neg h' q
    rwa [neg_neg] at h2

omit [IsStrictOrderedRing K] in
/-- **Turning takes lines of the plane to lines of the plane.** -/
theorem rot_isLine {c s : K} (h : c ^ 2 + s ^ 2 = 1) {κ : K} {S : Set (K × K)}
    (hS : IsLine (plane κ) S) : IsLine (plane κ) (rot c s '' S) := by
  obtain ⟨M, hM, rfl, A, hAM, hA⟩ := hS
  have hne : rot c s M.zero ≠ rot c s M.one := by
    intro h'
    apply hM
    have h'' := congrArg (rot c (-s)) h'
    rwa [rot_rot_neg h, rot_rot_neg h] at h''
  refine ⟨⟨rot c s M.zero, rot c s M.one⟩, hne, ?_, ⟨rot c s A, A, ⟨hAM, hA⟩, rfl⟩⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨X, ⟨⟨t, rfl⟩, hX⟩, rfl⟩
    exact ⟨⟨t, (rot_pt c s M t).symm⟩, (rot_mem_plane h).mpr hX⟩
  · rintro Y ⟨⟨t, rfl⟩, hY⟩
    rw [← rot_pt] at hY
    exact ⟨M.pt t, ⟨⟨t, rfl⟩, (rot_mem_plane h).mp hY⟩, rot_pt c s M t⟩

end StepsOrder

end HyperbolicPlane
