/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import ParallelPostulate.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Three dimensions and the parallel postulate

Three dimensions `a`, `b`, `c`, each a number line with its own zero, and two constraints:

    a0 = b0        a1 = c0

So `a` is the straight line that falls on the two other lines: it meets `b` where `a` has its
zero, and `c` where `a` has its 1.

Checked with Lean `v4.35.0-rc3` and Mathlib at the matching tag (September 2026). Every theorem
uses only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The dimensions, the cross product and the figure, with their small facts, are in
`Basic.lean`, in the namespace `Pairs`. Some of the names below are there.

## Contents

* Lemma E1, read as numbers `a1 = c0` collapses `a`: `collapse`
* a dimension, its direction, its points, its sides: `Dim`, `Dim.dir`, `Dim.pt`, `Dim.points`,
  `Dim.side`
* the cross product: `cross`
* the figure, with the two constraints: `Figure`, `Figure.a0_eq_b0`, `Figure.a1_eq_c0`
* Lemma E2, three independent dimensions: `skew_of_independent`
* Example E3, whole numbers and fractions: `wholeFigure_hypotheses`, `whole_numbers_never_meet`,
  `exampleFigure_meets`
* Theorem E4, the postulate with no angle: `Figure.meet_eq`, `fifth_postulate`, and
  `fifth_postulate_right` on the right of `a`
* Theorem E5, the two other cases: `Figure.never_meet_of_two_right_angles`,
  `meet_on_the_other_side`, `meet_on_the_other_side_right`
* Theorem E6, exactly when: `Figure.meet_unique`, `meet_on_side_iff`, `meet_on_side_iff_right`
* Theorem E7, Playfair: `meet_of_cross_ne_zero`, `not_meet_of_cross_eq_zero`, `playfair_exists`,
  `playfair_unique`, `playfair_unique_through`
* a dimension with its zero moved: `Dim.rebase`, `Dim.rebase_points`, `meet_iff_common_point`
* Lemma E8, the sine of the two angles together: `sin_angle_sum`, `angle_pos_and_lt_pi`
* Theorem E9, the postulate as Euclid states it: `euclid_fifth_either_side`,
  `never_meet_either_side`, `other_side_either_side`, `meet_iff_angles_either_side`
* the same on the left of `a` only: `euclid_fifth_general`, `never_meet_general`,
  `other_side_general`, `meet_on_side_iff_angles`
* the figure with `a` run backwards: `Figure.reverse`, `Figure.reverse_side`,
  `Figure.reverse_angles`
* Proposition E10, the figure with given angles: `angleFigure`, `angle_at_a0`, `angle_at_a1`,
  `angleFigure_cross`, `law_of_sines`, `euclid_fifth`, `never_meet_of_sum_eq_pi`

## What is assumed, and what is not formalised

* **The postulate is not proved from Euclid's other postulates.** That cannot be done: the
  hyperbolic plane meets the others and fails this one. What is proved is that the plane of
  pairs of numbers of a field meets the postulate. It does so because of how it is made: adding
  moves a line to any point without turning it, and two lines of one plane meet if neither
  direction is a multiple of the other, because the numbers can be divided.
* **That this plane meets Euclid's other postulates** is not formalised.
* **That the plane is built from dimensions** is a reading, and is not in Lean. In this file
  the plane is `K × K`, and a dimension is any line in it with a zero and a 1.

-/

namespace ThreeDimensions

open Pairs

/-! ## Read as numbers, `a1 = c0` collapses the dimension `a` -/

/-- `ι n` is the number `n` of the plus world of `a`. The zero of a dimension is its own double:
`c0 + c0 = c0`. So if `a1` is `c0`, then `a1 + a1 = a1`. Every number of `a` is then `a0`. -/
theorem collapse {N : Type*} [Add N] (ι : ℤ → N)
    (hadd : ∀ m n : ℤ, ι (m + n) = ι m + ι n) (hidem : ι 1 + ι 1 = ι 1) (n : ℤ) :
    ι n = ι 0 := by
  have h2 : ι 2 = ι 1 := by
    have h := hadd 1 1
    rw [hidem] at h
    simpa using h
  have h10 : ι 1 = ι 0 := by
    have h := hadd 2 (-1)
    have h' := hadd 1 (-1)
    rw [h2] at h
    rw [← h'] at h
    simpa using h
  have hstep : ∀ m : ℤ, ι (m + 1) = ι m := by
    intro m
    have h := hadd m 1
    have h' := hadd m 0
    rw [h10, ← h'] at h
    simpa using h
  induction n using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [hstep]; exact ih
  | pred k ih =>
    have h := hstep (-(k : ℤ) - 1)
    rw [sub_add_cancel] at h
    rw [← h]; exact ih

/-! ## Three independent dimensions: the two lines never meet -/

/-- `a` runs from `O` to `O + a`. The line `b` leaves `O` and the line `c` leaves `O + a`. If the
three directions are independent, the two lines have no point in common. -/
theorem skew_of_independent {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (O a b c : V) (h : LinearIndependent K ![a, b, c]) (t u : K) :
    O + t • b ≠ O + a + u • c := by
  intro heq
  have h2 : t • b = a + u • c := by
    have h1 : O + t • b = O + (a + u • c) := by rw [heq, add_assoc]
    exact add_left_cancel h1
  have h0 : ∑ i : Fin 3, ![1, -t, u] i • ![a, b, c] i = 0 := by
    have h3 : (1 : K) • a + (-t) • b + u • c = 0 := by
      rw [one_smul, neg_smul, h2]; abel
    simpa [Fin.sum_univ_three] using h3
  have h4 := Fintype.linearIndependent_iff.mp h ![1, -t, u] h0 0
  simp at h4

/-! ## The plane -/

section Plane

variable {K : Type*} [CommRing K]

/-- Two dimensions meet. -/
def Meet (L M : Dim K) : Prop := ∃ t u : K, L.pt t = M.pt u

/-- Two dimensions meet exactly when they have a point in common. -/
theorem meet_iff_common_point (L M : Dim K) :
    Meet L M ↔ ∃ Q, Q ∈ L.points ∧ Q ∈ M.points := by
  constructor
  · rintro ⟨t, u, h⟩
    exact ⟨L.pt t, ⟨t, rfl⟩, ⟨u, h.symm⟩⟩
  · rintro ⟨Q, ⟨t, ht⟩, ⟨u, hu⟩⟩
    exact ⟨t, u, ht.trans hu.symm⟩

end Plane

/-! ## With whole numbers the postulate is false -/

/-- A figure with whole numbers: `a` from `(0, 0)` to `(1, 0)`, `b` towards `(1, 1)`, and `c`
from `(1, 0)` towards `(0, 1)`. -/
def wholeFigure : Figure ℤ where
  a := ⟨(0, 0), (1, 0)⟩
  b := ⟨(0, 0), (1, 1)⟩
  c := ⟨(1, 0), (0, 1)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl

/-- It meets every hypothesis of the postulate. -/
theorem wholeFigure_hypotheses :
    0 < wholeFigure.a.side wholeFigure.b.one ∧ 0 < wholeFigure.a.side wholeFigure.c.one ∧
      0 < cross wholeFigure.b.dir wholeFigure.c.dir := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [wholeFigure, Dim.side, Dim.dir, cross]

/-- **And its two lines never meet.** They cross at `(1/2, 1/2)`, between their points. -/
theorem whole_numbers_never_meet (t u : ℤ) : wholeFigure.b.pt t ≠ wholeFigure.c.pt u := by
  intro h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp [wholeFigure, Dim.pt] at h1 h2
  omega

/-! ## With fractions -/

section Fractions

variable {K : Type*} [Field K]

/-! ### The postulate as Playfair states it -/

/-- Two dimensions meet if the cross product of their directions is not zero. -/
theorem meet_of_cross_ne_zero (L M : Dim K) (h : cross L.dir M.dir ≠ 0) : Meet L M := by
  refine ⟨cross (M.zero.1 - L.zero.1, M.zero.2 - L.zero.2) M.dir / cross L.dir M.dir,
    cross (M.zero.1 - L.zero.1, M.zero.2 - L.zero.2) L.dir / cross L.dir M.dir, ?_⟩
  apply Prod.ext
  · simp only [Dim.pt, Dim.dir, cross] at h ⊢
    exact cramer_aux _ _ _ _ _ _ _ h (by ring)
  · simp only [Dim.pt, Dim.dir, cross] at h ⊢
    exact cramer_aux _ _ _ _ _ _ _ h (by ring)

/-- A dimension with the direction of `L`, through a point that is not on `L`, never meets
`L`. -/
theorem not_meet_of_cross_eq_zero (L M : Dim K) (hL : L.zero ≠ L.one)
    (h : cross L.dir M.dir = 0) (hP : M.zero ∉ L.points) : ¬ Meet L M := by
  rintro ⟨t, u, heq⟩
  obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) h
  apply hP
  refine ⟨t - u * l, ?_⟩
  have e1 := congrArg Prod.fst heq
  have e2 := congrArg Prod.snd heq
  have l1 := congrArg Prod.fst hl
  have l2 := congrArg Prod.snd hl
  simp only [Dim.pt, Dim.dir] at e1 e2 l1 l2
  apply Prod.ext
  · simp only [Dim.pt]
    linear_combination e1 + u * l1
  · simp only [Dim.pt]
    linear_combination e2 + u * l2

/-- **Playfair, first half.** Through a point that is not on `L` there is a line that never
meets `L`. -/
theorem playfair_exists (L : Dim K) (hL : L.zero ≠ L.one) (P : K × K) (hP : P ∉ L.points) :
    ∃ M : Dim K, M.zero = P ∧ M.zero ≠ M.one ∧ ¬ Meet L M := by
  refine ⟨⟨P, (P.1 + (L.one.1 - L.zero.1), P.2 + (L.one.2 - L.zero.2))⟩, rfl, ?_,
    not_meet_of_cross_eq_zero L ⟨P, (P.1 + (L.one.1 - L.zero.1), P.2 + (L.one.2 - L.zero.2))⟩
      hL ?_ hP⟩
  · intro h
    apply hL
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [] at h1 h2
    apply Prod.ext
    · linear_combination h1
    · linear_combination h2
  · simp only [cross, Dim.dir]
    ring

/-- If the direction of `M` is a multiple of the direction of `M'`, and they leave the same
point, every point of `M` is a point of `M'`. -/
theorem points_subset (M M' : Dim K) (hP : M.zero = M'.zero) (k : K)
    (hk : M.dir = (k * M'.dir.1, k * M'.dir.2)) : M.points ⊆ M'.points := by
  rintro _ ⟨t, rfl⟩
  refine ⟨t * k, ?_⟩
  have k1 := congrArg Prod.fst hk
  have k2 := congrArg Prod.snd hk
  have p1 := congrArg Prod.fst hP
  have p2 := congrArg Prod.snd hP
  simp only [Dim.dir] at k1 k2
  apply Prod.ext
  · simp only [Dim.pt]
    linear_combination -p1 - t * k1
  · simp only [Dim.pt]
    linear_combination -p2 - t * k2

/-- **Playfair, second half.** Two lines through the same point that never meet `L` are the
same line. -/
theorem playfair_unique (L M M' : Dim K) (hL : L.zero ≠ L.one) (hM : M.zero ≠ M.one)
    (hM' : M'.zero ≠ M'.one) (hP : M.zero = M'.zero)
    (h : ¬ Meet L M) (h' : ¬ Meet L M') : M.points = M'.points := by
  have c1 : cross L.dir M.dir = 0 := by
    by_contra hne
    exact h (meet_of_cross_ne_zero L M hne)
  have c2 : cross L.dir M'.dir = 0 := by
    by_contra hne
    exact h' (meet_of_cross_ne_zero L M' hne)
  obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) c1
  obtain ⟨l', hl'⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) c2
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply M.dir_ne_zero hM
    rw [hl]
    simp
  have hl'0 : l' ≠ 0 := by
    rintro rfl
    apply M'.dir_ne_zero hM'
    rw [hl']
    simp
  apply Set.Subset.antisymm
  · apply points_subset M M' hP (l / l')
    rw [hl, hl']
    apply Prod.ext
    · simp only []
      rw [← mul_assoc, div_mul_cancel₀ _ hl'0]
    · simp only []
      rw [← mul_assoc, div_mul_cancel₀ _ hl'0]
  · apply points_subset M' M hP.symm (l' / l)
    rw [hl, hl']
    apply Prod.ext
    · simp only []
      rw [← mul_assoc, div_mul_cancel₀ _ hl0]
    · simp only []
      rw [← mul_assoc, div_mul_cancel₀ _ hl0]

/-- **Playfair, second half, for lines through a point.** Two lines through the point `P` that
never meet `L` are the same line, wherever they have their zeros. -/
theorem playfair_unique_through (L M M' : Dim K) (hL : L.zero ≠ L.one) (hM : M.zero ≠ M.one)
    (hM' : M'.zero ≠ M'.one) {P : K × K} (hP : P ∈ M.points) (hP' : P ∈ M'.points)
    (h : ¬ Meet L M) (h' : ¬ Meet L M') : M.points = M'.points := by
  have hN : (M.rebase P).zero ≠ (M.rebase P).one :=
    (M.rebase P).zero_ne_one_of_dir (by rw [M.rebase_dir]; exact M.dir_ne_zero hM)
  have hN' : (M'.rebase P).zero ≠ (M'.rebase P).one :=
    (M'.rebase P).zero_ne_one_of_dir (by rw [M'.rebase_dir]; exact M'.dir_ne_zero hM')
  have hmeet : ¬ Meet L (M.rebase P) := by
    rw [meet_iff_common_point, M.rebase_points hP, ← meet_iff_common_point]
    exact h
  have hmeet' : ¬ Meet L (M'.rebase P) := by
    rw [meet_iff_common_point, M'.rebase_points hP', ← meet_iff_common_point]
    exact h'
  have hsame := playfair_unique L (M.rebase P) (M'.rebase P) hL hN hN' rfl hmeet hmeet'
  rwa [M.rebase_points hP, M'.rebase_points hP'] at hsame

end Fractions

/-! ## The postulate, in the plane over an ordered field -/

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The parallel postulate, in the plane of the three dimensions.**

`a` falls on `b` and `c`. Let `b1` and `c1` lie on the left of `a`, and let the two interior
angles on that side be together less than two right angles: `c` is a turn to the left of `b`.
Then `b` and `c`, produced on that side, meet on that side. For the right of `a` see
`fifth_postulate_right`. -/
theorem fifth_postulate (F : Figure K)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hsum : 0 < cross F.b.dir F.c.dir) :
    ∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ 0 < F.a.side (F.b.pt t) := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have ht : 0 < cross F.a.dir F.c.dir / cross F.b.dir F.c.dir := div_pos hc hsum
  refine ⟨_, _, ht, div_pos hb hsum, F.meet_eq hsum.ne', ?_⟩
  rw [F.side_b_pt]
  exact mul_pos ht hb

/-- **More than two right angles: the lines meet on the other side.** -/
theorem meet_on_the_other_side (F : Figure K)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hsum : cross F.b.dir F.c.dir < 0) :
    ∃ t u : K, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have ht : cross F.a.dir F.c.dir / cross F.b.dir F.c.dir < 0 := div_neg_of_pos_of_neg hc hsum
  refine ⟨_, _, ht, div_neg_of_pos_of_neg hb hsum, F.meet_eq hsum.ne, ?_⟩
  rw [F.side_b_pt]
  exact mul_neg_of_neg_of_pos ht hb

/-- **Exactly when.** The lines `b` and `c` meet on the side of `b1` and `c1` exactly when `c`
is a turn to the left of `b`. -/
theorem meet_on_side_iff (F : Figure K)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    (∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔ 0 < cross F.b.dir F.c.dir := by
  constructor
  · rintro ⟨t, u, ht, -, h⟩
    rcases lt_trichotomy (cross F.b.dir F.c.dir) 0 with hneg | hzero | hpos
    · obtain ⟨t', u', ht', -, h', -⟩ := meet_on_the_other_side F hb hc hneg
      have htt := (F.meet_unique hneg.ne h h').1
      rw [htt] at ht
      exact absurd ht (lt_asymm ht')
    · exact absurd h (F.never_meet_of_two_right_angles hc.ne' hzero t u)
    · exact hpos
  · intro hsum
    obtain ⟨t, u, ht, hu, h, -⟩ := fifth_postulate F hb hc hsum
    exact ⟨t, u, ht, hu, h⟩

/-- **The postulate on the other side of `a`.** If `b1` and `c1` lie on the right of `a`, and
`c` is a turn to the right of `b`, the lines meet on the right of `a`. -/
theorem fifth_postulate_right (F : Figure K)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0)
    (hsum : cross F.b.dir F.c.dir < 0) :
    ∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have ht : 0 < cross F.a.dir F.c.dir / cross F.b.dir F.c.dir := div_pos_of_neg_of_neg hc hsum
  refine ⟨_, _, ht, div_pos_of_neg_of_neg hb hsum, F.meet_eq hsum.ne, ?_⟩
  rw [F.side_b_pt]
  exact mul_neg_of_pos_of_neg ht hb

/-- **More than two right angles, on the right of `a`: the lines meet on the left of `a`.** -/
theorem meet_on_the_other_side_right (F : Figure K)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0)
    (hsum : 0 < cross F.b.dir F.c.dir) :
    ∃ t u : K, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧ 0 < F.a.side (F.b.pt t) := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have ht : cross F.a.dir F.c.dir / cross F.b.dir F.c.dir < 0 := div_neg_of_neg_of_pos hc hsum
  refine ⟨_, _, ht, div_neg_of_neg_of_pos hb hsum, F.meet_eq hsum.ne', ?_⟩
  rw [F.side_b_pt]
  exact mul_pos_of_neg_of_neg ht hb

/-- **Exactly when, on the other side.** -/
theorem meet_on_side_iff_right (F : Figure K)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0) :
    (∃ t u : K, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔ cross F.b.dir F.c.dir < 0 := by
  have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hc
  have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hb
  have h := meet_on_side_iff F.reverse hb' hc'
  rw [F.reverse_cross, neg_pos] at h
  rw [← h]
  constructor
  · rintro ⟨t, u, ht, hu, e⟩
    exact ⟨u, t, hu, ht, e.symm⟩
  · rintro ⟨t, u, ht, hu, e⟩
    exact ⟨u, t, hu, ht, e.symm⟩

end Ordered

/-- The figure of `wholeFigure`, with fractions in the dimensions. -/
def exampleFigure : Figure ℚ where
  a := ⟨(0, 0), (1, 0)⟩
  b := ⟨(0, 0), (1, 1)⟩
  c := ⟨(1, 0), (0, 1)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl

/-- It meets every hypothesis of the postulate, and its two lines meet at `(1/2, 1/2)`. -/
theorem exampleFigure_meets :
    0 < exampleFigure.a.side exampleFigure.b.one ∧
      0 < exampleFigure.a.side exampleFigure.c.one ∧
      0 < cross exampleFigure.b.dir exampleFigure.c.dir ∧
      exampleFigure.b.pt (1 / 2) = (1 / 2, 1 / 2) ∧
      exampleFigure.c.pt (1 / 2) = (1 / 2, 1 / 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [exampleFigure, Dim.side, Dim.dir, Dim.pt, cross]

/-! ## The figure with given angles -/

section Angles

open Real

/-- The figure with `a` from `(0, 0)` to `(1, 0)`. The line `b` leaves `a0` at the angle `β` to
`a`. The line `c` leaves `a1` at the angle `γ` to `a` run backwards. So `β` and `γ` are the two
interior angles on the upper side of `a`. -/
noncomputable def angleFigure (β γ : ℝ) : Figure ℝ where
  a := ⟨(0, 0), (1, 0)⟩
  b := ⟨(0, 0), (cos β, sin β)⟩
  c := ⟨(1, 0), (1 - cos γ, sin γ)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl

theorem angleFigure_side_b (β γ : ℝ) :
    (angleFigure β γ).a.side (angleFigure β γ).b.one = sin β := by
  simp [angleFigure, Dim.side, Dim.dir, cross]

theorem angleFigure_side_c (β γ : ℝ) :
    (angleFigure β γ).a.side (angleFigure β γ).c.one = sin γ := by
  simp [angleFigure, Dim.side, Dim.dir, cross]

theorem angleFigure_cross (β γ : ℝ) :
    cross (angleFigure β γ).b.dir (angleFigure β γ).c.dir = sin (β + γ) := by
  simp only [angleFigure, Dim.dir, cross, sin_add]
  ring

/-- **Euclid's fifth postulate, for the figure with the angles `β` and `γ`.** If the two
interior angles on the upper side of `a` are together less than two right angles, the lines `b`
and `c`, produced on that side, meet on that side. -/
theorem euclid_fifth (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (h : β + γ < π) :
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧
      (angleFigure β γ).b.pt t = (angleFigure β γ).c.pt u ∧
      0 < (angleFigure β γ).a.side ((angleFigure β γ).b.pt t) := by
  apply fifth_postulate
  · rw [angleFigure_side_b]
    exact sin_pos_of_pos_of_lt_pi hβ (by linarith)
  · rw [angleFigure_side_c]
    exact sin_pos_of_pos_of_lt_pi hγ (by linarith)
  · rw [angleFigure_cross]
    exact sin_pos_of_pos_of_lt_pi (by linarith) h

/-- **Where they meet: the law of sines.** The point is at the number `sin γ / sin (β + γ)` of
`b`, and at the number `sin β / sin (β + γ)` of `c`. -/
theorem law_of_sines (β γ : ℝ) (h : sin (β + γ) ≠ 0) :
    (angleFigure β γ).b.pt (sin γ / sin (β + γ))
      = (angleFigure β γ).c.pt (sin β / sin (β + γ)) := by
  have hc : cross (angleFigure β γ).a.dir (angleFigure β γ).c.dir = sin γ := by
    rw [← Figure.side_c_one, angleFigure_side_c]
  have hb : cross (angleFigure β γ).a.dir (angleFigure β γ).b.dir = sin β := by
    rw [← Figure.side_b_one, angleFigure_side_b]
  have hne : cross (angleFigure β γ).b.dir (angleFigure β γ).c.dir ≠ 0 := by
    rw [angleFigure_cross]; exact h
  have hmeet := (angleFigure β γ).meet_eq hne
  rw [hc, hb, angleFigure_cross] at hmeet
  exact hmeet

/-- **Two right angles: the lines never meet.** -/
theorem never_meet_of_sum_eq_pi (β γ : ℝ) (hγ : 0 < γ) (hγ' : γ < π) (h : β + γ = π)
    (t u : ℝ) : (angleFigure β γ).b.pt t ≠ (angleFigure β γ).c.pt u := by
  apply Figure.never_meet_of_two_right_angles
  · rw [angleFigure_side_c]
    exact (sin_pos_of_pos_of_lt_pi hγ hγ').ne'
  · rw [angleFigure_cross, h, sin_pi]

end Angles

/-! ## The angles are angles in Mathlib's sense -/

section MathlibAngles

open Real InnerProductGeometry

/-- A direction of the plane of the three dimensions, as a vector of Mathlib's Euclidean
plane. -/
noncomputable def toE (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) := !₂[p.1, p.2]

theorem inner_toE (p q : ℝ × ℝ) : inner ℝ (toE p) (toE q) = p.1 * q.1 + p.2 * q.2 := by
  simp [toE, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem norm_toE (p : ℝ × ℝ) : ‖toE p‖ = √(p.1 ^ 2 + p.2 ^ 2) := by
  simp [toE, EuclideanSpace.norm_eq, Fin.sum_univ_two]

theorem norm_toE_sq (p : ℝ × ℝ) : ‖toE p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [norm_toE, sq_sqrt (by positivity)]

theorem norm_toE_neg (p : ℝ × ℝ) : ‖toE (-p)‖ = ‖toE p‖ := by
  rw [norm_toE, norm_toE]
  simp

/-- The interior angle at `a0`, between `a` and `b`, is `β`. -/
theorem angle_at_a0 (β γ : ℝ) (h0 : 0 ≤ β) (hπ : β ≤ π) :
    angle (toE (angleFigure β γ).a.dir) (toE (angleFigure β γ).b.dir) = β := by
  rw [angle, inner_toE, norm_toE, norm_toE]
  simp [angleFigure, Dim.dir, arccos_cos h0 hπ]

/-- The interior angle at `a1`, between `a` run backwards and `c`, is `γ`. -/
theorem angle_at_a1 (β γ : ℝ) (h0 : 0 ≤ γ) (hπ : γ ≤ π) :
    angle (toE (-(angleFigure β γ).a.dir)) (toE (angleFigure β γ).c.dir) = γ := by
  rw [angle, inner_toE, norm_toE, norm_toE]
  simp [angleFigure, Dim.dir, arccos_cos h0 hπ]

/-! ### Any figure in the real plane -/

theorem cos_angle_toE (p q : ℝ × ℝ) :
    cos (angle (toE p) (toE q)) * (‖toE p‖ * ‖toE q‖) = p.1 * q.1 + p.2 * q.2 := by
  rw [cos_angle_mul_norm_mul_norm, inner_toE]

theorem sin_angle_toE (p q : ℝ × ℝ) :
    sin (angle (toE p) (toE q)) * (‖toE p‖ * ‖toE q‖) = |cross p q| := by
  rw [sin_angle_mul_norm_mul_norm, inner_toE, inner_toE, inner_toE, ← sqrt_sq_eq_abs]
  congr 1
  simp only [cross]
  ring

theorem normSq_pos_left {p q : ℝ × ℝ} (h : cross p q ≠ 0) : 0 < p.1 ^ 2 + p.2 ^ 2 := by
  by_contra hn
  push Not at hn
  have h1 : p.1 ^ 2 = 0 := by linarith [sq_nonneg p.1, sq_nonneg p.2]
  have h2 : p.2 ^ 2 = 0 := by linarith [sq_nonneg p.1, sq_nonneg p.2]
  have h3 : p.1 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1
  have h4 : p.2 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
  apply h
  simp [cross, h3, h4]

theorem normSq_pos_right {p q : ℝ × ℝ} (h : cross p q ≠ 0) : 0 < q.1 ^ 2 + q.2 ^ 2 := by
  by_contra hn
  push Not at hn
  have h1 : q.1 ^ 2 = 0 := by linarith [sq_nonneg q.1, sq_nonneg q.2]
  have h2 : q.2 ^ 2 = 0 := by linarith [sq_nonneg q.1, sq_nonneg q.2]
  have h3 : q.1 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h1
  have h4 : q.2 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
  apply h
  simp [cross, h3, h4]

theorem norm_toE_pos_left {p q : ℝ × ℝ} (h : cross p q ≠ 0) : 0 < ‖toE p‖ := by
  rw [norm_toE]
  exact sqrt_pos.mpr (normSq_pos_left h)

theorem norm_toE_pos_right {p q : ℝ × ℝ} (h : cross p q ≠ 0) : 0 < ‖toE q‖ := by
  rw [norm_toE]
  exact sqrt_pos.mpr (normSq_pos_right h)

/-- Two directions whose cross product is not zero make an angle that is more than nothing
and less than two right angles. -/
theorem angle_pos_and_lt_pi {p q : ℝ × ℝ} (h : cross p q ≠ 0) :
    0 < angle (toE p) (toE q) ∧ angle (toE p) (toE q) < π := by
  have hN : 0 < ‖toE p‖ * ‖toE q‖ := mul_pos (norm_toE_pos_left h) (norm_toE_pos_right h)
  have hs := sin_angle_toE p q
  have habs : 0 < |cross p q| := abs_pos.mpr h
  have hsin : 0 < sin (angle (toE p) (toE q)) := by
    by_contra hn
    push Not at hn
    have h5 := mul_nonpos_of_nonpos_of_nonneg hn hN.le
    linarith
  constructor
  · rcases (angle_nonneg (toE p) (toE q)).eq_or_lt with h0 | h0
    · rw [← h0, sin_zero] at hsin
      exact absurd hsin (lt_irrefl 0)
    · exact h0
  · rcases (angle_le_pi (toE p) (toE q)).eq_or_lt with h0 | h0
    · rw [h0, sin_pi] at hsin
      exact absurd hsin (lt_irrefl 0)
    · exact h0

/-- **The sine of the two interior angles together.** `a` is the direction of the line that
falls on the two others, and `b` and `c` are the directions of the two others, both to the left
of `a`. With `β` the angle from `a` to `b`, and `γ` the angle from `a` run backwards to `c`:

    sin (β + γ) · |b| · |c| = cross b c . -/
theorem sin_angle_sum (a b c : ℝ × ℝ) (hab : 0 < cross a b) (hac : 0 < cross a c) :
    sin (angle (toE a) (toE b) + angle (toE (-a)) (toE c)) * (‖toE b‖ * ‖toE c‖)
      = cross b c := by
  have hA : 0 < ‖toE a‖ := norm_toE_pos_left hab.ne'
  have hA2 := norm_toE_sq a
  have hsβ := sin_angle_toE a b
  have hcβ := cos_angle_toE a b
  have hsγ := sin_angle_toE (-a) c
  have hcγ := cos_angle_toE (-a) c
  have hac' : cross (-a) c = -cross a c := by
    simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring
  rw [abs_of_pos hab] at hsβ
  rw [hac', abs_neg, abs_of_pos hac, norm_toE_neg] at hsγ
  rw [norm_toE_neg] at hcγ
  simp only [Prod.fst_neg, Prod.snd_neg] at hcγ
  simp only [cross] at hsβ hsγ ⊢
  generalize angle (toE a) (toE b) = β at *
  generalize angle (toE (-a)) (toE c) = γ at *
  generalize ‖toE a‖ = A at *
  generalize ‖toE b‖ = B at *
  generalize ‖toE c‖ = C at *
  have hA2' : A ^ 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ hA2'
  rw [sin_add]
  linear_combination (cos γ * (A * C)) * hsβ + (a.1 * b.2 - a.2 * b.1) * hcγ
    + (sin γ * (A * C)) * hcβ + (a.1 * b.1 + a.2 * b.2) * hsγ
    - (b.1 * c.2 - b.2 * c.1) * hA2

/-- What the two interior angles of a figure say, gathered. -/
theorem _root_.Pairs.Figure.angle_facts (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    sin (angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir))
        * (‖toE F.b.dir‖ * ‖toE F.c.dir‖) = cross F.b.dir F.c.dir ∧
      0 < ‖toE F.b.dir‖ * ‖toE F.c.dir‖ ∧
      0 < angle (toE F.a.dir) (toE F.b.dir) ∧ angle (toE F.a.dir) (toE F.b.dir) < π ∧
      0 < angle (toE (-F.a.dir)) (toE F.c.dir) ∧ angle (toE (-F.a.dir)) (toE F.c.dir) < π := by
  rw [F.side_b_one] at hb
  rw [F.side_c_one] at hc
  have hc' : cross (-F.a.dir) F.c.dir ≠ 0 := by
    have hneg : cross (-F.a.dir) F.c.dir = -cross F.a.dir F.c.dir := by
      simp only [cross, Prod.fst_neg, Prod.snd_neg]; ring
    rw [hneg]
    exact neg_ne_zero.mpr hc.ne'
  obtain ⟨hβ0, hβπ⟩ := angle_pos_and_lt_pi hb.ne'
  obtain ⟨hγ0, hγπ⟩ := angle_pos_and_lt_pi hc'
  exact ⟨sin_angle_sum _ _ _ hb hc,
    mul_pos (norm_toE_pos_right hb.ne') (norm_toE_pos_right hc.ne'), hβ0, hβπ, hγ0, hγπ⟩

/-- Less than two right angles: `c` is a turn to the left of `b`. -/
theorem cross_pos_of_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    0 < cross F.b.dir F.c.dir := by
  obtain ⟨hsin, hN, hβ0, -, hγ0, -⟩ := F.angle_facts hb hc
  rw [← hsin]
  exact mul_pos (sin_pos_of_pos_of_lt_pi (by linarith) hang) hN

/-- Two right angles: the cross product of the directions of `b` and `c` is zero. -/
theorem cross_eq_zero_of_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) = π) :
    cross F.b.dir F.c.dir = 0 := by
  obtain ⟨hsin, -, -, -, -, -⟩ := F.angle_facts hb hc
  rw [← hsin, hang, sin_pi, zero_mul]

/-- More than two right angles: `c` is a turn to the right of `b`. -/
theorem cross_neg_of_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    cross F.b.dir F.c.dir < 0 := by
  obtain ⟨hsin, hN, -, hβπ, -, hγπ⟩ := F.angle_facts hb hc
  rw [← hsin]
  have hneg : sin (angle (toE F.a.dir) (toE F.b.dir)
      + angle (toE (-F.a.dir)) (toE F.c.dir)) < 0 := by
    rw [← sin_sub_two_pi]
    exact sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  exact mul_neg_of_neg_of_pos hneg hN

/-- **Euclid's fifth postulate, on the left of `a`, for any figure in the real plane.** The
angles are angles in Mathlib's sense. If `b1` and `c1` lie on the left of `a`, and the two
interior angles on that side are together less than two right angles, then `b` and `c` meet on
that side. For either side see `euclid_fifth_either_side`. -/
theorem euclid_fifth_general (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ 0 < F.a.side (F.b.pt t) :=
  fifth_postulate F hb hc (cross_pos_of_angles F hb hc hang)

/-- **Two right angles, with `b1` and `c1` on the left of `a`, for any figure in the real
plane: the lines never meet.** For either side see `never_meet_either_side`. -/
theorem never_meet_general (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) = π)
    (t u : ℝ) : F.b.pt t ≠ F.c.pt u :=
  F.never_meet_of_two_right_angles hc.ne' (cross_eq_zero_of_angles F hb hc hang) t u

/-- **More than two right angles, with `b1` and `c1` on the left of `a`, for any figure in the
real plane: the lines meet on the right of `a`.** For either side see
`other_side_either_side`. -/
theorem other_side_general (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    ∃ t u : ℝ, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 :=
  meet_on_the_other_side F hb hc (cross_neg_of_angles F hb hc hang)

/-- **The postulate and its converse.** In the real plane, the lines `b` and `c` meet on the
side of `b1` and `c1` exactly when the two interior angles on that side are together less than
two right angles. -/
theorem meet_on_side_iff_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    (∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔
      angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π := by
  rw [meet_on_side_iff F hb hc]
  constructor
  · intro hpos
    rcases lt_trichotomy
        (angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) π
      with h | h | h
    · exact h
    · have h0 := cross_eq_zero_of_angles F hb hc h
      rw [h0] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact absurd hpos (lt_asymm (cross_neg_of_angles F hb hc h))
  · exact cross_pos_of_angles F hb hc

/-! ### Either side of `a` -/

/-- The two interior angles of the figure with `a` run backwards are the two interior angles
of the figure, in the other order. -/
theorem _root_.Pairs.Figure.reverse_angles (F : Figure ℝ) :
    angle (toE F.reverse.a.dir) (toE F.reverse.b.dir)
        + angle (toE (-F.reverse.a.dir)) (toE F.reverse.c.dir)
      = angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) := by
  rw [F.reverse_dir, neg_neg]
  change angle (toE (-F.a.dir)) (toE F.c.dir) + angle (toE F.a.dir) (toE F.b.dir)
    = angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)
  ring

/-- **Euclid's fifth postulate on the right of `a`.** -/
theorem euclid_fifth_right (F : Figure ℝ)
    (hb : F.a.side F.b.one < 0) (hc : F.a.side F.c.one < 0)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 := by
  have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hc
  have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
    rw [F.reverse_side]; exact neg_pos.mpr hb
  have hang' := hang
  rw [← F.reverse_angles] at hang'
  obtain ⟨t, u, ht, hu, e, hs⟩ := euclid_fifth_general F.reverse hb' hc' hang'
  have e' : F.b.pt u = F.c.pt t := e.symm
  refine ⟨u, t, hu, ht, e', ?_⟩
  rw [F.reverse_side] at hs
  rw [e']
  exact neg_pos.mp hs

/-- **Euclid's fifth postulate, in the real plane, on either side.** If `b1` and `c1` lie on
the same side of `a`, and the two interior angles on that side are together less than two right
angles, then `b` and `c` meet on that side. -/
theorem euclid_fifth_either_side (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧
      0 < F.a.side (F.b.pt t) * F.a.side F.b.one := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · obtain ⟨t, u, ht, hu, e, hs⟩ := euclid_fifth_general F hb hc hang
    exact ⟨t, u, ht, hu, e, mul_pos hs hb⟩
  · obtain ⟨t, u, ht, hu, e, hs⟩ := euclid_fifth_right F hb hc hang
    exact ⟨t, u, ht, hu, e, mul_pos_of_neg_of_neg hs hb⟩

/-- **Two right angles, on either side: the lines never meet.** -/
theorem never_meet_either_side (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) = π)
    (t u : ℝ) : F.b.pt t ≠ F.c.pt u := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · exact never_meet_general F hb hc hang t u
  · have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hc
    have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hb
    have hang' := hang
    rw [← F.reverse_angles] at hang'
    intro e
    exact never_meet_general F.reverse hb' hc' hang' u t e.symm

/-- **More than two right angles, on either side: the lines meet on the other side.** -/
theorem other_side_either_side (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one)
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    ∃ t u : ℝ, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧
      F.a.side (F.b.pt t) * F.a.side F.b.one < 0 := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · obtain ⟨t, u, ht, hu, e, hs⟩ := other_side_general F hb hc hang
    exact ⟨t, u, ht, hu, e, mul_neg_of_neg_of_pos hs hb⟩
  · have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hc
    have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hb
    have hang' := hang
    rw [← F.reverse_angles] at hang'
    obtain ⟨t, u, ht, hu, e, hs⟩ := other_side_general F.reverse hb' hc' hang'
    have e' : F.b.pt u = F.c.pt t := e.symm
    refine ⟨u, t, hu, ht, e', ?_⟩
    rw [F.reverse_side] at hs
    rw [e']
    exact mul_neg_of_pos_of_neg (neg_lt_zero.mp hs) hb

/-- **The postulate and its converse, on either side.** In the real plane, let `b1` and `c1`
lie on the same side of `a`. The lines `b` and `c`, produced towards `b1` and `c1`, meet exactly
when the two interior angles on that side are together less than two right angles. -/
theorem meet_iff_angles_either_side (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one) :
    (∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔
      angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π := by
  rcases mul_pos_iff.mp hside with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · exact meet_on_side_iff_angles F hb hc
  · have hb' : 0 < F.reverse.a.side F.reverse.b.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hc
    have hc' : 0 < F.reverse.a.side F.reverse.c.one := by
      rw [F.reverse_side]; exact neg_pos.mpr hb
    have h := meet_on_side_iff_angles F.reverse hb' hc'
    rw [F.reverse_angles] at h
    rw [← h]
    constructor
    · rintro ⟨t, u, ht, hu, e⟩
      exact ⟨u, t, hu, ht, e.symm⟩
    · rintro ⟨t, u, ht, hu, e⟩
      exact ⟨u, t, hu, ht, e.symm⟩

end MathlibAngles

end ThreeDimensions
