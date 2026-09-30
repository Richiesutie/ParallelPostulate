/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import LeanCodeParallel.HyperbolicPlane.Angles
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The figure of `ThreeDimensions.lean` under the bound `-1`

Example H10 lays the figure of `ThreeDimensions.lean` in the plane of the bound `-1`, with
fractions for numbers: it meets the hypotheses of the postulate there, and its lines `b` and `c`
meet only outside the plane. Theorem H14 lays the same figure among the pairs of real numbers,
measures its two interior angles with `kleinAngle`, a right angle and the angle whose cosine is
`3 / √409`, and so shows that Euclid's fifth postulate, as he states it, fails under the bound
`-1`.

## Contents

* Example H10, the figure of `ThreeDimensions.lean` under the bound `-1`: `leaningFigure`,
  `leaningFigure_within`, `leaningFigure_values`, `leaningFigure_hypotheses`,
  `leaningFigure_numbers`, `leaningFigure_meets_beyond`, `leaningFigure_never_meets`,
  `leaningFigure_angles`
* Theorem H14, Euclid's fifth postulate fails under the bound `-1`: `EuclidFifth`,
  `realLeaningFigure`, `realLeaningFigure_within`, `realLeaningFigure_sides`,
  `realLeaningFigure_angle_a0`, `realLeaningFigure_angle_a1`, `realLeaningFigure_angle_a1_lt`,
  `realLeaningFigure_angles`, `realLeaningFigure_never_meets`, `not_euclidFifth`
-/

namespace HyperbolicPlane

open Pairs

/-! ## The figure of `ThreeDimensions.lean` under the bound -/

/-- A figure within the bound `-1`. `a` runs from `(0, 0)` to `(3/5, 0)`, `b` leaves `a0`
straight up, and `c` leaves `a1` leaning toward `b`. -/
def leaningFigure : Figure ℚ where
  a := ⟨(0, 0), (3 / 5, 0)⟩
  b := ⟨(0, 0), (0, 1 / 2)⟩
  c := ⟨(3 / 5, 0), (27 / 50, 1 / 2)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl

/-- Its zeros and its 1s are points of the plane of the bound `-1`. -/
theorem leaningFigure_within :
    leaningFigure.a.zero ∈ plane (-1 : ℚ) ∧ leaningFigure.a.one ∈ plane (-1 : ℚ) ∧
      leaningFigure.b.one ∈ plane (-1 : ℚ) ∧ leaningFigure.c.one ∈ plane (-1 : ℚ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [leaningFigure, plane]

/-- The sides of `b1` and of `c1`, and the cross product of the directions of `b` and `c`. -/
theorem leaningFigure_values :
    leaningFigure.a.side leaningFigure.b.one = 3 / 10 ∧
      leaningFigure.a.side leaningFigure.c.one = 3 / 10 ∧
      cross leaningFigure.b.dir leaningFigure.c.dir = 3 / 100 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [leaningFigure, Dim.side, Dim.dir, cross]

/-- It meets the three hypotheses of Theorem E4 (`ThreeDimensions.lean`). -/
theorem leaningFigure_hypotheses :
    0 < leaningFigure.a.side leaningFigure.b.one ∧
      0 < leaningFigure.a.side leaningFigure.c.one ∧
      0 < cross leaningFigure.b.dir leaningFigure.c.dir := by
  obtain ⟨h1, h2, h3⟩ := leaningFigure_values
  rw [h1, h2, h3]
  norm_num

/-- The two numbers at which Theorem E4 (`ThreeDimensions.lean`) has `b` and `c` meet are both
10. -/
theorem leaningFigure_numbers :
    cross leaningFigure.a.dir leaningFigure.c.dir / cross leaningFigure.b.dir leaningFigure.c.dir
        = 10 ∧
      cross leaningFigure.a.dir leaningFigure.b.dir
          / cross leaningFigure.b.dir leaningFigure.c.dir = 10 := by
  refine ⟨?_, ?_⟩ <;> norm_num [leaningFigure, Dim.dir, cross]

/-- As dimensions, `b` and `c` meet at the number 10 of each, at the pair `(0, 5)`, which is
not a point of the plane. -/
theorem leaningFigure_meets_beyond :
    leaningFigure.b.pt 10 = (0, 5) ∧ leaningFigure.c.pt 10 = (0, 5) ∧
      ((0 : ℚ), (5 : ℚ)) ∉ plane (-1 : ℚ) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Prod.ext <;> norm_num [leaningFigure, Dim.pt]
  · apply Prod.ext <;> norm_num [leaningFigure, Dim.pt]
  · norm_num [plane]

/-- **In the plane of the bound `-1` the lines of `b` and `c` do not meet.** -/
theorem leaningFigure_never_meets :
    (leaningFigure.b.points ∩ plane (-1 : ℚ)) ∩ (leaningFigure.c.points ∩ plane (-1 : ℚ))
      = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro X ⟨⟨⟨t, rfl⟩, hX⟩, ⟨⟨u, hu⟩, -⟩⟩
  have e1 := congrArg Prod.fst hu
  have e2 := congrArg Prod.snd hu
  simp only [leaningFigure, Dim.pt] at e1 e2
  have hu10 : u = 10 := by linarith
  have ht10 : t = 10 := by linarith
  rw [ht10] at hX
  rw [leaningFigure_meets_beyond.1] at hX
  exact leaningFigure_meets_beyond.2.2 hX

/-- **The two interior angles of the figure, as far as numbers can show them.** At `a0`, which
is `(0, 0)`, the directions of `a` and `b` have the inner product 0. The motion along the first
axis with `a = -3/5` and `w = 4/5` takes `a1` to `(0, 0)`, `a0` to `(-3/5, 0)`, and `c1` to
`(-15/169, 100/169)`. So after the motion `c` leaves `(0, 0)`, and the inner product of its
direction with the direction of `a` run backwards is positive. -/
theorem leaningFigure_angles :
    leaningFigure.a.dir.1 * leaningFigure.b.dir.1
        + leaningFigure.a.dir.2 * leaningFigure.b.dir.2 = 0 ∧
      ((4 / 5 : ℚ)) ^ 2 = 1 + (-1) * (-3 / 5) ^ 2 ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.a.one = (0, 0) ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.a.zero = (-3 / 5, 0) ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.c.one = (-15 / 169, 100 / 169) ∧
      (0 : ℚ) < (-15 / 169) * (-3 / 5) + (100 / 169) * 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [leaningFigure, Dim.dir]
  · norm_num
  · apply Prod.ext <;> norm_num [leaningFigure, shift]
  · apply Prod.ext <;> norm_num [leaningFigure, shift]
  · apply Prod.ext <;> norm_num [leaningFigure, shift]
  · norm_num

/-! ## Euclid's fifth postulate under the bound `-1`

The figure of Example H10, with real numbers, and its two interior angles measured with
`kleinAngle`. -/

section KleinFifth

open Real

/-- **Euclid's fifth postulate in the plane of the bound `κ`**, with the angles of
`kleinAngle`. Let `a` fall on `b` and `c`, with its zero, its 1, and `b1` and `c1` points of the
plane. Let `b1` and `c1` lie on the left of `a`, and let the two interior angles on that side be
together less than two right angles. Then `b` and `c`, produced on that side, meet at a point of
the plane, on that side. -/
def EuclidFifth (κ : ℝ) : Prop :=
  ∀ F : Figure ℝ, F.a.zero ∈ plane κ → F.a.one ∈ plane κ → F.b.one ∈ plane κ →
    F.c.one ∈ plane κ → 0 < F.a.side F.b.one → 0 < F.a.side F.c.one →
    kleinAngle κ F.a.zero F.a.one F.b.one + kleinAngle κ F.a.one F.a.zero F.c.one < π →
    ∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u ∧ F.b.pt t ∈ plane κ ∧
      0 < F.a.side (F.b.pt t)

/-- The figure of Example H10, with real numbers. -/
noncomputable def realLeaningFigure : Figure ℝ where
  a := ⟨(0, 0), (3 / 5, 0)⟩
  b := ⟨(0, 0), (0, 1 / 2)⟩
  c := ⟨(3 / 5, 0), (27 / 50, 1 / 2)⟩
  a0_eq_b0 := rfl
  a1_eq_c0 := rfl

/-- Its zeros and its 1s are points of the plane of the bound `-1`. -/
theorem realLeaningFigure_within :
    realLeaningFigure.a.zero ∈ plane (-1 : ℝ) ∧ realLeaningFigure.a.one ∈ plane (-1 : ℝ) ∧
      realLeaningFigure.b.one ∈ plane (-1 : ℝ) ∧ realLeaningFigure.c.one ∈ plane (-1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [realLeaningFigure, plane]

/-- `b1` and `c1` lie on the left of `a`. -/
theorem realLeaningFigure_sides :
    0 < realLeaningFigure.a.side realLeaningFigure.b.one ∧
      0 < realLeaningFigure.a.side realLeaningFigure.c.one := by
  refine ⟨?_, ?_⟩ <;> norm_num [realLeaningFigure, Dim.side, Dim.dir, cross]

/-- **The interior angle at `a0` is a right angle.** -/
theorem realLeaningFigure_angle_a0 :
    kleinAngle (-1) realLeaningFigure.a.zero realLeaningFigure.a.one realLeaningFigure.b.one
      = π / 2 := by
  have h : kleinInner (-1) realLeaningFigure.a.zero realLeaningFigure.a.one
      realLeaningFigure.b.one = 0 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  rw [kleinAngle, h, zero_div, arccos_zero]

/-- **The interior angle at `a1`** is the angle whose cosine is `3 / √409`, about 81.5 degrees.
With the angles of Euclid it would be the angle whose cosine is `3 / √634`. -/
theorem realLeaningFigure_angle_a1 :
    kleinAngle (-1) realLeaningFigure.a.one realLeaningFigure.a.zero realLeaningFigure.c.one
      = arccos (3 / √409) := by
  have h : kleinInner (-1) realLeaningFigure.a.one realLeaningFigure.a.zero
      realLeaningFigure.c.one = 9 / 250 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  have h1 : kleinInner (-1) realLeaningFigure.a.one realLeaningFigure.a.zero
      realLeaningFigure.a.zero = (3 / 5) ^ 2 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  have h2 : kleinInner (-1) realLeaningFigure.a.one realLeaningFigure.c.one
      realLeaningFigure.c.one = 409 / 50 ^ 2 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  have hs : 0 < √409 := by positivity
  rw [kleinAngle, h, h1, h2, sqrt_sq (by norm_num), sqrt_div' _ (by norm_num),
    sqrt_sq (by norm_num)]
  congr 1
  field_simp
  norm_num

/-- The interior angle at `a1` is less than a right angle. -/
theorem realLeaningFigure_angle_a1_lt :
    kleinAngle (-1) realLeaningFigure.a.one realLeaningFigure.a.zero realLeaningFigure.c.one
      < π / 2 := by
  rw [realLeaningFigure_angle_a1, arccos_lt_pi_div_two]
  positivity

/-- **The two interior angles are together less than two right angles.** -/
theorem realLeaningFigure_angles :
    kleinAngle (-1) realLeaningFigure.a.zero realLeaningFigure.a.one realLeaningFigure.b.one
      + kleinAngle (-1) realLeaningFigure.a.one realLeaningFigure.a.zero realLeaningFigure.c.one
      < π := by
  rw [realLeaningFigure_angle_a0]
  linarith [realLeaningFigure_angle_a1_lt]

/-- **In the plane of the bound `-1` the lines of `b` and `c` do not meet**, on either side
of `a`. As dimensions they meet at the pair `(0, 5)`, which is not a point of the plane. -/
theorem realLeaningFigure_never_meets :
    (realLeaningFigure.b.points ∩ plane (-1 : ℝ)) ∩ (realLeaningFigure.c.points ∩ plane (-1 : ℝ))
      = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro X ⟨⟨⟨t, rfl⟩, hX⟩, ⟨⟨u, hu⟩, -⟩⟩
  have e1 := congrArg Prod.fst hu
  have e2 := congrArg Prod.snd hu
  simp only [realLeaningFigure, Dim.pt] at e1 e2
  have hu10 : u = 10 := by linarith
  have ht10 : t = 10 := by linarith
  rw [ht10] at hX
  norm_num [realLeaningFigure, Dim.pt, plane] at hX

/-- **Theorem H14. Euclid's fifth postulate fails in the plane of the bound `-1`.** The figure
of Example H10 meets every hypothesis: its points are points of the plane, `b1` and `c1` lie on
the left of `a`, and the two interior angles on that side, a right angle and the angle whose
cosine is `3 / √409`, are together less than two right angles. But `b` and `c` have no point of
the plane in common. -/
theorem not_euclidFifth : ¬ EuclidFifth (-1) := by
  intro h
  obtain ⟨h0, h1, hb, hc⟩ := realLeaningFigure_within
  obtain ⟨sb, sc⟩ := realLeaningFigure_sides
  obtain ⟨t, u, -, -, htu, ht, -⟩ :=
    h realLeaningFigure h0 h1 hb hc sb sc realLeaningFigure_angles
  have hmem : realLeaningFigure.b.pt t ∈ (realLeaningFigure.b.points ∩ plane (-1 : ℝ))
      ∩ (realLeaningFigure.c.points ∩ plane (-1 : ℝ)) :=
    ⟨⟨⟨t, rfl⟩, ht⟩, ⟨⟨u, htu.symm⟩, ht⟩⟩
  rw [realLeaningFigure_never_meets] at hmem
  exact hmem

end KleinFifth

end HyperbolicPlane
