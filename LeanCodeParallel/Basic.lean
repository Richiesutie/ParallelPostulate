/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Dimensions laid among the pairs of numbers

A dimension is a number line with its own zero and its own 1, laid among the pairs of numbers
of a ring `K`: `Dim`, with its direction `Dim.dir`, its pairs `Dim.pt` and `Dim.points`, and the
side `Dim.side` of a pair. `cross` is the cross product of two directions. A figure, `Figure`,
is three dimensions `a`, `b`, `c` with the two constraints

    a0 = b0        a1 = c0

so that `a` is the line that falls on the two others. `ThreeDimensions.lean` and the files of
`HyperbolicPlane` both build on these, in the namespace `Pairs`.

## Contents

* a dimension, its direction, its pairs, its sides: `Dim`, `Dim.dir`, `Dim.pt`, `Dim.points`,
  `Dim.side`, `cross`
* a dimension with its zero moved: `Dim.rebase`, `Dim.rebase_dir`, `Dim.rebase_points`,
  `Dim.rebase_zero_ne_one`, `Dim.cross_rebase`
* small facts about a dimension: `Dim.pt_zero`, `Dim.pt_one`, `Dim.zero_mem`, `Dim.one_mem`,
  `Dim.dir_ne_zero`, `Dim.zero_ne_one_of_dir`, `Dim.side_eq_zero_of_mem`, `Dim.side_through`,
  `Dim.through_subset`
* the figure, with the two constraints: `Figure`, `Figure.a0_eq_b0`, `Figure.a1_eq_c0`,
  `Figure.a_meets_b`, `Figure.a_meets_c`, `Figure.side_b_one`, `Figure.side_c_one`,
  `Figure.side_b_pt`
* two right angles, and the figure with `a` run backwards:
  `Figure.never_meet_of_two_right_angles`, `Figure.reverse`, `Figure.reverse_side`,
  `Figure.reverse_dir`, `Figure.reverse_cross`
* with fractions: `cramer_aux`, `Figure.meet_eq`, `Figure.meet_unique`,
  `exists_mul_of_cross_eq_zero`, `Dim.pt_injective`, `Dim.mem_points_of_side_eq_zero`,
  `Dim.points_eq_through`
-/

namespace Pairs

section Ring

variable {K : Type*} [CommRing K]

/-- A dimension laid in the plane: a number line with its own zero and its own 1. -/
structure Dim (K : Type*) where
  /-- The point where the dimension has its zero. -/
  zero : K × K
  /-- The point where the dimension has its 1. -/
  one : K × K

/-- The cross product of two directions. It is positive when the second is a turn to the left
of the first, by less than two right angles. -/
def cross (u v : K × K) : K := u.1 * v.2 - u.2 * v.1

namespace Dim

/-- The direction of a dimension, from its zero to its 1. -/
def dir (L : Dim K) : K × K := (L.one.1 - L.zero.1, L.one.2 - L.zero.2)

/-- The point of the dimension at the number `t`. -/
def pt (L : Dim K) (t : K) : K × K :=
  (L.zero.1 + t * (L.one.1 - L.zero.1), L.zero.2 + t * (L.one.2 - L.zero.2))

/-- The side of the dimension on which a point lies: positive on its left, negative on its
right, and zero on the dimension itself. -/
def side (L : Dim K) (P : K × K) : K := cross L.dir (P.1 - L.zero.1, P.2 - L.zero.2)

/-- The points of a dimension. -/
def points (L : Dim K) : Set (K × K) := Set.range L.pt

/-- The dimension `M` with its zero moved to the point `P`. It keeps its direction. -/
def rebase (M : Dim K) (P : K × K) : Dim K :=
  ⟨P, (P.1 + (M.one.1 - M.zero.1), P.2 + (M.one.2 - M.zero.2))⟩

theorem pt_zero (L : Dim K) : L.pt 0 = L.zero := by
  apply Prod.ext <;> simp [pt]

theorem pt_one (L : Dim K) : L.pt 1 = L.one := by
  apply Prod.ext <;> simp [pt]

theorem zero_mem (L : Dim K) : L.zero ∈ L.points := ⟨0, L.pt_zero⟩

theorem one_mem (L : Dim K) : L.one ∈ L.points := ⟨1, L.pt_one⟩

theorem dir_ne_zero (L : Dim K) (hL : L.zero ≠ L.one) : L.dir ≠ (0, 0) := by
  intro h0
  apply hL
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [dir] at h1 h2
  exact Prod.ext (sub_eq_zero.mp h1).symm (sub_eq_zero.mp h2).symm

theorem zero_ne_one_of_dir (L : Dim K) (h : L.dir ≠ (0, 0)) : L.zero ≠ L.one := by
  intro e
  apply h
  simp only [dir, e, sub_self]

theorem rebase_dir (M : Dim K) (P : K × K) : (M.rebase P).dir = M.dir := by
  apply Prod.ext <;> simp [rebase, dir]

/-- A dimension can be given its zero at any of its points: it keeps its points. -/
theorem rebase_points (M : Dim K) {P : K × K} (hP : P ∈ M.points) :
    (M.rebase P).points = M.points := by
  obtain ⟨s, rfl⟩ := hP
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    refine ⟨s + t, ?_⟩
    apply Prod.ext
    · simp only [pt, rebase]
      ring
    · simp only [pt, rebase]
      ring
  · rintro _ ⟨t, rfl⟩
    refine ⟨t - s, ?_⟩
    apply Prod.ext
    · simp only [pt, rebase]
      ring
    · simp only [pt, rebase]
      ring

theorem rebase_zero_ne_one (L : Dim K) (hL : L.zero ≠ L.one) (P : K × K) :
    (L.rebase P).zero ≠ (L.rebase P).one := by
  intro h
  apply hL
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [rebase] at h1 h2
  apply Prod.ext
  · linear_combination h1
  · linear_combination h2

/-- The moved dimension has the direction of the dimension it was made from. -/
theorem cross_rebase (L : Dim K) (P : K × K) : cross L.dir (L.rebase P).dir = 0 := by
  simp only [cross, dir, rebase]
  ring

/-- The side of a pair of the dimension is zero. -/
theorem side_eq_zero_of_mem (L : Dim K) {P : K × K} (hP : P ∈ L.points) : L.side P = 0 := by
  obtain ⟨t, rfl⟩ := hP
  simp only [side, dir, pt, cross]
  ring

/-- Along the dimension from `A` to `C`, the side changes evenly from the side of `A` to the
side of `C`. -/
theorem side_through (L : Dim K) (A C : K × K) (u : K) :
    L.side ((Dim.mk A C).pt u) = (1 - u) * L.side A + u * L.side C := by
  simp only [side, dir, pt, cross]
  ring

/-- The dimension through two pairs of `L` has its pairs among those of `L`. -/
theorem through_subset (L : Dim K) {A B : K × K} (hA : A ∈ L.points) (hB : B ∈ L.points) :
    (Dim.mk A B).points ⊆ L.points := by
  obtain ⟨s, rfl⟩ := hA
  obtain ⟨s', rfl⟩ := hB
  rintro _ ⟨u, rfl⟩
  refine ⟨s + u * (s' - s), ?_⟩
  apply Prod.ext
  · simp only [pt]
    ring
  · simp only [pt]
    ring

end Dim

/-- The figure: three dimensions with `a0 = b0` and `a1 = c0`, read as points. -/
structure Figure (K : Type*) where
  /-- The straight line that falls on the two others. -/
  a : Dim K
  /-- The line that leaves `a` at `a0`. -/
  b : Dim K
  /-- The line that leaves `a` at `a1`. -/
  c : Dim K
  /-- The first constraint. -/
  a0_eq_b0 : a.zero = b.zero
  /-- The second constraint. -/
  a1_eq_c0 : a.one = c.zero

namespace Figure

/-- `a` meets `b` where `a` has its zero. -/
theorem a_meets_b (F : Figure K) : F.a.pt 0 = F.b.pt 0 := by
  rw [Dim.pt_zero, Dim.pt_zero]; exact F.a0_eq_b0

/-- `a` meets `c` where `a` has its 1. -/
theorem a_meets_c (F : Figure K) : F.a.pt 1 = F.c.pt 0 := by
  rw [Dim.pt_one, Dim.pt_zero]; exact F.a1_eq_c0

theorem side_b_one (F : Figure K) : F.a.side F.b.one = cross F.a.dir F.b.dir := by
  simp only [Dim.side, Dim.dir, F.a0_eq_b0]

theorem side_c_one (F : Figure K) : F.a.side F.c.one = cross F.a.dir F.c.dir := by
  simp only [Dim.side, Dim.dir, cross, ← F.a1_eq_c0]
  ring

theorem side_b_pt (F : Figure K) (t : K) :
    F.a.side (F.b.pt t) = t * cross F.a.dir F.b.dir := by
  simp only [Dim.side, Dim.dir, Dim.pt, cross, ← F.a0_eq_b0]
  ring

/-- **Two right angles: the lines never meet.** If the side of `c1` is not zero, and the cross
product of the directions of `b` and `c` is zero, the two lines have no point in common. -/
theorem never_meet_of_two_right_angles (F : Figure K)
    (hc : F.a.side F.c.one ≠ 0) (hsum : cross F.b.dir F.c.dir = 0) (t u : K) :
    F.b.pt t ≠ F.c.pt u := by
  intro heq
  apply hc
  rw [F.side_c_one]
  have hb0 : F.b.zero = F.a.zero := F.a0_eq_b0.symm
  have hc0 : F.c.zero = F.a.one := F.a1_eq_c0.symm
  have e1 := congrArg Prod.fst heq
  have e2 := congrArg Prod.snd heq
  simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at e1 e2 hsum ⊢
  linear_combination (-(F.c.one.2 - F.a.one.2)) * e1 + (F.c.one.1 - F.a.one.1) * e2 + t * hsum

/-- The same figure with `a` run backwards. It starts at `a1` and ends at `a0`, so the line
that leaves its zero is `c` and the line that leaves its 1 is `b`. Left and right of `a` change
places. -/
def reverse (F : Figure K) : Figure K where
  a := ⟨F.a.one, F.a.zero⟩
  b := F.c
  c := F.b
  a0_eq_b0 := F.a1_eq_c0
  a1_eq_c0 := F.a0_eq_b0

theorem reverse_side (F : Figure K) (P : K × K) : F.reverse.a.side P = -F.a.side P := by
  simp only [reverse, Dim.side, Dim.dir, cross]
  ring

theorem reverse_dir (F : Figure K) : F.reverse.a.dir = -F.a.dir := by
  apply Prod.ext <;> simp [reverse, Dim.dir]

theorem reverse_cross (F : Figure K) :
    cross F.reverse.b.dir F.reverse.c.dir = -cross F.b.dir F.c.dir := by
  simp only [reverse, cross]
  ring

end Figure

end Ring

section Field

variable {K : Type*} [Field K]

/-- The one step that divides. If `(a' - o) D = p n - x m`, the point at `n / D` along `p` from
`o` is the point at `m / D` along `x` from `a'`. -/
theorem cramer_aux (o a' p x n m D : K) (hD : D ≠ 0)
    (h : (a' - o) * D = p * n - x * m) : o + n / D * p = a' + m / D * x := by
  have hn : n / D * D = n := div_mul_cancel₀ _ hD
  have hm : m / D * D = m := div_mul_cancel₀ _ hD
  apply mul_right_cancel₀ hD
  linear_combination p * hn - x * hm - h

/-- Where `b` and `c` meet, when the cross product of their directions is not zero. -/
theorem Figure.meet_eq (F : Figure K) (hne : cross F.b.dir F.c.dir ≠ 0) :
    F.b.pt (cross F.a.dir F.c.dir / cross F.b.dir F.c.dir)
      = F.c.pt (cross F.a.dir F.b.dir / cross F.b.dir F.c.dir) := by
  have hb0 : F.b.zero = F.a.zero := F.a0_eq_b0.symm
  have hc0 : F.c.zero = F.a.one := F.a1_eq_c0.symm
  apply Prod.ext
  · simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at hne ⊢
    exact cramer_aux _ _ _ _ _ _ _ hne (by ring)
  · simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at hne ⊢
    exact cramer_aux _ _ _ _ _ _ _ hne (by ring)

/-- And they meet at one point only. -/
theorem Figure.meet_unique (F : Figure K) (hne : cross F.b.dir F.c.dir ≠ 0) {t u t' u' : K}
    (h : F.b.pt t = F.c.pt u) (h' : F.b.pt t' = F.c.pt u') : t = t' ∧ u = u' := by
  have hb0 : F.b.zero = F.a.zero := F.a0_eq_b0.symm
  have hc0 : F.c.zero = F.a.one := F.a1_eq_c0.symm
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  have e1' := congrArg Prod.fst h'
  have e2' := congrArg Prod.snd h'
  simp only [Dim.pt, Dim.dir, cross, hb0, hc0] at e1 e2 e1' e2' hne
  have ht : (t - t') * ((F.b.one.1 - F.a.zero.1) * (F.c.one.2 - F.a.one.2)
      - (F.b.one.2 - F.a.zero.2) * (F.c.one.1 - F.a.one.1)) = 0 := by
    linear_combination (F.c.one.2 - F.a.one.2) * e1 - (F.c.one.2 - F.a.one.2) * e1'
      - (F.c.one.1 - F.a.one.1) * e2 + (F.c.one.1 - F.a.one.1) * e2'
  have hu : (u - u') * ((F.b.one.1 - F.a.zero.1) * (F.c.one.2 - F.a.one.2)
      - (F.b.one.2 - F.a.zero.2) * (F.c.one.1 - F.a.one.1)) = 0 := by
    linear_combination (F.b.one.2 - F.a.zero.2) * e1 - (F.b.one.2 - F.a.zero.2) * e1'
      - (F.b.one.1 - F.a.zero.1) * e2 + (F.b.one.1 - F.a.zero.1) * e2'
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hne),
    sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_right hne)⟩

/-- A direction with cross product zero against `v` is a multiple of `v`. -/
theorem exists_mul_of_cross_eq_zero {v w : K × K} (hv : v ≠ (0, 0)) (h : cross v w = 0) :
    ∃ l : K, w = (l * v.1, l * v.2) := by
  simp only [cross] at h
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
    have hw : w.1 = 0 := by
      have h3 : v.2 * w.1 = 0 := by linear_combination w.2 * h1 - h
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 h2
      · exact h4
    refine ⟨w.2 / v.2, Prod.ext ?_ ?_⟩
    · simp only [h1, hw, mul_zero]
    · simp only [div_mul_cancel₀ _ h2]
  · refine ⟨w.1 / v.1, Prod.ext ?_ ?_⟩
    · simp only [div_mul_cancel₀ _ h1]
    · have h3 : w.2 * v.1 = w.1 * v.2 := by linear_combination h
      have h4 : w.1 / v.1 * v.1 = w.1 := div_mul_cancel₀ _ h1
      simp only []
      apply mul_right_cancel₀ h1
      linear_combination h3 - v.2 * h4

/-- A dimension is a number line: different numbers are at different pairs. -/
theorem Dim.pt_injective (M : Dim K) (hM : M.zero ≠ M.one) : Function.Injective M.pt := by
  intro s s' h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only [Dim.pt] at e1 e2
  by_contra hne
  have hs : s - s' ≠ 0 := sub_ne_zero.mpr hne
  have h1 : (s - s') * (M.one.1 - M.zero.1) = 0 := by linear_combination e1
  have h2 : (s - s') * (M.one.2 - M.zero.2) = 0 := by linear_combination e2
  exact M.dir_ne_zero hM
    (Prod.ext ((mul_eq_zero.mp h1).resolve_left hs) ((mul_eq_zero.mp h2).resolve_left hs))

/-- A pair whose side is zero is a pair of the dimension. -/
theorem Dim.mem_points_of_side_eq_zero (L : Dim K) (hL : L.zero ≠ L.one) (P : K × K)
    (h : L.side P = 0) : P ∈ L.points := by
  obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero (L.dir_ne_zero hL) h
  refine ⟨l, ?_⟩
  have l1 := congrArg Prod.fst hl
  have l2 := congrArg Prod.snd hl
  simp only [Dim.dir] at l1 l2
  apply Prod.ext
  · simp only [Dim.pt]
    linear_combination -l1
  · simp only [Dim.pt]
    linear_combination -l2

/-- Two different pairs of a dimension give the dimension: it has the pairs of the dimension
from the one to the other. -/
theorem Dim.points_eq_through (L : Dim K) {A B : K × K} (hA : A ∈ L.points)
    (hB : B ∈ L.points) (hAB : A ≠ B) : L.points = (Dim.mk A B).points := by
  apply Set.Subset.antisymm
  · obtain ⟨s, rfl⟩ := hA
    obtain ⟨s', rfl⟩ := hB
    have hs : s' - s ≠ 0 := by
      intro h
      apply hAB
      rw [sub_eq_zero.mp h]
    rintro _ ⟨x, rfl⟩
    refine ⟨(x - s) / (s' - s), ?_⟩
    have hx : (x - s) / (s' - s) * (s' - s) = x - s := div_mul_cancel₀ _ hs
    apply Prod.ext
    · simp only [Dim.pt]
      linear_combination (L.one.1 - L.zero.1) * hx
    · simp only [Dim.pt]
      linear_combination (L.one.2 - L.zero.2) * hx
  · exact L.through_subset hA hB

end Field

end Pairs
