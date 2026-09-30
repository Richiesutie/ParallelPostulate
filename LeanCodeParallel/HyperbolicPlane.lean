/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import LeanCodeParallel.HyperbolicPlane.Plane
import LeanCodeParallel.HyperbolicPlane.Motions
import LeanCodeParallel.HyperbolicPlane.Angles
import LeanCodeParallel.HyperbolicPlane.Metric
import LeanCodeParallel.HyperbolicPlane.Curvature
import LeanCodeParallel.HyperbolicPlane.Distance
import LeanCodeParallel.HyperbolicPlane.Congruence
import LeanCodeParallel.HyperbolicPlane.LeaningFigure

/-!
# The hyperbolic plane: a bound on the dimensions

`ThreeDimensions.lean` lays three dimensions `a`, `b`, `c` among the pairs of numbers, with the two
constraints

    a0 = b0        a1 = c0

and proves the parallel postulate there. It takes every pair of numbers for a point of the
plane. This file keeps the dimensions, the pairs and the two constraints, and makes one choice:
a bound `κ`. The pair `(x, y)` is a point of the plane when

    0 < 1 + κ (x² + y²) .

With `κ = 0`, or any `κ` that is not negative, every pair is a point. That is the plane of
`ThreeDimensions.lean`, with one parallel. With real numbers it is Euclid's plane, which is
known. With `κ < 0`, through a point that is not on a line there are at least two different
lines, and in fact infinitely many, that do not meet the line. With `κ = -1`, and the angles of
Klein's model, Euclid's fifth postulate as he states it fails: two lines make interior angles
that are together less than two right angles, and never meet.

Checked with Lean `v4.35.0-rc3` and Mathlib at the matching tag (September 2026). Every theorem
uses only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Files

The dimensions and the figure are in `Basic.lean`. The rest is in the files below, in the
namespace `HyperbolicPlane`. The labels H11 and H12, a second bound made of three sides, belong
to a larger project and are not in this one.

* `HyperbolicPlane/Plane.lean`: the plane of a bound, its lines and its order, and its
  parallels (Theorems H1 to H7)
* `HyperbolicPlane/Motions.lean`: steps, the motion along the first axis, turning, and `apart`
  (Proposition H8, Theorem H9)
* `HyperbolicPlane/Angles.lean`: the inner product at a pair and the angle `kleinAngle`, which
  the motions keep (Theorems H13 and H15)
* `HyperbolicPlane/Metric.lean`: Klein's metric, which the motions keep (Theorem H16)
* `HyperbolicPlane/Curvature.lean`: its curvature is `κ` (Theorem H17)
* `HyperbolicPlane/Distance.lean`: Klein's distance, and `apart` as a function of it
  (Theorem H18)
* `HyperbolicPlane/Congruence.lean`: Hilbert's axioms of congruence (Theorem H19)
* `HyperbolicPlane/LeaningFigure.lean`: the figure of `ThreeDimensions.lean` under the bound
  `-1`, and Euclid's fifth postulate there (Example H10, Theorem H14)

## What is assumed, and what is not formalised

* **The hyperbolic plane of the books is not defined in these files.** That the plane of a
  negative bound, with real numbers, is a model of it is known (Beltrami 1868, Klein 1871).
  The files prove, for the plane of any bound and any ordered field, the statements on
  incidence and on order of Proposition H4, and they prove the statement on parallels. With the
  real numbers and a negative bound it proves Hilbert's six axioms of congruence (Theorem H19):
  a segment is measured by Klein's distance, `kleinDist`, an angle by `kleinAngle`, and two
  segments, or two angles, are congruent when their measures are equal. Of Hilbert's axioms of
  order, Proposition H4 has that of three points of a line at most one is between the two
  others, and `between_trichotomy` that one of them is. The axioms of continuity are in
  `Hilbert/Continuity.lean`. With the fractions for numbers the plane does not meet the axioms
  of congruence. That is not formalised.
* **`apart` and `kleinAngle` are numbers that the two motions of the file keep** (Theorems H9
  and H13). `kleinAngle` is
  the angle of Euclid, in Mathlib's sense, at `(0, 0)` under any bound, and at every pair under
  the bound 0 (`kleinAngle_centre`, `kleinAngle_zero_bound`). The motions take every point of
  the plane to `(0, 0)` (Theorem H15), and so `kleinAngle` is the only angle that the motions
  keep and that is the angle of Euclid at `(0, 0)`: `kleinAngle_unique`. `kleinMetric` is the
  metric of Klein's model as the books write it, and the two motions keep it: moved by the
  derivative of a motion in Mathlib's sense, two directions have the metric they had before
  (Theorem H16). `kleinAngle` is the angle of that metric: `kleinAngle_eq_metric`. Its
  curvature is `κ` (Theorem H17). Under a negative bound, `apart` is `sinh² (√(-κ) d) / (-κ)`,
  where `d` is the distance that the metric gives, `kleinDist` (Theorem H18). Theorem H14
  measures its angles with `kleinAngle`.
* **Klein's distance is the least length of a path.** Mathlib has no distance for a metric
  given by its coefficients, so `kleinDist` is the infimum of the lengths of the paths between
  two points: maps of `[0, 1]` into the plane with a continuous derivative. Paths with corners
  are not admitted. They give the same infimum, since the bound below in the proof of
  Theorem H18 holds for them too, but that is not formalised. Theorem H18 is proved for a
  negative bound only.
* **The curvature is Brioschi's formula.** Mathlib has no curvature for a metric given by its
  coefficients, so `gaussCurvature` is Brioschi's formula, with Mathlib's derivatives along the
  two axes. It gives the known curvature `-1` for the upper half plane of Poincaré:
  `halfPlane_curvature`. That it is the curvature of the Levi-Civita connection, or Gauss's
  curvature of a surface in space, is not formalised.
* **Theorem H14 is proved for the bound `-1` only.** For another negative bound the figure
  would be scaled, and that is not formalised. Example H10 keeps fractions for numbers, and
  `kleinAngle` has real numbers, so Theorem H14 lays the same figure among the pairs of real
  numbers: `realLeaningFigure`.
* **A bound that is positive does not give the plane of the sphere.** Every pair is then a
  point, and the points and lines are those of `ThreeDimensions.lean`. Klein's metric still has
  the curvature `κ` there (Theorem H17): it is then the metric of a half sphere, seen from its
  centre. That is not formalised.
* **In Lean a division by zero gives zero.** Seven theorems cover cases in which a denominator
  is zero. Four of them have the same quotient on both sides, so they hold whatever a division
  by zero gives: `step_comm`, `apart_comm`, `apart_centre` and
  `rot_apart`. Three hold at a division by zero because it gives zero: `step_neg` at a number
  on the edge, `apart_self` at a pair on the edge, and `shift_axis` where `1 - κ a t = 0`. All
  seven are meant where no division by zero is made. `kleinAngle` divides by zero when `A` or
  `B` is `P`, and is then `π / 2`, as Mathlib's angle is with a zero vector. It is meant where
  `A` and `B` are not `P`.
* **That the plane is built from dimensions** is a reading, and is not in Lean. In these files
  a plane is a set of pairs, and a dimension is any line among the pairs with a zero and a 1.
-/
