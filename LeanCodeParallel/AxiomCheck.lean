/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import LeanCodeParallel.ThreeDimensions
import LeanCodeParallel.HyperbolicPlane
import LeanCodeParallel.Hilbert

/-!
# The axioms of the main theorems

Each main theorem of the project depends only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`: there is no `sorry`, which would show as `sorryAx`, and no
axiom added by the project. Each check below is a `#guard_msgs`, so `lake build` fails if one of
these theorems comes to depend on anything else.
-/

/--
info: 'Hilbert.playfair_independent_continuous' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hilbert.playfair_independent_continuous

/--
info: 'Hilbert.playfair_independent' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hilbert.playfair_independent

/--
info: 'Hilbert.model_archimedes' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hilbert.model_archimedes

/--
info: 'Hilbert.model_dedekind' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hilbert.model_dedekind

/--
info: 'ThreeDimensions.playfair_exists' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ThreeDimensions.playfair_exists

/--
info: 'ThreeDimensions.playfair_unique_through' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ThreeDimensions.playfair_unique_through

/--
info: 'ThreeDimensions.euclid_fifth_either_side' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ThreeDimensions.euclid_fifth_either_side

/--
info: 'ThreeDimensions.meet_iff_angles_either_side' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ThreeDimensions.meet_iff_angles_either_side

/--
info: 'HyperbolicPlane.hyperbolic_parallel_property' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.hyperbolic_parallel_property

/--
info: 'HyperbolicPlane.one_parallel_iff_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.one_parallel_iff_bound

/--
info: 'HyperbolicPlane.not_euclidFifth' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.not_euclidFifth

/--
info: 'HyperbolicPlane.shift_kleinMetric_fderiv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.shift_kleinMetric_fderiv

/--
info: 'HyperbolicPlane.rot_kleinMetric_fderiv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.rot_kleinMetric_fderiv

/--
info: 'HyperbolicPlane.kleinAngle_unique' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.kleinAngle_unique

/--
info: 'HyperbolicPlane.kleinMetric_curvature' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.kleinMetric_curvature

/--
info: 'HyperbolicPlane.halfPlane_curvature' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.halfPlane_curvature

/--
info: 'HyperbolicPlane.apart_eq_sinh_kleinDist' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.apart_eq_sinh_kleinDist

/--
info: 'HyperbolicPlane.law_of_cosines' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.law_of_cosines

/--
info: 'HyperbolicPlane.segment_construction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.segment_construction

/--
info: 'HyperbolicPlane.segment_addition' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.segment_addition

/--
info: 'HyperbolicPlane.angle_construction' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.angle_construction

/--
info: 'HyperbolicPlane.side_angle_side' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms HyperbolicPlane.side_angle_side
