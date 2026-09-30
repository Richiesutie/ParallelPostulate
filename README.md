# LeanCodeParallel

[![Lean Action CI](https://github.com/Richiesutie/LeanCodeParallel/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Richiesutie/LeanCodeParallel/actions/workflows/lean_action_ci.yml)

Formal proofs, in Lean 4 with Mathlib, about Euclid's parallel postulate:

* it holds in the Euclidean plane;
* it fails in the Beltrami–Klein model of the hyperbolic plane, in Playfair's form and in
  Euclid's own form with angles;
* it is independent of Hilbert's axioms of incidence, order, congruence and continuity.

There is no `sorry`, and every main theorem depends only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`. The build checks this.

## Main result

```lean
/-- The parallel postulate is independent of Hilbert's axioms, with continuity. -/
theorem Hilbert.playfair_independent_continuous :
    (∃ (P L : Type) (H : Hilbert.HilbertPlane P L), H.Archimedes ∧ H.Dedekind ∧ H.Playfair) ∧
      ∃ (P L : Type) (H : Hilbert.HilbertPlane P L), H.Archimedes ∧ H.Dedekind ∧ ¬ H.Playfair
```

`Hilbert.HilbertPlane P L` bundles points `P`, lines `L`, betweenness, and congruence of
segments and of angles, with Hilbert's axioms of incidence (I1–I3), order (B1–B4, with Pasch's
axiom as B4) and congruence (C1–C6). `Archimedes` and `Dedekind` are the axioms of continuity,
and `Playfair` states that through a point off a line there is at most one parallel. The two
witnesses are `euclidPlane`, where Playfair's axiom holds, and `kleinPlane`, where it fails.
The same result without continuity is `Hilbert.playfair_independent`.

## For reviewers

### What has to be read

The statement of the main theorem uses only the definitions in
[`LeanCodeParallel/Hilbert/Defs.lean`](LeanCodeParallel/Hilbert/Defs.lean), a file of 118 lines
that imports only `Mathlib.Data.Set.Basic`: `Collinear`, `OnRay`, `SameSide`, the structure
`HilbertPlane`, `Parallel`, `Playfair`, `Archimedes` and `Dedekind`. To trust the theorem, it is
enough to check that these say what Hilbert's axioms say. The rest of `Hilbert/` and all of
`HyperbolicPlane/` build the two models, which are witnesses: Lean checks that they meet the
definitions, so they need not be read for that.

Choices in these definitions that deserve a look:

* A segment is a pair of points, and an angle `ABC` is a triple with its vertex in the middle.
  The fields `seg_swap`, `ang_swap` and `ang_rays` make congruence blind to the order of the
  ends of a segment, the order of the two rays of an angle, and the points chosen on the rays.
* B4 is Pasch's axiom, as in Hilbert, rather than Hartshorne's plane separation.
* Dedekind's axiom stands in for Hilbert's axiom of completeness (see below).
* Two lines are parallel when they have no point in common, and Playfair's axiom says there is
  at most one parallel through a point off a line.

The other results are stated with definitions from the `HyperbolicPlane` files: the plane
`plane κ`, its lines `IsLine` and `Between` (`Plane.lean`), `apart` (`Motions.lean`), the angle
`kleinAngle` (`Angles.lean`), Klein's metric `kleinMetric` (`Metric.lean`), the curvature
`gaussCurvature`, which is Brioschi's formula (`Curvature.lean`), and the distance `kleinDist`,
an infimum of path lengths (`Distance.lean`). Each file begins with a header that lists its
contents; `HyperbolicPlane.lean` and `Hilbert.lean` also say what is assumed and what is not
formalised.

### What is checked automatically

`lake build`, which the CI runs on every push:

* builds the library with Mathlib's standard linter set (`weak.linter.mathlibStandardSet`) and
  with `autoImplicit = false`, with no warnings;
* runs [`LeanCodeParallel/AxiomCheck.lean`](LeanCodeParallel/AxiomCheck.lean), which checks with
  `#guard_msgs` that each of 22 main theorems depends on exactly `propext`, `Classical.choice`
  and `Quot.sound`, so the build fails if any of them ever picks up `sorry` or another axiom.

Batteries' environment linters also pass: `#lint in LeanCodeParallel` reports no problems in
412 declarations.

## Other results

| Result | Lean name |
|---|---|
| Playfair's axiom in the plane of pairs of a field | `ThreeDimensions.playfair_exists`, `ThreeDimensions.playfair_unique_through` |
| Euclid's fifth postulate in `ℝ²`, with Mathlib's angles, and its converse | `ThreeDimensions.euclid_fifth_either_side`, `ThreeDimensions.meet_iff_angles_either_side` |
| Infinitely many parallels through a point in the Klein disc | `HyperbolicPlane.hyperbolic_parallel_property` |
| One parallel exactly when the curvature bound is not negative | `HyperbolicPlane.one_parallel_iff_bound` |
| Euclid's fifth postulate, with Klein angles, fails in the Klein disc | `HyperbolicPlane.not_euclidFifth` |
| The motions of the disc keep Klein's metric (via Mathlib's `fderiv`) | `HyperbolicPlane.shift_kleinMetric_fderiv`, `HyperbolicPlane.rot_kleinMetric_fderiv` |
| The motions reach every point, so `kleinAngle` is the unique invariant angle | `HyperbolicPlane.exists_motion_to_centre`, `HyperbolicPlane.kleinAngle_unique` |
| The Gaussian curvature of Klein's metric is `κ` | `HyperbolicPlane.kleinMetric_curvature` |
| Klein's distance: `apart = sinh² (√-κ d) / -κ` | `HyperbolicPlane.kleinDist_eq_arsinh`, `HyperbolicPlane.apart_eq_sinh_kleinDist` |
| Hyperbolic law of cosines | `HyperbolicPlane.law_of_cosines` |
| Hilbert's congruence axioms C1–C6 in the Klein disc | `HyperbolicPlane.segment_construction`, `segment_addition`, `angle_construction`, `side_angle_side`, … |
| The Euclidean and Klein planes as Hilbert planes | `Hilbert.model`, `Hilbert.euclidPlane`, `Hilbert.kleinPlane` |
| Archimedes' axiom and Dedekind's axiom in both planes | `Hilbert.model_archimedes`, `Hilbert.model_dedekind` |

## Layout

```
LeanCodeParallel.lean                 root of the library: imports every module
LeanCodeParallel/
  Basic.lean                          dimensions, the cross product and the figure (namespace Pairs)
  ThreeDimensions.lean                the plane of pairs of numbers, and the parallel postulate there
  HyperbolicPlane.lean                overview of the plane of a curvature bound κ
  HyperbolicPlane/
    Plane.lean                        lines, order and parallels (H1–H7)
    Motions.lean                      steps, the two motions, and `apart` (H8, H9)
    Angles.lean                       Klein's inner product and angle (H13, H15)
    Metric.lean                       Klein's metric, kept by the motions (H16)
    Curvature.lean                    its curvature is κ (H17)
    Distance.lean                     Klein's distance (H18)
    Congruence.lean                   Hilbert's axioms of congruence (H19)
    LeaningFigure.lean                Euclid's fifth postulate fails under the bound -1 (H10, H14)
  Hilbert.lean                        overview of the Hilbert planes (namespace Hilbert)
  Hilbert/
    Defs.lean                         the axioms: all that the main theorem's statement uses
    Model.lean                        the plane of a bound as a Hilbert plane
    Continuity.lean                   Archimedes' axiom and Dedekind's axiom there
    Independence.lean                 the two planes, and the independence theorems
  AxiomCheck.lean                     the axiom checks of the main theorems
.github/workflows/lean_action_ci.yml  CI: builds the project with leanprover/lean-action
```

`Basic.lean` and `Hilbert/Defs.lean` import only Mathlib. `ThreeDimensions.lean` and the
`HyperbolicPlane` files build on `Basic.lean`, and the `Hilbert` files on both.

## Building

You need [elan](https://github.com/leanprover/elan), which installs the right version of Lean.
Then, in this folder:

```bash
lake exe cache get
```

```bash
lake build
```

The first command downloads a compiled Mathlib. The second builds the library and runs the
axiom checks, which takes about a minute on a laptop.

* Lean: `v4.35.0-rc3` (see `lean-toolchain`)
* Mathlib: tag `v4.35.0-rc3`; `lake-manifest.json` pins the exact commit

## Scope and limitations

* **Dedekind's axiom stands in for Hilbert's axiom of completeness.** Hilbert's axiom V.2 says
  that the points of a line cannot be extended while the other axioms still hold, which is a
  statement about all models rather than an axiom inside one plane. The continuity axioms here
  are Archimedes' axiom (Hilbert's V.1) and Dedekind's axiom, as in Hartshorne. Their relation
  to Hilbert's V.2 is not formalised.
* **B4 is Pasch's axiom**, as in Hilbert. Hartshorne uses plane separation instead; the two are
  equivalent given the other axioms, which is not formalised here.
* **Curvature and distance are defined in coordinates.** Gaussian curvature is Brioschi's
  formula (checked against the Poincaré half-plane, where it gives `-1`), and Klein's distance
  is the infimum of lengths of `C¹` paths. Neither is connected to Mathlib's Riemannian geometry
  (`riemannianEDist`).
* **Euclid's fifth postulate with angles** is refuted for the bound `-1` only.
* **Own coordinates rather than Mathlib's geometry.** The development works in `ℝ × ℝ` with its
  own vocabulary, not with Mathlib's `EuclideanSpace`, `Sbtw` or the upper half-plane `ℍ`, so it
  is a standalone project rather than a candidate for Mathlib as it stands.

## License

Released under the Apache License 2.0; see `LICENSE`.
