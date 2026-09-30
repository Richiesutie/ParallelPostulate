# LeanCodeParallel

Formal proofs, in Lean 4 with Mathlib, about Euclid's parallel postulate:

* it holds in the Euclidean plane;
* it fails in the Beltrami–Klein model of the hyperbolic plane, in Playfair's form and in
  Euclid's own form with angles;
* it is independent of Hilbert's axioms of incidence, order, congruence and continuity.

The proofs are complete: there is no `sorry`, and every theorem depends only on Lean's standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Main result

```lean
/-- The parallel postulate is independent of Hilbert's axioms, with continuity. -/
theorem HyperbolicPlane.playfair_independent_continuous :
    (∃ (P L : Type) (H : Hilbert.HilbertPlane P L), H.Archimedes ∧ H.Dedekind ∧ H.Playfair) ∧
      ∃ (P L : Type) (H : Hilbert.HilbertPlane P L), H.Archimedes ∧ H.Dedekind ∧ ¬ H.Playfair
```

`Hilbert.HilbertPlane P L` bundles points `P`, lines `L`, betweenness, and congruence of
segments and of angles, with Hilbert's axioms of incidence (I1–I3), order (B1–B4, with Pasch's
axiom as B4) and congruence (C1–C6). `Archimedes` and `Dedekind` are the axioms of continuity,
and `Playfair` states that through a point off a line there is at most one parallel. The two
witnesses are `euclidPlane`, where Playfair's axiom holds, and `kleinPlane`, where it fails.
The same result without continuity is `HyperbolicPlane.playfair_independent`.

## Other results

| Result | Lean name | File |
|---|---|---|
| Playfair's axiom in the plane of pairs of a field | `ThreeDimensions.playfair_exists`, `ThreeDimensions.playfair_unique_through` | `ThreeDimensions.lean` |
| Euclid's fifth postulate in `ℝ²`, with Mathlib's angles, and its converse | `ThreeDimensions.euclid_fifth_either_side`, `ThreeDimensions.meet_iff_angles_either_side` | `ThreeDimensions.lean` |
| Infinitely many parallels through a point in the Klein disc | `HyperbolicPlane.hyperbolic_parallel_property` | `HyperbolicPlane.lean` |
| One parallel exactly when the curvature bound is not negative | `HyperbolicPlane.one_parallel_iff_bound` | `HyperbolicPlane.lean` |
| Euclid's fifth postulate, with Klein angles, fails in the Klein disc | `HyperbolicPlane.not_euclidFifth` | `HyperbolicPlane.lean` |
| The motions of the disc keep Klein's metric (via Mathlib's `fderiv`) | `HyperbolicPlane.shift_kleinMetric_fderiv`, `HyperbolicPlane.rot_kleinMetric_fderiv` | `HyperbolicPlane.lean` |
| The motions reach every point, so `kleinAngle` is the unique invariant angle | `HyperbolicPlane.exists_motion_to_centre`, `HyperbolicPlane.kleinAngle_unique` | `HyperbolicPlane.lean` |
| The Gaussian curvature of Klein's metric is `κ` | `HyperbolicPlane.kleinMetric_curvature` | `HyperbolicPlane.lean` |
| Klein's distance, as an infimum of path lengths: `apart = sinh² (√-κ d) / -κ` | `HyperbolicPlane.kleinDist_eq_arsinh`, `HyperbolicPlane.apart_eq_sinh_kleinDist` | `HyperbolicPlane.lean` |
| Hyperbolic law of cosines | `HyperbolicPlane.law_of_cosines` | `HyperbolicPlane.lean` |
| Hilbert's congruence axioms C1–C6 in the Klein disc | `HyperbolicPlane.segment_construction`, `segment_addition`, `angle_construction`, `side_angle_side`, … | `HyperbolicPlane.lean` |
| The Euclidean and Klein planes as Hilbert planes | `HyperbolicPlane.model`, `euclidPlane`, `kleinPlane` | `HilbertPlane.lean` |
| Archimedes' axiom and Dedekind's axiom in both planes | `HyperbolicPlane.model_archimedes`, `HyperbolicPlane.model_dedekind` | `HilbertPlane.lean` |

Each file begins with a header that lists its contents and states what it assumes and what it
does not formalise.

## Files

| File | Contents | Imports from this project |
|---|---|---|
| `ThreeDimensions.lean` | The plane of pairs of numbers, and the parallel postulate there | — |
| `HyperbolicPlane.lean` | The plane under a curvature bound `κ`; for `κ < 0` the Klein disc, its metric, curvature, distance, angles and congruence | — |
| `HilbertPlane.lean` | The axioms of a Hilbert plane and of continuity, the two models, and the independence theorems | `HyperbolicPlane` |

Every file is a module at the top level of the project.

## Building

You need [elan](https://github.com/leanprover/elan), which installs the right version of Lean.
Then, in this folder:

```bash
lake exe cache get
```

```bash
lake build
```

The first command downloads a compiled Mathlib. The second checks the three files, which takes
about a minute on a laptop.

* Lean: `v4.35.0-rc3` (see `lean-toolchain`)
* Mathlib: tag `v4.35.0-rc3`; `lake-manifest.json` pins the exact commit

To confirm the axioms a theorem uses, add for example

```lean
#print axioms HyperbolicPlane.playfair_independent_continuous
```

at the end of `HilbertPlane.lean`.

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
* **Not in Mathlib style.** The development uses its own coordinates and vocabulary rather than
  Mathlib's `EuclideanSpace`, `Sbtw` or the upper half-plane `ℍ`.

## License

Released under the Apache License 2.0; see `LICENSE`.
