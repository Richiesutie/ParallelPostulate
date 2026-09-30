/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import LeanCodeParallel.Hilbert.Defs
import LeanCodeParallel.Hilbert.Model
import LeanCodeParallel.Hilbert.Continuity
import LeanCodeParallel.Hilbert.Independence

/-!
# Hilbert planes, and the independence of the parallel postulate

`HilbertPlane P L` is a plane with points `P` and lines `L`, a betweenness, and congruence of
segments and of angles, that meets Hilbert's axioms of incidence (I1 to I3), of order (B1 to
B4) and of congruence (C1 to C6). Playfair's axiom, `HilbertPlane.Playfair`, is not among them.
The axioms of continuity are `HilbertPlane.Archimedes` and `HilbertPlane.Dedekind`.

`model κ` makes a Hilbert plane of the plane of `HyperbolicPlane` under a bound `κ` that
is not positive: its points and its lines, its `Between`, `apart` for segments and `kleinAngle`
for angles. `euclidPlane` is the bound 0 and `kleinPlane` the bound `-1`. Playfair's axiom
holds in the first and fails in the second, so it is independent of the axioms of a Hilbert
plane: `playfair_independent`. Both planes meet Archimedes' axiom and Dedekind's axiom, so it
is independent of these axioms too: `playfair_independent_continuous`.

Everything is in the namespace `Hilbert`.

## Files

* `Hilbert/Defs.lean`: the axioms of a Hilbert plane, Playfair's axiom, and the axioms of
  continuity
* `Hilbert/Model.lean`: the plane of a bound as a Hilbert plane
* `Hilbert/Continuity.lean`: Dedekind's axiom and Archimedes' axiom in that plane
* `Hilbert/Independence.lean`: Euclid's plane and Klein's plane, and the independence

## What is assumed, and what is not formalised

* **The axioms of a Hilbert plane**, as Hartshorne calls it, are those of incidence, order and
  congruence. The axioms of continuity are stated apart, as `Archimedes` and `Dedekind`, and
  both planes meet them.
* **Dedekind's axiom stands for Hilbert's axiom of completeness.** Hilbert's axiom V.2 says that
  the points of a line cannot be extended while the other axioms still hold. It is a statement
  about all the models, not an axiom inside one plane. Dedekind's axiom is the usual axiom in
  its place. That the two are equivalent, given Archimedes' axiom, is not formalised.
* **B4 is Pasch's axiom**, as Hilbert states it. Hartshorne takes plane separation instead.
  Given the other axioms the two are equivalent. That is not formalised.
* **A segment is a pair of points, and an angle is a triple with its vertex in the middle.**
  The fields `seg_swap`, `ang_swap` and `ang_rays` say that congruence does not see the order
  of the ends of a segment, the order of the two rays of an angle, or the points chosen on the
  rays.
* **Not in the style of Mathlib.** In Mathlib the plane would be built on `EuclideanSpace`,
  betweenness would be `Sbtw`, and Klein's distance would be `riemannianEDist`.
-/
