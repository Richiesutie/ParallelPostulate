/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import ParallelPostulate.Hilbert.Continuity

/-!
# The independence of the parallel postulate

`euclidPlane`, the plane of the bound 0, and `kleinPlane`, the plane of the bound `-1`, are
Hilbert planes that meet the axioms of continuity. Playfair's axiom holds in the first and fails
in the second, so it is independent of Hilbert's axioms, with continuity or without it.

## Contents

* the two planes: `euclidPlane`, `kleinPlane`, `euclidPlane_playfair`, `kleinPlane_not_playfair`
* the independence: `playfair_independent`, `playfair_not_consequence`,
  `not_playfair_not_consequence`, `playfair_independent_continuous`
-/

namespace Hilbert

open Pairs HyperbolicPlane

/-- **Euclid's plane**: the plane of the bound 0. -/
noncomputable abbrev euclidPlane : HilbertPlane (Pt 0) (Ln 0) := model 0 le_rfl

/-- **Klein's plane**: the plane of the bound `-1`. -/
noncomputable abbrev kleinPlane : HilbertPlane (Pt (-1)) (Ln (-1)) := model (-1) (by norm_num)

/-- **Playfair's axiom holds in Euclid's plane.** -/
theorem euclidPlane_playfair : euclidPlane.Playfair := by
  intro l A hA m m' hm hml hm' hm'l
  have key : ∀ n : Ln 0, euclidPlane.lies A n → euclidPlane.Parallel n l → n.1 ∩ l.1 = ∅ := by
    intro n _ hnl
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨hxn, hxl⟩
    exact hnl ⟨⟨x, n.2.subset_plane hxn⟩, hxn, hxl⟩
  obtain ⟨M, -, huniq⟩ := euclid_one_parallel le_rfl l.2 hA
  have e1 := huniq m.1 ⟨m.2, hm, key m hm hml⟩
  have e2 := huniq m'.1 ⟨m'.2, hm', key m' hm' hm'l⟩
  exact Subtype.ext (e1.trans e2.symm)

/-- **Playfair's axiom fails in Klein's plane.** -/
theorem kleinPlane_not_playfair : ¬ kleinPlane.Playfair := by
  intro h
  obtain ⟨S, P, hS, hP, hPS⟩ := plane_exists_line_and_point (-1 : ℝ)
  obtain ⟨M₁, M₂, hne, ⟨h₁, hP₁, e₁⟩, ⟨h₂, hP₂, e₂⟩⟩ :=
    hyperbolic_two_parallels (by norm_num : (-1 : ℝ) < 0) hS hP hPS
  have par : ∀ {M : Set (ℝ × ℝ)} (hM : IsLine (plane (-1)) M), M ∩ S = ∅ →
      kleinPlane.Parallel ⟨M, hM⟩ ⟨S, hS⟩ := by
    intro M hM hMS ⟨A, hAM, hAS⟩
    have hA : A.1 ∈ M ∩ S := ⟨hAM, hAS⟩
    rw [hMS] at hA
    exact hA
  have := h ⟨S, hS⟩ ⟨P, hP⟩ hPS ⟨M₁, h₁⟩ ⟨M₂, h₂⟩ hP₁ (par h₁ e₁) hP₂ (par h₂ e₂)
  exact hne (congrArg Subtype.val this)

/-- **The parallel postulate is independent of the axioms of a Hilbert plane.** There is a
Hilbert plane in which Playfair's axiom holds, and one in which it fails. -/
theorem playfair_independent :
    (∃ (P L : Type) (H : HilbertPlane P L), H.Playfair) ∧
      ∃ (P L : Type) (H : HilbertPlane P L), ¬ H.Playfair :=
  ⟨⟨_, _, euclidPlane, euclidPlane_playfair⟩, ⟨_, _, kleinPlane, kleinPlane_not_playfair⟩⟩

/-- Playfair's axiom does not follow from the axioms of a Hilbert plane. -/
theorem playfair_not_consequence : ¬ ∀ (P L : Type) (H : HilbertPlane P L), H.Playfair :=
  fun h => kleinPlane_not_playfair (h _ _ kleinPlane)

/-- Nor does its negation. -/
theorem not_playfair_not_consequence : ¬ ∀ (P L : Type) (H : HilbertPlane P L), ¬ H.Playfair :=
  fun h => h _ _ euclidPlane euclidPlane_playfair

/-! ## The independence, with continuity -/

/-- **The parallel postulate is independent of Hilbert's axioms, with continuity.** Both planes
meet Archimedes' axiom and Dedekind's axiom; Playfair's axiom holds in the one and fails in
the other. -/
theorem playfair_independent_continuous :
    (∃ (P L : Type) (H : HilbertPlane P L), H.Archimedes ∧ H.Dedekind ∧ H.Playfair) ∧
      ∃ (P L : Type) (H : HilbertPlane P L), H.Archimedes ∧ H.Dedekind ∧ ¬ H.Playfair :=
  ⟨⟨_, _, euclidPlane, model_archimedes 0 le_rfl, model_dedekind 0 le_rfl, euclidPlane_playfair⟩,
    ⟨_, _, kleinPlane, model_archimedes (-1) (by norm_num), model_dedekind (-1) (by norm_num),
      kleinPlane_not_playfair⟩⟩

end Hilbert
