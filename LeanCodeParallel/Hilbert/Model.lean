/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import LeanCodeParallel.HyperbolicPlane
import LeanCodeParallel.Hilbert.Defs

/-!
# The plane of a bound as a Hilbert plane

`model κ` makes a Hilbert plane of the plane of a bound `κ` that is not positive: its points and
its lines, its `Between`, `apart` for segments and `kleinAngle` for angles.

## Contents

* the model: `Pt`, `Ln`, `mlies`, `mbtw`, `msegCong`, `mangCong`, `lineThrough`, `model_I1` to
  `model_I3`, `model_B1` to `model_B4`, `model_onRay`, `model_onRay_of`, `model_C1`,
  `model_side_ne_zero`, `model_sameSide_iff`, `model_C4`, `model_C6`, `model`
-/

namespace Hilbert

open Pairs HyperbolicPlane

open Real

/-! ## The plane of a bound as a Hilbert plane -/

/-- The points of the plane of the bound `κ`. -/
abbrev Pt (κ : ℝ) := {p : ℝ × ℝ // p ∈ plane κ}

/-- The lines of the plane of the bound `κ`. -/
abbrev Ln (κ : ℝ) := {S : Set (ℝ × ℝ) // IsLine (plane κ) S}

/-- A point lies on a line. -/
def mlies (κ : ℝ) (p : Pt κ) (l : Ln κ) : Prop := p.1 ∈ l.1

/-- Betweenness is the file's `Between`. -/
def mbtw (κ : ℝ) (A B C : Pt κ) : Prop := Between A.1 B.1 C.1

/-- Two segments are congruent when `apart` is the same for both. -/
def msegCong (κ : ℝ) (A B C D : Pt κ) : Prop := apart κ A.1 B.1 = apart κ C.1 D.1

/-- The angle `ABC` is congruent to `DEF` when `kleinAngle` is the same at `B` and at `E`. -/
def mangCong (κ : ℝ) (A B C D E F : Pt κ) : Prop :=
  kleinAngle κ B.1 A.1 C.1 = kleinAngle κ E.1 D.1 F.1

/-- The line through two different points of the plane. -/
def lineThrough {κ : ℝ} (A B : Pt κ) (h : A.1 ≠ B.1) : Ln κ :=
  ⟨(Dim.mk A.1 B.1).points ∩ plane κ, ⟨Dim.mk A.1 B.1, h, rfl, A.1, (Dim.mk _ _).zero_mem, A.2⟩⟩

theorem lies_lineThrough_left {κ : ℝ} (A B : Pt κ) (h : A.1 ≠ B.1) :
    mlies κ A (lineThrough A B h) := ⟨(Dim.mk _ _).zero_mem, A.2⟩

theorem lies_lineThrough_right {κ : ℝ} (A B : Pt κ) (h : A.1 ≠ B.1) :
    mlies κ B (lineThrough A B h) := ⟨(Dim.mk _ _).one_mem, B.2⟩

theorem model_I1 (κ : ℝ) : ∀ A B : Pt κ, A ≠ B → ∃! l, mlies κ A l ∧ mlies κ B l := by
  intro A B hAB
  obtain ⟨S, ⟨hS, hA, hB⟩, huniq⟩ :=
    line_through (plane κ) A.2 B.2 (fun h => hAB (Subtype.ext h))
  exact ⟨⟨S, hS⟩, ⟨hA, hB⟩, fun l hl => Subtype.ext (huniq l.1 ⟨l.2, hl.1, hl.2⟩)⟩

theorem model_I2 (κ : ℝ) : ∀ l : Ln κ, ∃ A B : Pt κ, A ≠ B ∧ mlies κ A l ∧ mlies κ B l := by
  intro l
  obtain ⟨A, B, hAB, hA, hB⟩ := l.2.two_points (plane_openAlong κ)
  exact ⟨⟨A, l.2.subset_plane hA⟩, ⟨B, l.2.subset_plane hB⟩,
    fun h => hAB (congrArg Subtype.val h), hA, hB⟩

theorem model_I3 (κ : ℝ) : ∃ A B C : Pt κ, ¬ Collinear (mlies κ) A B C := by
  obtain ⟨A, B, C, hA, hB, hC, h⟩ := exists_three_points κ
  exact ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩, fun ⟨l, h1, h2, h3⟩ => h l.1 l.2 ⟨h1, h2, h3⟩⟩

theorem model_B1 (κ : ℝ) : ∀ A B C : Pt κ, mbtw κ A B C →
    A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ Collinear (mlies κ) A B C ∧ mbtw κ C B A := by
  intro A B C h
  obtain ⟨h1, h2, h3⟩ := Between.ne h
  exact ⟨fun e => h1 (congrArg Subtype.val e), fun e => h2 (congrArg Subtype.val e),
    fun e => h3 (congrArg Subtype.val e),
    ⟨lineThrough A C h3, lies_lineThrough_left A C h3, ⟨Between.mem h, B.2⟩,
      lies_lineThrough_right A C h3⟩, Between.symm h⟩

theorem model_B2 (κ : ℝ) : ∀ A B : Pt κ, A ≠ B → ∃ C, mbtw κ A B C := by
  intro A B hAB
  obtain ⟨C, hC, h⟩ := exists_beyond κ (fun e => hAB (Subtype.ext e)) B.2
  exact ⟨⟨C, hC⟩, h⟩

theorem model_B3 (κ : ℝ) : ∀ A B C : Pt κ, A ≠ B → B ≠ C → A ≠ C → Collinear (mlies κ) A B C →
    (mbtw κ A B C ∨ mbtw κ B A C ∨ mbtw κ A C B) ∧ ¬ (mbtw κ A B C ∧ mbtw κ B A C) ∧
      ¬ (mbtw κ A B C ∧ mbtw κ A C B) ∧ ¬ (mbtw κ B A C ∧ mbtw κ A C B) := by
  intro A B C hAB hBC hAC ⟨l, hA, hB, hC⟩
  have hAC' : A.1 ≠ C.1 := fun e => hAC (Subtype.ext e)
  have hBm : B.1 ∈ (Dim.mk A.1 C.1).points := by
    have h : B.1 ∈ l.1 := hB
    rw [IsLine.eq_through l.2 hA hC hAC'] at h
    exact h.1
  exact ⟨between_trichotomy (fun e => hAB (Subtype.ext e)) (fun e => hBC (Subtype.ext e)) hAC'
      hBm, fun ⟨h1, h2⟩ => Between.not_left h1 h2, fun ⟨h1, h2⟩ => Between.not_right h1 h2,
    fun ⟨h1, h2⟩ => Between.not_right h1 (Between.symm h2)⟩

theorem model_B4 (κ : ℝ) : ∀ (A B C : Pt κ) (l : Ln κ), ¬ Collinear (mlies κ) A B C →
    ¬ mlies κ A l → ¬ mlies κ B l → ¬ mlies κ C l →
    (∃ D, mlies κ D l ∧ mbtw κ A D B) → ∃ E, mlies κ E l ∧ (mbtw κ A E C ∨ mbtw κ B E C) := by
  intro A B C l _ hA hB hC ⟨D, hD, hAD⟩
  obtain ⟨M, hM, hl, -⟩ := l.2
  have hnot : ∀ X : Pt κ, ¬ mlies κ X l → X.1 ∉ M.points := fun X hX hm =>
    hX (by change X.1 ∈ l.1; rw [hl]; exact ⟨hm, X.2⟩)
  have hDm : D.1 ∈ M.points := by
    have h : D.1 ∈ l.1 := hD
    rw [hl] at h
    exact h.1
  obtain ⟨Y, hYM, hY, hYb⟩ :=
    pasch κ A.2 B.2 C.2 M hM (hnot A hA) (hnot B hB) (hnot C hC) hDm hAD
  exact ⟨⟨Y, hY⟩, by change Y ∈ l.1; rw [hl]; exact ⟨hYM, hY⟩, hYb⟩

/-- A point on a ray, as Hilbert has it, in the plane of a bound. -/
theorem model_onRay {κ : ℝ} {O A X : Pt κ} (h : Hilbert.OnRay (mbtw κ) O A X) :
    HyperbolicPlane.OnRay O.1 A.1 X.1 :=
  onRay_of_between (h.imp (congrArg Subtype.val) id)

theorem model_onRay_of {κ : ℝ} {O A X : Pt κ} (hOA : O.1 ≠ A.1)
    (h : HyperbolicPlane.OnRay O.1 A.1 X.1) : Hilbert.OnRay (mbtw κ) O A X :=
  (between_of_onRay hOA h).imp Subtype.ext id

theorem model_C1 (κ : ℝ) (hκ : κ ≤ 0) : ∀ A B C R : Pt κ, A ≠ B → C ≠ R →
    ∃! D, Hilbert.OnRay (mbtw κ) C R D ∧ msegCong κ A B C D := by
  intro A B C R hAB hCR
  have hCR' : C.1 ≠ R.1 := fun e => hCR (Subtype.ext e)
  obtain ⟨X, ⟨hX, hray, hap⟩, huniq⟩ :=
    segment_construction_apart hκ A.2 B.2 C.2 (fun e => hAB (Subtype.ext e)) hCR'
  refine ⟨⟨X, hX⟩, ⟨model_onRay_of hCR' hray, hap⟩, ?_⟩
  rintro D ⟨hD, hapD⟩
  exact Subtype.ext (huniq D.1 ⟨D.2, model_onRay hD, hapD⟩)

/-- Three points of the plane that are not on one line give a side that is not 0. -/
theorem model_side_ne_zero {κ : ℝ} {A B C : Pt κ} (h : ¬ Collinear (mlies κ) A B C) :
    (Dim.mk B.1 A.1).side C.1 ≠ 0 := by
  intro hs
  apply h
  by_cases hBA : B.1 = A.1
  · by_cases hAC : A.1 = C.1
    · have hne : A.1 ≠ (A.1.1 + 1, A.1.2) := by
        intro e
        have := congrArg Prod.fst e
        simp at this
      refine ⟨⟨(Dim.mk A.1 (A.1.1 + 1, A.1.2)).points ∩ plane κ,
        ⟨_, hne, rfl, A.1, (Dim.mk _ _).zero_mem, A.2⟩⟩, ⟨(Dim.mk _ _).zero_mem, A.2⟩, ?_, ?_⟩
      · change B.1 ∈ _
        rw [hBA]
        exact ⟨(Dim.mk _ _).zero_mem, A.2⟩
      · change C.1 ∈ _
        rw [← hAC]
        exact ⟨(Dim.mk _ _).zero_mem, A.2⟩
    · refine ⟨lineThrough A C hAC, lies_lineThrough_left A C hAC, ?_,
        lies_lineThrough_right A C hAC⟩
      change B.1 ∈ _
      rw [hBA]
      exact ⟨(Dim.mk _ _).zero_mem, A.2⟩
  · exact ⟨lineThrough B A hBA, lies_lineThrough_right B A hBA, lies_lineThrough_left B A hBA,
      ⟨Dim.mem_points_of_side_eq_zero _ hBA C.1 hs, C.2⟩⟩

/-- Hilbert's sides of a line, in the plane of a bound, are the signs of `side`. -/
theorem model_sameSide_iff {κ : ℝ} {D F : Pt κ} {l : Ln κ} (hD : mlies κ D l) (hF : mlies κ F l)
    (hDF : D.1 ≠ F.1) (E G : Pt κ) :
    Hilbert.SameSide (mlies κ) (mbtw κ) l E G ↔ HyperbolicPlane.SameSide D.1 F.1 E.1 G.1 := by
  have hl := IsLine.eq_through l.2 hD hF hDF
  have hmem : ∀ X : Pt κ, mlies κ X l ↔ (Dim.mk D.1 F.1).side X.1 = 0 := by
    intro X
    change X.1 ∈ l.1 ↔ _
    rw [hl]
    constructor
    · rintro ⟨h, -⟩
      exact Dim.side_eq_zero_of_mem _ h
    · intro h
      exact ⟨Dim.mem_points_of_side_eq_zero _ hDF X.1 h, X.2⟩
  constructor
  · rintro ⟨hE, hG, hno⟩
    have hE' : (Dim.mk D.1 F.1).side E.1 ≠ 0 := fun h => hE ((hmem E).mpr h)
    have hG' : (Dim.mk D.1 F.1).side G.1 ≠ 0 := fun h => hG ((hmem G).mpr h)
    change 0 < _ * _
    rcases lt_trichotomy ((Dim.mk D.1 F.1).side E.1 * (Dim.mk D.1 F.1).side G.1) 0 with h | h | h
    · obtain ⟨Y, hYM, hY, hYb⟩ := crosses κ (Dim.mk D.1 F.1) hDF E.2 G.2 h
      exact absurd ⟨⟨Y, hY⟩, (hmem ⟨Y, hY⟩).mpr (Dim.side_eq_zero_of_mem _ hYM), hYb⟩ hno
    · exact absurd h (mul_ne_zero hE' hG')
    · exact h
  · intro h
    have h' : 0 < (Dim.mk D.1 F.1).side E.1 * (Dim.mk D.1 F.1).side G.1 := h
    have hE' : (Dim.mk D.1 F.1).side E.1 ≠ 0 := by
      intro e
      rw [e, zero_mul] at h'
      exact lt_irrefl 0 h'
    have hG' : (Dim.mk D.1 F.1).side G.1 ≠ 0 := by
      intro e
      rw [e, mul_zero] at h'
      exact lt_irrefl 0 h'
    refine ⟨fun hm => hE' ((hmem E).mp hm), fun hm => hG' ((hmem G).mp hm), ?_⟩
    rintro ⟨C, hCl, ⟨-, u, hu0, hu1, hC⟩⟩
    have h0 := (hmem C).mp hCl
    rw [← hC, Dim.side_through] at h0
    have h1 := congrArg (· * (Dim.mk D.1 F.1).side E.1) h0
    simp only [zero_mul] at h1
    have h2 : 0 < (1 - u) * (Dim.mk D.1 F.1).side E.1 ^ 2 :=
      mul_pos (sub_pos.mpr hu1) (by positivity)
    have h3 := mul_pos hu0 h'
    nlinarith

theorem model_C4 (κ : ℝ) : ∀ (A B C D F G : Pt κ) (l : Ln κ), ¬ Collinear (mlies κ) A B C →
    D ≠ F → mlies κ D l → mlies κ F l → ¬ mlies κ G l →
    (∃ E, Hilbert.SameSide (mlies κ) (mbtw κ) l E G ∧ mangCong κ A B C E D F) ∧
    ∀ E E', Hilbert.SameSide (mlies κ) (mbtw κ) l E G → mangCong κ A B C E D F →
      Hilbert.SameSide (mlies κ) (mbtw κ) l E' G → mangCong κ A B C E' D F →
      Hilbert.OnRay (mbtw κ) D E E' := by
  intro A B C D F G l hABC hDF hD hF hG
  have hDF' : D.1 ≠ F.1 := fun e => hDF (Subtype.ext e)
  have hl := IsLine.eq_through l.2 hD hF hDF'
  have hGs : (Dim.mk D.1 F.1).side G.1 ≠ 0 := by
    intro h
    apply hG
    change G.1 ∈ l.1
    rw [hl]
    exact ⟨Dim.mem_points_of_side_eq_zero _ hDF' G.1 h, G.2⟩
  obtain ⟨hex, huniq⟩ := angle_construction B.2 D.2 (model_side_ne_zero hABC) hDF' hGs
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hE, hs, ha⟩ := hex
    refine ⟨⟨E, hE⟩, (model_sameSide_iff hD hF hDF' ⟨E, hE⟩ G).mpr hs, ?_⟩
    change kleinAngle κ B.1 A.1 C.1 = kleinAngle κ D.1 E F.1
    rw [kleinAngle_comm κ D.1 E F.1, ha]
  · intro E E' hs ha hs' ha'
    have hDE : D.1 ≠ E.1 := by
      intro e
      apply hs.1
      rw [show E = D from (Subtype.ext e).symm]
      exact hD
    unfold mangCong at ha ha'
    have hr := huniq E.1 E'.1 E.2 ((model_sameSide_iff hD hF hDF' E G).mp hs)
      (by rw [kleinAngle_comm]; exact ha.symm) E'.2 ((model_sameSide_iff hD hF hDF' E' G).mp hs')
      (by rw [kleinAngle_comm]; exact ha'.symm)
    exact model_onRay_of hDE hr

theorem model_C6 (κ : ℝ) (hκ : κ ≤ 0) : ∀ A B C D E F : Pt κ, ¬ Collinear (mlies κ) A B C →
    ¬ Collinear (mlies κ) D E F → msegCong κ A B D E → msegCong κ A C D F →
    mangCong κ B A C E D F →
    msegCong κ B C E F ∧ mangCong κ A B C D E F ∧ mangCong κ A C B D F E := by
  intro A B C D E F h1 h2 e1 e2 e3
  obtain ⟨hBA, hCB, hCA⟩ := ne_of_side_ne_zero (model_side_ne_zero h1)
  obtain ⟨hED, hFE, hFD⟩ := ne_of_side_ne_zero (model_side_ne_zero h2)
  exact sas_apart hκ A.2 B.2 C.2 D.2 E.2 F.2 hBA.symm hCA.symm hCB.symm hED.symm hFD.symm
    hFE.symm e1 e2 e3

/-- **The plane of a bound that is not positive is a Hilbert plane.** -/
noncomputable def model (κ : ℝ) (hκ : κ ≤ 0) : HilbertPlane (Pt κ) (Ln κ) where
  lies := mlies κ
  btw := mbtw κ
  segCong := msegCong κ
  angCong := mangCong κ
  I1 := model_I1 κ
  I2 := model_I2 κ
  I3 := model_I3 κ
  B1 := model_B1 κ
  B2 := model_B2 κ
  B3 := model_B3 κ
  B4 := model_B4 κ
  seg_swap := fun A B => apart_comm κ A.1 B.1
  ang_swap := fun A B C => kleinAngle_comm κ B.1 A.1 C.1
  ang_rays := fun _ _ _ _ _ hA hC => (kleinAngle_onRay (model_onRay hA) (model_onRay hC)).symm
  C1 := model_C1 κ hκ
  C2 := fun _ _ _ _ _ _ h1 h2 => h1.symm.trans h2
  C2_refl := fun _ _ => rfl
  C3 := fun A _ C D _ F h1 h2 h3 h4 => segment_addition_apart hκ A.2 C.2 D.2 F.2 h1 h2 h3 h4
  C4 := model_C4 κ
  C5 := fun _ _ _ _ _ _ _ _ _ h1 h2 => h1.symm.trans h2
  C5_refl := fun _ _ _ => rfl
  C6 := model_C6 κ hκ

end Hilbert
