import HyperbolicPlane

/-!
# Hilbert planes, and the independence of the parallel postulate

`HilbertPlane P L` is a plane with points `P` and lines `L`, a betweenness, and congruence of
segments and of angles, that meets Hilbert's axioms of incidence (I1 to I3), of order (B1 to
B4) and of congruence (C1 to C6). Playfair's axiom, `HilbertPlane.Playfair`, is not among them.

`model κ` makes a Hilbert plane of the plane of `HyperbolicPlane.lean` under a bound `κ` that
is not positive: its points and its lines, its `Between`, `apart` for segments and `kleinAngle`
for angles. `euclidPlane` is the bound 0 and `kleinPlane` the bound `-1`. Playfair's axiom
holds in the first and fails in the second, so it is independent of the axioms of a Hilbert
plane: `playfair_independent`.

Checked with Lean `v4.35.0-rc3` and Mathlib at the matching tag. It imports
`HyperbolicPlane.lean`. Every theorem uses only Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Contents

| What | Lean |
|---|---|
| the axioms | `Hilbert.HilbertPlane`, `Hilbert.Collinear`, `Hilbert.OnRay`, `Hilbert.SameSide` |
| Playfair's axiom | `HilbertPlane.Parallel`, `HilbertPlane.Playfair` |
| rays, and the order of three points on a line | `onRay_of_between`, `between_of_onRay`, `between_trichotomy`, `ne_of_side_ne_zero`, `IsLine.subset_plane`, `IsLine.eq_through` |
| Euclid's plane, with `apart` | `mem_plane_zero`, `apart_zero_nonneg`, `apart_zero_eq_kleinInner`, `euclid_segment_construction`, `euclid_sqrt_apart_add`, `euclid_segment_addition`, `euclid_law_of_cosines`, `euclid_sas` |
| C1, C3 and C6 with `apart`, under a bound that is not positive | `apart_eq_iff_kleinDist_eq`, `segment_construction_apart`, `segment_addition_apart`, `sas_apart` |
| the model | `Pt`, `Ln`, `mlies`, `mbtw`, `msegCong`, `mangCong`, `lineThrough`, `model_I1` to `model_I3`, `model_B1` to `model_B4`, `model_onRay`, `model_onRay_of`, `model_C1`, `model_side_ne_zero`, `model_sameSide_iff`, `model_C4`, `model_C6`, `model` |
| the two planes, and the independence | `euclidPlane`, `kleinPlane`, `euclidPlane_playfair`, `kleinPlane_not_playfair`, `playfair_independent`, `playfair_not_consequence`, `not_playfair_not_consequence` |

## What is assumed, and what is not formalised

* **The axioms are those of a Hilbert plane**, as Hartshorne calls it: incidence, order and
  congruence. The axioms of continuity are not among them. Both planes meet them, since their
  numbers are the real numbers, but that is not formalised, and neither is the independence
  of Playfair's axiom from the axioms with continuity added.
* **B4 is Pasch's axiom**, as Hilbert states it. Hartshorne takes plane separation instead.
  Given the other axioms the two are equivalent. That is not formalised.
* **A segment is a pair of points, and an angle is a triple with its vertex in the middle.**
  The fields `seg_swap`, `ang_swap` and `ang_rays` say that congruence does not see the order
  of the ends of a segment, the order of the two rays of an angle, or the points chosen on the
  rays.
* **This is a sketch, not in the style of a library.** In Mathlib the plane would be built on
  `EuclideanSpace`, betweenness would be `Sbtw`, and Klein's distance would be
  `riemannianEDist`.
-/

namespace Hilbert

variable {P L : Type*}

/-- Three points on one line. -/
def Collinear (lies : P → L → Prop) (A B C : P) : Prop :=
  ∃ l, lies A l ∧ lies B l ∧ lies C l

/-- `C` is on the ray from `A` through `B`, and is not `A`. -/
def OnRay (btw : P → P → P → Prop) (A B C : P) : Prop :=
  C = B ∨ btw A C B ∨ btw A B C

/-- `A` and `B` are on the same side of `l`: neither is on `l`, and no point of `l` is between
them. -/
def SameSide (lies : P → L → Prop) (btw : P → P → P → Prop) (l : L) (A B : P) : Prop :=
  ¬ lies A l ∧ ¬ lies B l ∧ ¬ ∃ C, lies C l ∧ btw A C B

/-- **A Hilbert plane**: Hilbert's axioms of incidence, order and congruence. A segment is a
pair of points and an angle `ABC` is a triple with its vertex `B` in the middle; the fields
`seg_swap`, `ang_swap` and `ang_rays` say that congruence does not see the order of the ends of a
segment, the order of the two rays of an angle, or the points chosen on the rays. -/
structure HilbertPlane (P L : Type*) where
  /-- The point lies on the line. -/
  lies : P → L → Prop
  /-- `btw A B C`: `B` is between `A` and `C`. -/
  btw : P → P → P → Prop
  /-- `segCong A B C D`: the segment `AB` is congruent to the segment `CD`. -/
  segCong : P → P → P → P → Prop
  /-- `angCong A B C D E F`: the angle `ABC`, at `B`, is congruent to the angle `DEF`, at `E`. -/
  angCong : P → P → P → P → P → P → Prop
  I1 : ∀ A B : P, A ≠ B → ∃! l, lies A l ∧ lies B l
  I2 : ∀ l : L, ∃ A B : P, A ≠ B ∧ lies A l ∧ lies B l
  I3 : ∃ A B C : P, ¬ Collinear lies A B C
  B1 : ∀ A B C : P, btw A B C → A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ Collinear lies A B C ∧ btw C B A
  B2 : ∀ A B : P, A ≠ B → ∃ C, btw A B C
  B3 : ∀ A B C : P, A ≠ B → B ≠ C → A ≠ C → Collinear lies A B C →
    (btw A B C ∨ btw B A C ∨ btw A C B) ∧ ¬ (btw A B C ∧ btw B A C) ∧
      ¬ (btw A B C ∧ btw A C B) ∧ ¬ (btw B A C ∧ btw A C B)
  B4 : ∀ (A B C : P) (l : L), ¬ Collinear lies A B C → ¬ lies A l → ¬ lies B l → ¬ lies C l →
    (∃ D, lies D l ∧ btw A D B) → ∃ E, lies E l ∧ (btw A E C ∨ btw B E C)
  seg_swap : ∀ A B : P, segCong A B B A
  ang_swap : ∀ A B C : P, angCong A B C C B A
  ang_rays : ∀ A B C A' C' : P, OnRay btw B A A' → OnRay btw B C C' → angCong A B C A' B C'
  C1 : ∀ A B C R : P, A ≠ B → C ≠ R → ∃! D, OnRay btw C R D ∧ segCong A B C D
  C2 : ∀ A B C D E F : P, segCong A B C D → segCong A B E F → segCong C D E F
  C2_refl : ∀ A B : P, segCong A B A B
  C3 : ∀ A B C D E F : P, btw A B C → btw D E F → segCong A B D E → segCong B C E F →
    segCong A C D F
  C4 : ∀ (A B C D F G : P) (l : L), ¬ Collinear lies A B C → D ≠ F → lies D l → lies F l →
    ¬ lies G l →
    (∃ E, SameSide lies btw l E G ∧ angCong A B C E D F) ∧
    ∀ E E', SameSide lies btw l E G → angCong A B C E D F → SameSide lies btw l E' G →
      angCong A B C E' D F → OnRay btw D E E'
  C5 : ∀ A B C D E F G H I : P, angCong A B C D E F → angCong A B C G H I → angCong D E F G H I
  C5_refl : ∀ A B C : P, angCong A B C A B C
  C6 : ∀ A B C D E F : P, ¬ Collinear lies A B C → ¬ Collinear lies D E F →
    segCong A B D E → segCong A C D F → angCong B A C E D F →
    segCong B C E F ∧ angCong A B C D E F ∧ angCong A C B D F E

namespace HilbertPlane

variable (H : HilbertPlane P L)

/-- Two lines are parallel when they have no point in common. -/
def Parallel (l m : L) : Prop := ¬ ∃ A, H.lies A l ∧ H.lies A m

/-- **Playfair's axiom**: through a point that is not on a line there is at most one line
parallel to it. -/
def Playfair : Prop :=
  ∀ (l : L) (A : P), ¬ H.lies A l → ∀ m m' : L, H.lies A m → H.Parallel m l →
    H.lies A m' → H.Parallel m' l → m = m'

end HilbertPlane

end Hilbert

namespace HyperbolicPlane

open Real

/-! ## Rays and the order of three points on a line -/

/-- A point on the ray, as Hilbert has it, is on the ray as `OnRay` has it. -/
theorem onRay_of_between {O A X : ℝ × ℝ} (h : X = A ∨ Between O X A ∨ Between O A X) :
    OnRay O A X := by
  rcases h with rfl | ⟨-, u, hu0, -, hu⟩ | ⟨-, u, hu0, -, hu⟩
  · exact ⟨1, one_pos, (Dim.pt_one (Dim.mk O X)).symm⟩
  · exact ⟨u, hu0, hu.symm⟩
  · refine ⟨1 / u, by positivity, ?_⟩
    have h1 := congrArg Prod.fst hu
    have h2 := congrArg Prod.snd hu
    simp only [Dim.pt] at h1 h2
    apply Prod.ext
    · simp only [Dim.pt]
      rw [← h1]
      field_simp
      ring
    · simp only [Dim.pt]
      rw [← h2]
      field_simp
      ring

/-- A point on the ray as `OnRay` has it is on the ray, as Hilbert has it. -/
theorem between_of_onRay {O A X : ℝ × ℝ} (hOA : O ≠ A) (h : OnRay O A X) :
    X = A ∨ Between O X A ∨ Between O A X := by
  obtain ⟨t, ht, rfl⟩ := h
  rcases lt_trichotomy t 1 with h1 | rfl | h1
  · exact Or.inr (Or.inl ⟨hOA, t, ht, h1, rfl⟩)
  · exact Or.inl (Dim.pt_one (Dim.mk O A))
  · refine Or.inr (Or.inr ⟨?_, 1 / t, by positivity, (div_lt_one ht).mpr h1, ?_⟩)
    · intro h
      apply hOA
      have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      simp only [Dim.pt] at e1 e2
      have k1 : t * (A.1 - O.1) = 0 := by linarith
      have k2 : t * (A.2 - O.2) = 0 := by linarith
      apply Prod.ext
      · linarith [(mul_eq_zero.mp k1).resolve_left ht.ne']
      · linarith [(mul_eq_zero.mp k2).resolve_left ht.ne']
    · apply Prod.ext
      · simp only [Dim.pt]
        field_simp
        ring
      · simp only [Dim.pt]
        field_simp
        ring

/-- **Of three different points on a line, one is between the two others.** -/
theorem between_trichotomy {A B C : ℝ × ℝ} (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hB : B ∈ (Dim.mk A C).points) : Between A B C ∨ Between B A C ∨ Between A C B := by
  obtain ⟨s, rfl⟩ := hB
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hAB (Dim.pt_zero (Dim.mk A C)).symm
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hBC (Dim.pt_one (Dim.mk A C))
  rcases lt_or_gt_of_ne hs0 with hneg | hpos
  · have h1s : 0 < 1 - s := by linarith
    refine Or.inr (Or.inl ⟨hBC, -s / (1 - s), div_pos (by linarith) h1s,
      (div_lt_one h1s).mpr (by linarith), ?_⟩)
    apply Prod.ext
    · simp only [Dim.pt]
      field_simp
      ring
    · simp only [Dim.pt]
      field_simp
      ring
  · rcases lt_or_gt_of_ne hs1 with hlt | hgt
    · exact Or.inl ⟨hAC, s, hpos, hlt, rfl⟩
    · refine Or.inr (Or.inr ⟨hAB, 1 / s, by positivity, (div_lt_one hpos).mpr hgt, ?_⟩)
      apply Prod.ext
      · simp only [Dim.pt]
        field_simp
        ring
      · simp only [Dim.pt]
        field_simp
        ring

/-- A pair of the plane off a line has a side that is not 0, and the three points that make
the side not 0 are different. -/
theorem ne_of_side_ne_zero {X Y Z : ℝ × ℝ} (h : (Dim.mk X Y).side Z ≠ 0) :
    X ≠ Y ∧ Z ≠ X ∧ Z ≠ Y := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    apply h
    simp [Dim.side, Dim.dir, cross]
  · rintro rfl
    apply h
    simp [Dim.side, Dim.dir, cross]
  · rintro rfl
    apply h
    simp only [Dim.side, Dim.dir, cross]
    ring

/-- A line of the plane is a set of points of the plane. -/
theorem IsLine.subset_plane {κ : ℝ} {S : Set (ℝ × ℝ)} (hS : IsLine (plane κ) S) :
    S ⊆ plane κ := by
  obtain ⟨M, -, rfl, -⟩ := hS
  exact fun _ hx => hx.2

/-- A line of the plane through two different points of it is what the dimension through them
has in the plane. -/
theorem IsLine.eq_through {κ : ℝ} {S : Set (ℝ × ℝ)} (hS : IsLine (plane κ) S) {D F : ℝ × ℝ}
    (hD : D ∈ S) (hF : F ∈ S) (hDF : D ≠ F) : S = (Dim.mk D F).points ∩ plane κ := by
  obtain ⟨M, -, rfl, -⟩ := hS
  rw [M.points_eq_through hD.1 hF.1 hDF]

/-! ## Euclid's plane: congruence with `apart` under the bound 0 -/

theorem mem_plane_zero (p : ℝ × ℝ) : p ∈ plane (0 : ℝ) := by
  rw [plane_zero]
  trivial

theorem apart_zero_nonneg (P Q : ℝ × ℝ) : 0 ≤ apart 0 P Q := by
  rw [apart_zero_bound]
  positivity

theorem apart_zero_eq_kleinInner (P Q : ℝ × ℝ) : apart 0 P Q = kleinInner 0 P Q Q := by
  rw [apart_zero_bound]
  simp only [kleinInner, zero_mul, add_zero]
  ring

/-- Under the bound 0, on a ray there is one point at a given `apart` from its origin. -/
theorem euclid_segment_construction {A B O D : ℝ × ℝ} (hAB : A ≠ B) (hOD : O ≠ D) :
    ∃! X, X ∈ plane (0 : ℝ) ∧ OnRay O D X ∧ apart 0 A B = apart 0 O X := by
  have hα : 0 < apart 0 A B := apart_pos (mem_plane_zero A) (mem_plane_zero B) hAB
  have hV : 0 < (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 := by
    have hne : ((D.1 - O.1, D.2 - O.2) : ℝ × ℝ) ≠ (0, 0) := by
      intro h
      apply hOD
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [] at h1 h2
      exact Prod.ext (by linarith) (by linarith)
    exact sq_add_sq_pos hne
  have hray : ∀ t : ℝ, apart 0 O ((Dim.mk O D).pt t)
      = t ^ 2 * ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2) := by
    intro t
    rw [apart_zero_bound]
    simp only [Dim.pt]
    ring
  have ht0 : 0 < √(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) :=
    sqrt_pos.mpr (div_pos hα hV)
  have ht2 : √(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) ^ 2
      = apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2) := sq_sqrt (div_pos hα hV).le
  refine ⟨(Dim.mk O D).pt (√(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2))),
    ⟨mem_plane_zero _, ⟨_, ht0, rfl⟩, ?_⟩, ?_⟩
  · rw [hray, ht2, div_mul_cancel₀ _ hV.ne']
  · rintro Y ⟨-, ⟨s, hs, rfl⟩, hY⟩
    rw [hray] at hY
    have hs2 : s ^ 2 = √(apart 0 A B / ((D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2)) ^ 2 := by
      rw [ht2, eq_div_iff hV.ne']
      linarith
    rw [(pow_left_inj₀ hs.le ht0.le two_ne_zero).mp hs2]

/-- Under the bound 0, the square roots of `apart` add along a segment. -/
theorem euclid_sqrt_apart_add {A B C : ℝ × ℝ} (h : Between A B C) :
    √(apart 0 A C) = √(apart 0 A B) + √(apart 0 B C) := by
  obtain ⟨-, u, hu0, hu1, rfl⟩ := h
  have e1 : apart 0 A ((Dim.mk A C).pt u) = u ^ 2 * apart 0 A C := by
    rw [apart_zero_bound, apart_zero_bound]
    simp only [Dim.pt]
    ring
  have e2 : apart 0 ((Dim.mk A C).pt u) C = (1 - u) ^ 2 * apart 0 A C := by
    rw [apart_zero_bound, apart_zero_bound]
    simp only [Dim.pt]
    ring
  rw [e1, e2, sqrt_mul (sq_nonneg _), sqrt_mul (sq_nonneg _), sqrt_sq hu0.le,
    sqrt_sq (by linarith)]
  ring

/-- Addition of segments under the bound 0. -/
theorem euclid_segment_addition {A B C D E F : ℝ × ℝ} (hABC : Between A B C)
    (hDEF : Between D E F) (h1 : apart 0 A B = apart 0 D E) (h2 : apart 0 B C = apart 0 E F) :
    apart 0 A C = apart 0 D F := by
  have h := euclid_sqrt_apart_add hABC
  rw [h1, h2, ← euclid_sqrt_apart_add hDEF] at h
  exact (sqrt_inj (apart_zero_nonneg _ _) (apart_zero_nonneg _ _)).mp h

/-- The law of cosines under the bound 0. -/
theorem euclid_law_of_cosines {A B C : ℝ × ℝ} (hB : B ≠ A) (hC : C ≠ A) :
    apart 0 B C = apart 0 A B + apart 0 A C
      - 2 * (√(apart 0 A B) * √(apart 0 A C)) * cos (kleinAngle 0 A B C) := by
  have hgB := sqrt_pos.mpr (kleinInner_self_pos (mem_plane_zero A) hB)
  have hgC := sqrt_pos.mpr (kleinInner_self_pos (mem_plane_zero A) hC)
  have e : apart 0 B C = kleinInner 0 A B B + kleinInner 0 A C C - 2 * kleinInner 0 A B C := by
    rw [apart_zero_bound]
    simp only [kleinInner, zero_mul, add_zero]
    ring
  rw [e, apart_zero_eq_kleinInner A B, apart_zero_eq_kleinInner A C,
    cos_kleinAngle (mem_plane_zero A) hB hC]
  field_simp

/-- Side, angle, side under the bound 0. -/
theorem euclid_sas {A B C D E F : ℝ × ℝ} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hDE : D ≠ E) (hDF : D ≠ F) (hEF : E ≠ F) (h1 : apart 0 A B = apart 0 D E)
    (h2 : apart 0 A C = apart 0 D F) (h3 : kleinAngle 0 A B C = kleinAngle 0 D E F) :
    apart 0 B C = apart 0 E F ∧ kleinAngle 0 B A C = kleinAngle 0 E D F ∧
      kleinAngle 0 C A B = kleinAngle 0 F D E := by
  have hBCEF : apart 0 B C = apart 0 E F := by
    rw [euclid_law_of_cosines hAB.symm hAC.symm, euclid_law_of_cosines hDE.symm hDF.symm, h1, h2,
      h3]
  have angle_eq : ∀ {P Q R P' Q' R' : ℝ × ℝ}, Q ≠ P → R ≠ P → Q' ≠ P' → R' ≠ P' →
      apart 0 P Q = apart 0 P' Q' → apart 0 P R = apart 0 P' R' →
      apart 0 Q R = apart 0 Q' R' → kleinAngle 0 P Q R = kleinAngle 0 P' Q' R' := by
    intro P Q R P' Q' R' hQ hR hQ' hR' e1 e2 e3
    have l := euclid_law_of_cosines hQ hR
    have l' := euclid_law_of_cosines hQ' hR'
    rw [e1, e2, e3] at l
    have hpos : 0 < 2 * (√(apart 0 P' Q') * √(apart 0 P' R')) := by
      have := sqrt_pos.mpr (apart_pos (mem_plane_zero P') (mem_plane_zero Q') hQ'.symm)
      have := sqrt_pos.mpr (apart_pos (mem_plane_zero P') (mem_plane_zero R') hR'.symm)
      positivity
    have hcos : cos (kleinAngle 0 P Q R) = cos (kleinAngle 0 P' Q' R') :=
      mul_left_cancel₀ hpos.ne' (by linarith)
    rw [kleinAngle_eq_arccos_cos 0 P Q R, kleinAngle_eq_arccos_cos 0 P' Q' R', hcos]
  refine ⟨hBCEF, ?_, ?_⟩
  · exact angle_eq hAB hBC.symm hDE hEF.symm (by rw [apart_comm, h1, apart_comm]) hBCEF h2
  · exact angle_eq hAC hBC hDF hEF (by rw [apart_comm, h2, apart_comm])
      (by rw [apart_comm, hBCEF, apart_comm]) h1

/-! ## The plane of a bound that is not positive: congruence with `apart` -/

theorem apart_eq_iff_kleinDist_eq {κ : ℝ} (hκ : κ < 0) {A B C D : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hC : C ∈ plane κ) (hD : D ∈ plane κ) :
    apart κ A B = apart κ C D ↔ kleinDist κ A B = kleinDist κ C D := by
  constructor
  · intro h
    rw [kleinDist_eq_arsinh hκ hA hB, kleinDist_eq_arsinh hκ hC hD, h]
  · intro h
    rw [apart_eq_sinh_kleinDist hκ hA hB, apart_eq_sinh_kleinDist hκ hC hD, h]

/-- C1 with `apart`, under a bound that is not positive. -/
theorem segment_construction_apart {κ : ℝ} (hκ : κ ≤ 0) {A B O D : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hO : O ∈ plane κ) (hAB : A ≠ B) (hOD : O ≠ D) :
    ∃! X, X ∈ plane κ ∧ OnRay O D X ∧ apart κ A B = apart κ O X := by
  rcases hκ.lt_or_eq with h | rfl
  · obtain ⟨X, ⟨hX, hray, hd⟩, huniq⟩ := segment_construction h hA hB hO hAB hOD
    exact ⟨X, ⟨hX, hray, (apart_eq_iff_kleinDist_eq h hA hB hO hX).mpr hd⟩,
      fun Y ⟨hY, hrY, haY⟩ => huniq Y ⟨hY, hrY, (apart_eq_iff_kleinDist_eq h hA hB hO hY).mp haY⟩⟩
  · exact euclid_segment_construction hAB hOD

/-- C3 with `apart`, under a bound that is not positive. -/
theorem segment_addition_apart {κ : ℝ} (hκ : κ ≤ 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hF : F ∈ plane κ) (hABC : Between A B C)
    (hDEF : Between D E F) (h1 : apart κ A B = apart κ D E) (h2 : apart κ B C = apart κ E F) :
    apart κ A C = apart κ D F := by
  rcases hκ.lt_or_eq with h | rfl
  · have hB := (kleinDist_add_of_between h hA hC hABC).1
    have hE := (kleinDist_add_of_between h hD hF hDEF).1
    rw [apart_eq_iff_kleinDist_eq h hA hC hD hF]
    exact segment_addition h hA hC hD hF hABC hDEF
      ((apart_eq_iff_kleinDist_eq h hA hB hD hE).mp h1)
      ((apart_eq_iff_kleinDist_eq h hB hC hE hF).mp h2)
  · exact euclid_segment_addition hABC hDEF h1 h2

/-- C6 with `apart`, under a bound that is not positive. -/
theorem sas_apart {κ : ℝ} (hκ : κ ≤ 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hE : E ∈ plane κ)
    (hF : F ∈ plane κ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hDE : D ≠ E) (hDF : D ≠ F)
    (hEF : E ≠ F) (h1 : apart κ A B = apart κ D E) (h2 : apart κ A C = apart κ D F)
    (h3 : kleinAngle κ A B C = kleinAngle κ D E F) :
    apart κ B C = apart κ E F ∧ kleinAngle κ B A C = kleinAngle κ E D F ∧
      kleinAngle κ C A B = kleinAngle κ F D E := by
  rcases hκ.lt_or_eq with h | rfl
  · obtain ⟨e1, e2, e3⟩ := side_angle_side h hA hB hC hD hE hF hAB hAC hBC hDE hDF hEF
      ((apart_eq_iff_kleinDist_eq h hA hB hD hE).mp h1)
      ((apart_eq_iff_kleinDist_eq h hA hC hD hF).mp h2) h3
    exact ⟨(apart_eq_iff_kleinDist_eq h hB hC hE hF).mpr e1, e2, e3⟩
  · exact euclid_sas hAB hAC hBC hDE hDF hEF h1 h2 h3

/-! ## The plane of a bound as a Hilbert plane -/

open Hilbert

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
    hX (by show X.1 ∈ l.1; rw [hl]; exact ⟨hm, X.2⟩)
  have hDm : D.1 ∈ M.points := by
    have h : D.1 ∈ l.1 := hD
    rw [hl] at h
    exact h.1
  obtain ⟨Y, hYM, hY, hYb⟩ :=
    pasch κ A.2 B.2 C.2 M hM (hnot A hA) (hnot B hB) (hnot C hC) hDm hAD
  exact ⟨⟨Y, hY⟩, by show Y ∈ l.1; rw [hl]; exact ⟨hYM, hY⟩, hYb⟩

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
      · show B.1 ∈ _
        rw [hBA]
        exact ⟨(Dim.mk _ _).zero_mem, A.2⟩
      · show C.1 ∈ _
        rw [← hAC]
        exact ⟨(Dim.mk _ _).zero_mem, A.2⟩
    · refine ⟨lineThrough A C hAC, lies_lineThrough_left A C hAC, ?_,
        lies_lineThrough_right A C hAC⟩
      show B.1 ∈ _
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
    show X.1 ∈ l.1 ↔ _
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
    show 0 < _ * _
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
    show G.1 ∈ l.1
    rw [hl]
    exact ⟨Dim.mem_points_of_side_eq_zero _ hDF' G.1 h, G.2⟩
  obtain ⟨hex, huniq⟩ := angle_construction B.2 D.2 (model_side_ne_zero hABC) hDF' hGs
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hE, hs, ha⟩ := hex
    refine ⟨⟨E, hE⟩, (model_sameSide_iff hD hF hDF' ⟨E, hE⟩ G).mpr hs, ?_⟩
    show kleinAngle κ B.1 A.1 C.1 = kleinAngle κ D.1 E F.1
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

end HyperbolicPlane
