/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import ParallelPostulate.HyperbolicPlane.Distance

/-!
# Hilbert's axioms of congruence in the plane of a bound

With the real numbers and a negative bound, a segment is measured by Klein's distance and an
angle by `kleinAngle`, and two segments, or two angles, are congruent when their measures are
equal. This file proves Hilbert's six axioms of congruence, C1 to C6 (Theorem H19). It also
proves C1, C3 and C6 with `apart` for the bound 0, and so for every bound that is not positive,
for the Hilbert planes of `Hilbert/Model.lean`.

## Contents

* Theorem H19, Hilbert's axioms of congruence: `OnRay`, `SameSide`, `segment_construction` (C1),
  `segment_congruence_trans` (C2), `segment_addition` (C3), `angle_construction` (C4),
  `angle_congruence_trans` (C5), `side_angle_side` (C6), `kleinDist_comm`, `kleinAngle_comm`,
  `kleinAngle_onRay`, `kleinDist_nonneg`, `kleinDist_pos`, `sinh_kleinDist`, `cosh_kleinDist`,
  `cos_kleinAngle`, `law_of_cosines`, `kleinDist_add_of_between`
* steps of the proofs of congruence: `apart_eq_kleinInner`, `one_add_dot_pos`, `kleinInner_gram`,
  `kleinAngle_eq_arccos_cos`, `apart_ray`, `apart_ray_lt`, `exists_onRay_apart`,
  `sin_kleinAngle_pos`
* a ray, as Hilbert has it: `onRay_of_between`, `between_of_onRay`
* Euclid's plane, with `apart`: `mem_plane_zero`, `apart_zero_nonneg`, `apart_zero_eq_kleinInner`,
  `euclid_segment_construction`, `euclid_sqrt_apart_add`, `euclid_segment_addition`,
  `euclid_law_of_cosines`, `euclid_sas`
* C1, C3 and C6 with `apart`, under a bound that is not positive: `apart_eq_iff_kleinDist_eq`,
  `segment_construction_apart`, `segment_addition_apart`, `sas_apart`
-/

namespace HyperbolicPlane

open Pairs

/-! ## Hilbert's axioms of congruence

With the real numbers and a negative bound, a segment is measured by Klein's distance and an
angle by `kleinAngle`, and two segments, or two angles, are congruent when their measures are
equal. This section proves Hilbert's six axioms of congruence, C1 to C6, for the plane. -/

section Congruence

open Set Real

/-- `apart` is the inner product at `P` of the direction to `Q` with itself, divided by the
bounds at the two pairs. -/
theorem apart_eq_kleinInner (κ : ℝ) (P Q : ℝ × ℝ) :
    apart κ P Q = kleinInner κ P Q Q
      / ((1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * (1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) := by
  simp only [apart, kleinInner, cross]
  ring

/-- Under a bound that is not positive, two points of the plane have `1 + κ (P · Q)` positive. -/
theorem one_add_dot_pos {κ : ℝ} (hκ : κ ≤ 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : 0 < 1 + κ * (P.1 * Q.1 + P.2 * Q.2) := by
  have hP' := mem_plane.mp hP
  have hQ' := mem_plane.mp hQ
  have hcs : (P.1 * Q.1 + P.2 * Q.2) ^ 2 ≤ (P.1 ^ 2 + P.2 ^ 2) * (Q.1 ^ 2 + Q.2 ^ 2) := by
    nlinarith [sq_nonneg (P.1 * Q.2 - P.2 * Q.1)]
  have h1 : 0 ≤ -κ * (P.1 ^ 2 + P.2 ^ 2) := mul_nonneg (neg_nonneg.mpr hκ) (by positivity)
  have h2 : 0 ≤ -κ * (Q.1 ^ 2 + Q.2 ^ 2) := mul_nonneg (neg_nonneg.mpr hκ) (by positivity)
  have hlt : (κ * (P.1 * Q.1 + P.2 * Q.2)) ^ 2 < 1 := by
    calc (κ * (P.1 * Q.1 + P.2 * Q.2)) ^ 2 = κ ^ 2 * (P.1 * Q.1 + P.2 * Q.2) ^ 2 := by ring
      _ ≤ κ ^ 2 * ((P.1 ^ 2 + P.2 ^ 2) * (Q.1 ^ 2 + Q.2 ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg κ)
      _ = (-κ * (P.1 ^ 2 + P.2 ^ 2)) * (-κ * (Q.1 ^ 2 + Q.2 ^ 2)) := by ring
      _ < 1 * 1 := by
        apply mul_lt_mul'' _ _ h1 h2 <;> linarith
      _ = 1 := one_mul 1
  nlinarith [hlt]

/-- Klein's distance is not negative. -/
theorem kleinDist_nonneg {κ : ℝ} {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    0 ≤ kleinDist κ P Q :=
  le_csInf (kleinDist_nonempty hP hQ) (by rintro _ ⟨γ, -, rfl⟩; exact kleinLength_nonneg κ γ)

/-- **Klein's distance does not depend on the order of the two points.** -/
theorem kleinDist_comm {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : kleinDist κ P Q = kleinDist κ Q P := by
  rw [kleinDist_eq_arsinh hκ hP hQ, kleinDist_eq_arsinh hκ hQ hP, apart_comm]

/-- Two different points of the plane are a positive distance apart. -/
theorem kleinDist_pos {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) (hPQ : P ≠ Q) : 0 < kleinDist κ P Q := by
  rw [kleinDist_eq_arsinh hκ hP hQ]
  apply div_pos _ (sqrt_pos.mpr (neg_pos.mpr hκ))
  rw [arsinh_pos_iff, sqrt_pos]
  exact mul_pos (neg_pos.mpr hκ) (apart_pos hP hQ hPQ)

/-- **The hyperbolic sine of Klein's distance.** -/
theorem sinh_kleinDist {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) :
    sinh (√(-κ) * kleinDist κ P Q) = √(-κ) * √(kleinInner κ P Q Q)
      / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) := by
  have hs : √(-κ) ≠ 0 := (sqrt_pos.mpr (neg_pos.mpr hκ)).ne'
  have e : √(-κ) * (arsinh (√(-κ * apart κ P Q)) / √(-κ)) = arsinh (√(-κ * apart κ P Q)) := by
    field_simp
  rw [kleinDist_eq_arsinh hκ hP hQ, e, sinh_arsinh, apart_eq_kleinInner,
    sqrt_mul (neg_nonneg.mpr hκ.le),
    sqrt_div' _ (mul_nonneg (mem_plane.mp hP).le (mem_plane.mp hQ).le),
    sqrt_mul (mem_plane.mp hP).le, mul_div_assoc]

/-- **The hyperbolic cosine of Klein's distance.** -/
theorem cosh_kleinDist {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) :
    cosh (√(-κ) * kleinDist κ P Q) = (1 + κ * (P.1 * Q.1 + P.2 * Q.2))
      / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) := by
  have hBP := mem_plane.mp hP
  have hBQ := mem_plane.mp hQ
  have hsP : 0 < √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) := sqrt_pos.mpr hBP
  have hsQ : 0 < √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) := sqrt_pos.mpr hBQ
  have hk : √(-κ) ^ 2 = -κ := sq_sqrt (neg_nonneg.mpr hκ.le)
  have hg : √(kleinInner κ P Q Q) ^ 2 = kleinInner κ P Q Q := by
    rcases eq_or_ne Q P with rfl | h
    · have h0 : kleinInner κ Q Q Q = 0 := by
        simp only [kleinInner, cross]
        ring
      rw [h0]
      simp
    · exact sq_sqrt (kleinInner_self_pos hP h).le
  have hP2 : √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 = 1 + κ * (P.1 ^ 2 + P.2 ^ 2) := sq_sqrt hBP.le
  have hQ2 : √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2 = 1 + κ * (Q.1 ^ 2 + Q.2 ^ 2) := sq_sqrt hBQ.le
  have hpos : 0 < (1 + κ * (P.1 * Q.1 + P.2 * Q.2))
      / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2))) :=
    div_pos (one_add_dot_pos hκ.le hP hQ) (mul_pos hsP hsQ)
  rw [← pow_left_inj₀ (cosh_pos _).le hpos.le two_ne_zero, cosh_sq, sinh_kleinDist hκ hP hQ]
  have e1 : (√(-κ) * √(kleinInner κ P Q Q)
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)))) ^ 2 + 1
      = (√(-κ) ^ 2 * √(kleinInner κ P Q Q) ^ 2
        + √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2)
          / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2) := by
    field_simp
  have e2 : ((1 + κ * (P.1 * Q.1 + P.2 * Q.2))
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)))) ^ 2
      = (1 + κ * (P.1 * Q.1 + P.2 * Q.2)) ^ 2
          / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (Q.1 ^ 2 + Q.2 ^ 2)) ^ 2) := by
    rw [div_pow, mul_pow]
  rw [e1, e2, hk, hg, hP2, hQ2]
  congr 1
  simp only [kleinInner, cross]
  ring

/-- **The Gram identity** for the inner product at a pair. -/
theorem kleinInner_gram (κ : ℝ) (P A B : ℝ × ℝ) :
    kleinInner κ P A A * kleinInner κ P B B - kleinInner κ P A B ^ 2
      = (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) * (Dim.mk P A).side B ^ 2 := by
  simp only [kleinInner, Dim.side, Dim.dir, cross]
  ring

/-- **The cosine of `kleinAngle`.** At a point of the plane the quotient is between `-1` and
`1`, and `kleinAngle` is its arccosine. -/
theorem cos_kleinAngle {κ : ℝ} {P A B : ℝ × ℝ} (hP : P ∈ plane κ) (hA : A ≠ P) (hB : B ≠ P) :
    cos (kleinAngle κ P A B)
      = kleinInner κ P A B / (√(kleinInner κ P A A) * √(kleinInner κ P B B)) := by
  have hgA := kleinInner_self_pos hP hA
  have hgB := kleinInner_self_pos hP hB
  have hd : 0 < √(kleinInner κ P A A) * √(kleinInner κ P B B) :=
    mul_pos (sqrt_pos.mpr hgA) (sqrt_pos.mpr hgB)
  have habs : |kleinInner κ P A B| ≤ √(kleinInner κ P A A) * √(kleinInner κ P B B) := by
    rw [← sqrt_mul hgA.le]
    apply abs_le_sqrt
    have := kleinInner_gram κ P A B
    nlinarith [mul_nonneg (mem_plane.mp hP).le (sq_nonneg ((Dim.mk P A).side B))]
  have hx : |kleinInner κ P A B / (√(kleinInner κ P A A) * √(kleinInner κ P B B))| ≤ 1 := by
    rw [abs_div, abs_of_pos hd, div_le_one hd]
    exact habs
  have h1 := abs_le.mp hx
  rw [kleinAngle, cos_arccos h1.1 h1.2]

/-- `kleinAngle` is between 0 and `π`, so it is the arccosine of its cosine. -/
theorem kleinAngle_eq_arccos_cos (κ : ℝ) (P A B : ℝ × ℝ) :
    kleinAngle κ P A B = arccos (cos (kleinAngle κ P A B)) :=
  (arccos_cos (arccos_nonneg _) (arccos_le_pi _)).symm

/-- **The law of cosines** in the plane of a negative bound, with Klein's distance and
`kleinAngle`, at the vertex `P`. -/
theorem law_of_cosines {κ : ℝ} (hκ : κ < 0) {P A B : ℝ × ℝ} (hP : P ∈ plane κ)
    (hA : A ∈ plane κ) (hB : B ∈ plane κ) (hAP : A ≠ P) (hBP : B ≠ P) :
    cosh (√(-κ) * kleinDist κ P A) * cosh (√(-κ) * kleinDist κ P B)
        - cosh (√(-κ) * kleinDist κ A B)
      = sinh (√(-κ) * kleinDist κ P A) * sinh (√(-κ) * kleinDist κ P B)
        * cos (kleinAngle κ P A B) := by
  have hsP := sqrt_pos.mpr (mem_plane.mp hP)
  have hsA := sqrt_pos.mpr (mem_plane.mp hA)
  have hsB := sqrt_pos.mpr (mem_plane.mp hB)
  have hgA := sqrt_pos.mpr (kleinInner_self_pos hP hAP)
  have hgB := sqrt_pos.mpr (kleinInner_self_pos hP hBP)
  have hL : cosh (√(-κ) * kleinDist κ P A) * cosh (√(-κ) * kleinDist κ P B)
        - cosh (√(-κ) * kleinDist κ A B)
      = ((1 + κ * (P.1 * A.1 + P.2 * A.2)) * (1 + κ * (P.1 * B.1 + P.2 * B.2))
          - √(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * (1 + κ * (A.1 * B.1 + A.2 * B.2)))
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (A.1 ^ 2 + A.2 ^ 2))
          * √(1 + κ * (B.1 ^ 2 + B.2 ^ 2))) := by
    rw [cosh_kleinDist hκ hP hA, cosh_kleinDist hκ hP hB, cosh_kleinDist hκ hA hB]
    field_simp
  have hR : sinh (√(-κ) * kleinDist κ P A) * sinh (√(-κ) * kleinDist κ P B)
        * cos (kleinAngle κ P A B)
      = √(-κ) ^ 2 * kleinInner κ P A B
        / (√(1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 * √(1 + κ * (A.1 ^ 2 + A.2 ^ 2))
          * √(1 + κ * (B.1 ^ 2 + B.2 ^ 2))) := by
    rw [sinh_kleinDist hκ hP hA, sinh_kleinDist hκ hP hB, cos_kleinAngle hP hAP hBP]
    field_simp
  rw [hL, hR, sq_sqrt (neg_nonneg.mpr hκ.le), sq_sqrt (mem_plane.mp hP).le]
  congr 1
  simp only [kleinInner, cross]
  ring

/-- `X` is on the ray from `O` through `A`: `X = O + t (A - O)` with `t` positive. -/
def OnRay (O A X : ℝ × ℝ) : Prop := ∃ t : ℝ, 0 < t ∧ X = (Dim.mk O A).pt t

/-- `X` and `Y` are on the same side of the line through `O` and `A`. -/
def SameSide (O A X Y : ℝ × ℝ) : Prop := 0 < (Dim.mk O A).side X * (Dim.mk O A).side Y

/-- **An angle does not depend on the order of its two rays.** -/
theorem kleinAngle_comm (κ : ℝ) (P A B : ℝ × ℝ) : kleinAngle κ P A B = kleinAngle κ P B A := by
  have h : kleinInner κ P A B = kleinInner κ P B A := by
    simp only [kleinInner]
    ring
  rw [kleinAngle, kleinAngle, h, mul_comm (√(kleinInner κ P A A))]

/-- **An angle depends only on its two rays.** -/
theorem kleinAngle_onRay {κ : ℝ} {P A B A' B' : ℝ × ℝ} (hA : OnRay P A A') (hB : OnRay P B B') :
    kleinAngle κ P A' B' = kleinAngle κ P A B := by
  obtain ⟨s, hs, rfl⟩ := hA
  obtain ⟨t, ht, rfl⟩ := hB
  have e1 : kleinInner κ P ((Dim.mk P A).pt s) ((Dim.mk P B).pt t)
      = 1 * s * t * kleinInner κ P A B := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have e2 : kleinInner κ P ((Dim.mk P A).pt s) ((Dim.mk P A).pt s)
      = 1 * s ^ 2 * kleinInner κ P A A := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have e3 : kleinInner κ P ((Dim.mk P B).pt t) ((Dim.mk P B).pt t)
      = 1 * t ^ 2 * kleinInner κ P B B := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  rw [kleinAngle, e1, e2, e3, kleinAngle_aux one_pos (mul_pos hs ht)]
  rfl

/-- **Theorem H19, C6: side, angle, side.** Let two triangles have two sides and the angle
between them congruent. Then the third sides are congruent, and so are the two other pairs of
angles. -/
theorem side_angle_side {κ : ℝ} (hκ : κ < 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hE : E ∈ plane κ)
    (hF : F ∈ plane κ) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hDE : D ≠ E) (hDF : D ≠ F)
    (hEF : E ≠ F) (h1 : kleinDist κ A B = kleinDist κ D E)
    (h2 : kleinDist κ A C = kleinDist κ D F) (h3 : kleinAngle κ A B C = kleinAngle κ D E F) :
    kleinDist κ B C = kleinDist κ E F ∧ kleinAngle κ B A C = kleinAngle κ E D F ∧
      kleinAngle κ C A B = kleinAngle κ F D E := by
  have hk : 0 < √(-κ) := sqrt_pos.mpr (neg_pos.mpr hκ)
  have lA := law_of_cosines hκ hA hB hC hAB.symm hAC.symm
  have lD := law_of_cosines hκ hD hE hF hDE.symm hDF.symm
  rw [h1, h2, h3] at lA
  have hcosh : cosh (√(-κ) * kleinDist κ B C) = cosh (√(-κ) * kleinDist κ E F) := by linarith
  have hnn : ∀ {X Y : ℝ × ℝ}, X ∈ plane κ → Y ∈ plane κ → 0 ≤ √(-κ) * kleinDist κ X Y :=
    fun hX hY => mul_nonneg hk.le (kleinDist_nonneg hX hY)
  have hBCEF : kleinDist κ B C = kleinDist κ E F := by
    have h := le_antisymm (cosh_le_cosh.mp hcosh.le) (cosh_le_cosh.mp hcosh.ge)
    rw [abs_of_nonneg (hnn hB hC), abs_of_nonneg (hnn hE hF)] at h
    exact mul_left_cancel₀ hk.ne' h
  have hsinh : ∀ {X Y : ℝ × ℝ}, X ∈ plane κ → Y ∈ plane κ → X ≠ Y →
      0 < sinh (√(-κ) * kleinDist κ X Y) :=
    fun hX hY hXY => sinh_pos_iff.mpr (mul_pos hk (kleinDist_pos hκ hX hY hXY))
  have angle_eq : ∀ {P Q R P' Q' R' : ℝ × ℝ}, P ∈ plane κ → Q ∈ plane κ → R ∈ plane κ →
      P' ∈ plane κ → Q' ∈ plane κ → R' ∈ plane κ → Q ≠ P → R ≠ P → Q' ≠ P' → R' ≠ P' →
      kleinDist κ P Q = kleinDist κ P' Q' → kleinDist κ P R = kleinDist κ P' R' →
      kleinDist κ Q R = kleinDist κ Q' R' → kleinAngle κ P Q R = kleinAngle κ P' Q' R' := by
    intro P Q R P' Q' R' hP hQ hR hP' hQ' hR' hQP hRP hQP' hRP' e1 e2 e3
    have l := law_of_cosines hκ hP hQ hR hQP hRP
    have l' := law_of_cosines hκ hP' hQ' hR' hQP' hRP'
    rw [e1, e2, e3] at l
    have hpos := mul_pos (hsinh hP' hQ' hQP'.symm) (hsinh hP' hR' hRP'.symm)
    have hcos : cos (kleinAngle κ P Q R) = cos (kleinAngle κ P' Q' R') :=
      mul_left_cancel₀ hpos.ne' (by linarith)
    rw [kleinAngle_eq_arccos_cos κ P Q R, kleinAngle_eq_arccos_cos κ P' Q' R', hcos]
  refine ⟨hBCEF, ?_, ?_⟩
  · exact angle_eq hB hA hC hE hD hF hAB hBC.symm hDE hEF.symm
      (by rw [kleinDist_comm hκ hB hA, kleinDist_comm hκ hE hD, h1]) hBCEF h2
  · exact angle_eq hC hA hB hF hD hE hAC hBC hDF hEF
      (by rw [kleinDist_comm hκ hC hA, kleinDist_comm hκ hF hD, h2])
      (by rw [kleinDist_comm hκ hC hB, kleinDist_comm hκ hF hE, hBCEF]) h1

/-- **Klein's distance adds along a segment.** If `B` is between `A` and `C`, it is a point of
the plane, and the distance from `A` to `C` is the sum of the distances from `A` to `B` and from
`B` to `C`. -/
theorem kleinDist_add_of_between {κ : ℝ} (hκ : κ < 0) {A B C : ℝ × ℝ} (hA : A ∈ plane κ)
    (hC : C ∈ plane κ) (h : Between A B C) :
    B ∈ plane κ ∧ kleinDist κ A C = kleinDist κ A B + kleinDist κ B C := by
  obtain ⟨-, u, hu0, hu1, rfl⟩ := h
  have hB : (Dim.mk A C).pt u ∈ plane κ := plane_convex κ hA hC hu0.le hu1.le
  refine ⟨hB, ?_⟩
  have hk : 0 < √(-κ) := sqrt_pos.mpr (neg_pos.mpr hκ)
  have hsA := sqrt_pos.mpr (mem_plane.mp hA)
  have hsB := sqrt_pos.mpr (mem_plane.mp hB)
  have hsC := sqrt_pos.mpr (mem_plane.mp hC)
  have hgAB : kleinInner κ A ((Dim.mk A C).pt u) ((Dim.mk A C).pt u)
      = u ^ 2 * kleinInner κ A C C := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have hgBC : kleinInner κ ((Dim.mk A C).pt u) C C = (1 - u) ^ 2 * kleinInner κ A C C := by
    simp only [kleinInner, cross, Dim.pt]
    ring
  have hcB : u * (1 + κ * (((Dim.mk A C).pt u).1 * C.1 + ((Dim.mk A C).pt u).2 * C.2))
      + (1 - u) * (1 + κ * (A.1 * ((Dim.mk A C).pt u).1 + A.2 * ((Dim.mk A C).pt u).2))
      = 1 + κ * (((Dim.mk A C).pt u).1 ^ 2 + ((Dim.mk A C).pt u).2 ^ 2) := by
    simp only [Dim.pt]
    ring
  have hL : sinh (√(-κ) * kleinDist κ A ((Dim.mk A C).pt u))
        * cosh (√(-κ) * kleinDist κ ((Dim.mk A C).pt u) C)
      + cosh (√(-κ) * kleinDist κ A ((Dim.mk A C).pt u))
        * sinh (√(-κ) * kleinDist κ ((Dim.mk A C).pt u) C)
      = √(-κ) * √(kleinInner κ A C C)
        * (u * (1 + κ * (((Dim.mk A C).pt u).1 * C.1 + ((Dim.mk A C).pt u).2 * C.2))
          + (1 - u) * (1 + κ * (A.1 * ((Dim.mk A C).pt u).1 + A.2 * ((Dim.mk A C).pt u).2)))
        / (√(1 + κ * (A.1 ^ 2 + A.2 ^ 2))
          * √(1 + κ * (((Dim.mk A C).pt u).1 ^ 2 + ((Dim.mk A C).pt u).2 ^ 2)) ^ 2
          * √(1 + κ * (C.1 ^ 2 + C.2 ^ 2))) := by
    rw [sinh_kleinDist hκ hA hB, cosh_kleinDist hκ hB hC, cosh_kleinDist hκ hA hB,
      sinh_kleinDist hκ hB hC, hgAB, hgBC, sqrt_mul (sq_nonneg _), sqrt_mul (sq_nonneg _),
      sqrt_sq hu0.le, sqrt_sq (by linarith)]
    field_simp
  have hsum : sinh (√(-κ) * kleinDist κ A C) = sinh (√(-κ) * kleinDist κ A ((Dim.mk A C).pt u)
      + √(-κ) * kleinDist κ ((Dim.mk A C).pt u) C) := by
    have hBB := (mem_plane.mp hB).ne'
    rw [sinh_add, hL, hcB, sq_sqrt (mem_plane.mp hB).le, sinh_kleinDist hκ hA hC]
    field_simp
  have := sinh_injective hsum
  rw [← mul_add] at this
  exact mul_left_cancel₀ hk.ne' this

/-- **Theorem H19, C3: addition of segments.** -/
theorem segment_addition {κ : ℝ} (hκ : κ < 0) {A B C D E F : ℝ × ℝ} (hA : A ∈ plane κ)
    (hC : C ∈ plane κ) (hD : D ∈ plane κ) (hF : F ∈ plane κ) (hABC : Between A B C)
    (hDEF : Between D E F) (h1 : kleinDist κ A B = kleinDist κ D E)
    (h2 : kleinDist κ B C = kleinDist κ E F) : kleinDist κ A C = kleinDist κ D F := by
  rw [(kleinDist_add_of_between hκ hA hC hABC).2, (kleinDist_add_of_between hκ hD hF hDEF).2,
    h1, h2]

/-- **Theorem H19, C2.** Two segments congruent to a third are congruent to each other. -/
theorem segment_congruence_trans {κ : ℝ} {A B C D E F : ℝ × ℝ}
    (h1 : kleinDist κ A B = kleinDist κ C D) (h2 : kleinDist κ A B = kleinDist κ E F) :
    kleinDist κ C D = kleinDist κ E F :=
  h1.symm.trans h2

/-- **Theorem H19, C5.** Two angles congruent to a third are congruent to each other. -/
theorem angle_congruence_trans {κ : ℝ} {A B C D E F P Q R : ℝ × ℝ}
    (h1 : kleinAngle κ A B C = kleinAngle κ D E F) (h2 : kleinAngle κ A B C = kleinAngle κ P Q R) :
    kleinAngle κ D E F = kleinAngle κ P Q R :=
  h1.symm.trans h2

/-- Along the ray from `O` through `D`, `apart` from `O`. -/
theorem apart_ray (κ : ℝ) (O D : ℝ × ℝ) (t : ℝ) :
    apart κ O ((Dim.mk O D).pt t) = t ^ 2 * kleinInner κ O D D
      / ((1 + κ * (O.1 ^ 2 + O.2 ^ 2))
        * (1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2))) := by
  rw [apart_eq_kleinInner]
  congr 1
  simp only [kleinInner, cross, Dim.pt]
  ring

/-- **Along a ray, `apart` from its origin grows.** -/
theorem apart_ray_lt {κ : ℝ} (hκ : κ < 0) {O D : ℝ × ℝ} (hO : O ∈ plane κ) (hOD : O ≠ D)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (hXs : (Dim.mk O D).pt s ∈ plane κ)
    (hXt : (Dim.mk O D).pt t ∈ plane κ) :
    apart κ O ((Dim.mk O D).pt s) < apart κ O ((Dim.mk O D).pt t) := by
  have hG := kleinInner_self_pos hO hOD.symm
  have hBO := mem_plane.mp hO
  have hBs := mem_plane.mp hXs
  have hBt := mem_plane.mp hXt
  have h1 := one_add_dot_pos hκ.le hO hXs
  have h2 := one_add_dot_pos hκ.le hO hXt
  rw [apart_ray, apart_ray, div_lt_div_iff₀ (mul_pos hBO hBs) (mul_pos hBO hBt)]
  have key : t ^ 2 * kleinInner κ O D D * ((1 + κ * (O.1 ^ 2 + O.2 ^ 2))
        * (1 + κ * (((Dim.mk O D).pt s).1 ^ 2 + ((Dim.mk O D).pt s).2 ^ 2)))
      - s ^ 2 * kleinInner κ O D D * ((1 + κ * (O.1 ^ 2 + O.2 ^ 2))
        * (1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2)))
      = kleinInner κ O D D * (1 + κ * (O.1 ^ 2 + O.2 ^ 2)) * ((t - s)
        * (s * (1 + κ * (O.1 * ((Dim.mk O D).pt t).1 + O.2 * ((Dim.mk O D).pt t).2))
          + t * (1 + κ * (O.1 * ((Dim.mk O D).pt s).1 + O.2 * ((Dim.mk O D).pt s).2)))) := by
    simp only [Dim.pt]
    ring
  have hpos := mul_pos (mul_pos hG hBO) (mul_pos (sub_pos.mpr hst)
    (add_pos (mul_pos hs h2) (mul_pos (hs.trans hst) h1)))
  linarith

/-- **On a ray from a point of the plane, `apart` from the origin takes every positive value.**
Under a negative bound. -/
theorem exists_onRay_apart {κ : ℝ} (hκ : κ < 0) {O D : ℝ × ℝ} (hO : O ∈ plane κ) (hOD : O ≠ D)
    {α : ℝ} (hα : 0 < α) :
    ∃ t : ℝ, 0 < t ∧ (Dim.mk O D).pt t ∈ plane κ ∧ apart κ O ((Dim.mk O D).pt t) = α := by
  have hG := kleinInner_self_pos hO hOD.symm
  have hBO := mem_plane.mp hO
  have hnk : 0 < -κ := neg_pos.mpr hκ
  have hV : 0 < (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 := by
    have hne : ((D.1 - O.1, D.2 - O.2) : ℝ × ℝ) ≠ (0, 0) := by
      intro h
      apply hOD
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [] at h1 h2
      exact Prod.ext (by linarith) (by linarith)
    exact sq_add_sq_pos hne
  set V := (D.1 - O.1) ^ 2 + (D.2 - O.2) ^ 2 with hVdef
  set W := O.1 * (D.1 - O.1) + O.2 * (D.2 - O.2) with hWdef
  set T := (2 * |W| + 1) / V + 1 / (-κ) with hTdef
  have hT1 : 1 / (-κ) ≤ T := by
    have : 0 ≤ (2 * |W| + 1) / V := div_nonneg (by positivity) hV.le
    linarith
  have hT0 : 0 ≤ T := le_trans (one_div_pos.mpr hnk).le hT1
  have hTV : 2 * |W| + 1 ≤ T * V := by
    rw [hTdef, add_mul, div_mul_cancel₀ _ hV.ne']
    have : 0 ≤ 1 / (-κ) * V := mul_nonneg (one_div_pos.mpr hnk).le hV.le
    linarith
  have hXT : 1 / (-κ) ≤ ((Dim.mk O D).pt T).1 ^ 2 + ((Dim.mk O D).pt T).2 ^ 2 := by
    have e : ((Dim.mk O D).pt T).1 ^ 2 + ((Dim.mk O D).pt T).2 ^ 2
        = (O.1 ^ 2 + O.2 ^ 2) + 2 * (T * W) + T * (T * V) := by
      simp only [Dim.pt, hWdef, hVdef]
      ring
    rw [e]
    have ha : -(T * |W|) ≤ T * W := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le W) hT0
      linarith
    have hb : 0 ≤ T * (T * V - 2 * |W| - 1) := mul_nonneg hT0 (by linarith)
    nlinarith [sq_nonneg O.1, sq_nonneg O.2]
  have hBT : 1 + κ * (((Dim.mk O D).pt T).1 ^ 2 + ((Dim.mk O D).pt T).2 ^ 2) ≤ 0 := by
    have h := mul_le_mul_of_nonpos_left hXT hκ.le
    have e : κ * (1 / (-κ)) = -1 := by
      rw [mul_one_div, div_neg, div_self hκ.ne]
    linarith
  set f : ℝ → ℝ := fun t => t ^ 2 * kleinInner κ O D D - α
    * (1 + κ * (O.1 ^ 2 + O.2 ^ 2))
    * (1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2)) with hf
  have hfc : Continuous f := by
    simp only [hf, Dim.pt]
    fun_prop
  have hf0 : f 0 < 0 := by
    have e : f 0 = -(α * (1 + κ * (O.1 ^ 2 + O.2 ^ 2)) ^ 2) := by
      simp only [hf, Dim.pt]
      ring
    rw [e]
    have := mul_pos hα (pow_pos hBO 2)
    linarith
  have hfT : 0 ≤ f T := by
    simp only [hf]
    have := mul_nonneg (mul_nonneg hα.le hBO.le) (neg_nonneg.mpr hBT)
    nlinarith [mul_nonneg (sq_nonneg T) hG.le]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hT0 hfc.continuousOn ⟨hf0.le, hfT⟩
  have ht0 : 0 < t := by
    rcases ht.1.eq_or_lt with h | h
    · rw [← h] at hft
      linarith
    · exact h
  simp only [hf] at hft
  have hBt : 0 < 1 + κ * (((Dim.mk O D).pt t).1 ^ 2 + ((Dim.mk O D).pt t).2 ^ 2) := by
    by_contra h
    have h := not_lt.mp h
    have := mul_nonpos_of_nonneg_of_nonpos (mul_pos hα hBO).le h
    nlinarith [mul_pos (pow_pos ht0 2) hG]
  have hXt : (Dim.mk O D).pt t ∈ plane κ := mem_plane.mpr hBt
  have hap : apart κ O ((Dim.mk O D).pt t) = α := by
    rw [apart_ray, div_eq_iff (mul_pos hBO hBt).ne']
    linear_combination hft
  exact ⟨t, ht0, hXt, hap⟩

/-- **Theorem H19, C1: construction of segments.** On a ray from `O` there is one point, and
only one, whose distance from `O` is the length of a given segment. -/
theorem segment_construction {κ : ℝ} (hκ : κ < 0) {A B O D : ℝ × ℝ} (hA : A ∈ plane κ)
    (hB : B ∈ plane κ) (hO : O ∈ plane κ) (hAB : A ≠ B) (hOD : O ≠ D) :
    ∃! X, X ∈ plane κ ∧ OnRay O D X ∧ kleinDist κ A B = kleinDist κ O X := by
  obtain ⟨t, ht0, hXt, hap⟩ := exists_onRay_apart hκ hO hOD (apart_pos hA hB hAB)
  refine ⟨(Dim.mk O D).pt t, ⟨hXt, ⟨t, ht0, rfl⟩, ?_⟩, ?_⟩
  · rw [kleinDist_eq_arsinh hκ hA hB, kleinDist_eq_arsinh hκ hO hXt, hap]
  · rintro Y ⟨hY, ⟨s, hs, rfl⟩, hYd⟩
    have hapY : apart κ O ((Dim.mk O D).pt s) = apart κ A B := by
      rw [apart_eq_sinh_kleinDist hκ hO hY, ← hYd, ← apart_eq_sinh_kleinDist hκ hA hB]
    rcases lt_trichotomy s t with h | rfl | h
    · exact absurd (hapY.trans hap.symm) (apart_ray_lt hκ hO hOD hs h hY hXt).ne
    · rfl
    · exact absurd (hap.trans hapY.symm) (apart_ray_lt hκ hO hOD ht0 h hXt hY).ne

/-- **An angle with two rays that are not on one line is strictly between 0 and `π`**, so its
sine is positive. -/
theorem sin_kleinAngle_pos {κ : ℝ} {A B C : ℝ × ℝ} (hA : A ∈ plane κ)
    (hABC : (Dim.mk A B).side C ≠ 0) : 0 < sin (kleinAngle κ A B C) := by
  have hBA : B ≠ A := by
    rintro rfl
    apply hABC
    simp [Dim.side, Dim.dir, cross]
  have hCA : C ≠ A := by
    rintro rfl
    apply hABC
    simp [Dim.side, Dim.dir, cross]
  have hgB := kleinInner_self_pos hA hBA
  have hgC := kleinInner_self_pos hA hCA
  have h0 : 0 ≤ sin (kleinAngle κ A B C) :=
    sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg _) (arccos_le_pi _)
  have hc2 : cos (kleinAngle κ A B C) ^ 2 < 1 := by
    rw [cos_kleinAngle hA hBA hCA, div_pow, mul_pow, sq_sqrt hgB.le, sq_sqrt hgC.le,
      div_lt_one (mul_pos hgB hgC)]
    have := kleinInner_gram κ A B C
    have : 0 < (1 + κ * (A.1 ^ 2 + A.2 ^ 2)) * (Dim.mk A B).side C ^ 2 :=
      mul_pos (mem_plane.mp hA) (by positivity)
    linarith
  have hs := sin_sq_add_cos_sq (kleinAngle κ A B C)
  rcases h0.eq_or_lt with h | h
  · rw [← h] at hs
    linarith
  · exact h

/-- **Theorem H19, C4: construction of angles.** Given an angle, a ray from `D` through `F`,
and a side of the line `DF`, there is a ray from `D` on that side that makes the given angle
with the ray `DF`, and only one. This holds under any bound. -/
theorem angle_construction {κ : ℝ} {A B C D F G : ℝ × ℝ} (hA : A ∈ plane κ)
    (hD : D ∈ plane κ) (hABC : (Dim.mk A B).side C ≠ 0) (hDF : D ≠ F)
    (hG : (Dim.mk D F).side G ≠ 0) :
    (∃ E, E ∈ plane κ ∧ SameSide D F E G ∧ kleinAngle κ D F E = kleinAngle κ A B C) ∧
    ∀ E E', E ∈ plane κ → SameSide D F E G → kleinAngle κ D F E = kleinAngle κ A B C →
      E' ∈ plane κ → SameSide D F E' G → kleinAngle κ D F E' = kleinAngle κ A B C →
      OnRay D E E' := by
  have hsin := sin_kleinAngle_pos hA hABC
  have hgU := kleinInner_self_pos hD hDF.symm
  have hBD := mem_plane.mp hD
  refine ⟨?_, ?_⟩
  · -- the direction perpendicular to `DF` in Klein's metric, and the side of `G`
    set θ := kleinAngle κ A B C with hθ
    set sG := (Dim.mk D F).side G with hsG
    set σ := sG / |sG| with hσ
    have hσ2 : σ ^ 2 = 1 := by
      rw [hσ, div_pow, sq_abs, div_self (pow_ne_zero 2 hG)]
    have hσG : 0 < σ * sG := by
      rw [hσ, div_mul_eq_mul_div, ← sq, ← sq_abs, sq, mul_self_div_self]
      exact abs_pos.mpr hG
    set sB := √(1 + κ * (D.1 ^ 2 + D.2 ^ 2)) with hsB
    have hsB2 : sB ^ 2 = 1 + κ * (D.1 ^ 2 + D.2 ^ 2) := sq_sqrt hBD.le
    have hsBp : 0 < sB := sqrt_pos.mpr hBD
    set c := D.1 * F.2 - D.2 * F.1 with hc
    set v : ℝ × ℝ := (cos θ * sB * (F.1 - D.1) + σ * sin θ * (-(F.2 - D.2) - κ * c * D.1),
      cos θ * sB * (F.2 - D.2) + σ * sin θ * ((F.1 - D.1) - κ * c * D.2)) with hv
    obtain ⟨ε, hε, hE⟩ := plane_open_forward κ (Dim.mk D (D.1 + v.1, D.2 + v.2)) hD
    set E := (Dim.mk D (D.1 + v.1, D.2 + v.2)).pt ε with hEdef
    have hN : kleinInner κ D F E = ε * cos θ * sB * kleinInner κ D F F := by
      simp only [hEdef, hv, hc, kleinInner, cross, Dim.pt]
      ring
    have hNN : kleinInner κ D E E = ε ^ 2 * (cos θ ^ 2 * sB ^ 2
        + σ ^ 2 * sin θ ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2))) * kleinInner κ D F F := by
      simp only [hEdef, hv, hc, kleinInner, cross, Dim.pt]
      ring
    have hside : (Dim.mk D F).side E = ε * σ * sin θ * kleinInner κ D F F := by
      simp only [hEdef, hv, hc, kleinInner, Dim.side, Dim.dir, cross, Dim.pt]
      ring
    have hNN' : kleinInner κ D E E
        = ε ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2)) * kleinInner κ D F F := by
      rw [hNN, hsB2, hσ2]
      linear_combination (ε ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2)) * kleinInner κ D F F)
        * sin_sq_add_cos_sq θ
    have hsq : √(ε ^ 2 * (1 + κ * (D.1 ^ 2 + D.2 ^ 2)) * kleinInner κ D F F)
        = ε * sB * √(kleinInner κ D F F) := by
      rw [sqrt_mul (by positivity), sqrt_mul (by positivity), sqrt_sq hε.le]
    have hg2 : √(kleinInner κ D F F) * √(kleinInner κ D F F) = kleinInner κ D F F :=
      mul_self_sqrt hgU.le
    have hx : ε * cos θ * sB * kleinInner κ D F F
        / (√(kleinInner κ D F F) * (ε * sB * √(kleinInner κ D F F))) = cos θ := by
      rw [div_eq_iff (by positivity)]
      linear_combination (-(ε * cos θ * sB)) * hg2
    refine ⟨E, hE, ?_, ?_⟩
    · change 0 < (Dim.mk D F).side E * sG
      rw [hside]
      have := mul_pos (mul_pos (mul_pos hε hsin) hgU) hσG
      linarith [this]
    · have hθ0 : 0 ≤ θ := arccos_nonneg _
      have hθπ : θ ≤ π := arccos_le_pi _
      rw [kleinAngle, hN, hNN', hsq, hx, arccos_cos hθ0 hθπ]
  · intro E₁ E₂ hE₁ hs₁ ha₁ hE₂ hs₂ ha₂
    have hs12 : 0 < (Dim.mk D F).side E₁ * (Dim.mk D F).side E₂ := by
      have h := mul_pos hs₁ hs₂
      have e : (Dim.mk D F).side E₁ * (Dim.mk D F).side G
          * ((Dim.mk D F).side E₂ * (Dim.mk D F).side G)
          = (Dim.mk D F).side E₁ * (Dim.mk D F).side E₂ * (Dim.mk D F).side G ^ 2 := by ring
      rw [e] at h
      exact (mul_pos_iff_of_pos_right (by positivity)).mp h
    have hs1 : (Dim.mk D F).side E₁ ≠ 0 := by
      intro h
      rw [h, zero_mul] at hs12
      exact lt_irrefl 0 hs12
    have hE1D : E₁ ≠ D := by
      rintro rfl
      apply hs1
      simp [Dim.side, Dim.dir, cross]
    have hE2D : E₂ ≠ D := by
      rintro rfl
      apply (lt_irrefl (0 : ℝ))
      convert hs12 using 1
      simp [Dim.side, Dim.dir, cross]
    have hg1 := kleinInner_self_pos hD hE1D
    have hg2 := kleinInner_self_pos hD hE2D
    have hx : kleinInner κ D F E₁ / (√(kleinInner κ D F F) * √(kleinInner κ D E₁ E₁))
        = kleinInner κ D F E₂ / (√(kleinInner κ D F F) * √(kleinInner κ D E₂ E₂)) := by
      rw [← cos_kleinAngle hD hDF.symm hE1D, ← cos_kleinAngle hD hDF.symm hE2D, ha₁, ha₂]
    rw [div_eq_div_iff (by positivity) (by positivity)] at hx
    have hN : kleinInner κ D F E₁ * √(kleinInner κ D E₂ E₂)
        = kleinInner κ D F E₂ * √(kleinInner κ D E₁ E₁) := by
      apply mul_left_cancel₀ (sqrt_pos.mpr hgU).ne'
      linear_combination hx
    have hsq : kleinInner κ D F E₁ ^ 2 * kleinInner κ D E₂ E₂
        = kleinInner κ D F E₂ ^ 2 * kleinInner κ D E₁ E₁ := by
      have h := congrArg (· ^ 2) hN
      simp only [mul_pow, sq_sqrt hg1.le, sq_sqrt hg2.le] at h
      exact h
    have hNN : 0 ≤ kleinInner κ D F E₁ * kleinInner κ D F E₂ := by
      have h : kleinInner κ D F E₁ * kleinInner κ D F E₂ * √(kleinInner κ D E₂ E₂)
          = kleinInner κ D F E₂ ^ 2 * √(kleinInner κ D E₁ E₁) := by
        linear_combination (kleinInner κ D F E₂) * hN
      have h' : 0 ≤ kleinInner κ D F E₁ * kleinInner κ D F E₂ * √(kleinInner κ D E₂ E₂) := by
        rw [h]
        positivity
      exact (mul_nonneg_iff_of_pos_right (sqrt_pos.mpr hg2)).mp h'
    have gram1 := kleinInner_gram κ D F E₁
    have gram2 := kleinInner_gram κ D F E₂
    have hmain : (kleinInner κ D F E₁ * (Dim.mk D F).side E₂) ^ 2
        = (kleinInner κ D F E₂ * (Dim.mk D F).side E₁) ^ 2 := by
      apply mul_left_cancel₀ hBD.ne'
      linear_combination kleinInner κ D F F * hsq - kleinInner κ D F E₁ ^ 2 * gram2
        + kleinInner κ D F E₂ ^ 2 * gram1
    have hprod : 0 ≤ (kleinInner κ D F E₁ * (Dim.mk D F).side E₂)
        * (kleinInner κ D F E₂ * (Dim.mk D F).side E₁) := by
      have e : (kleinInner κ D F E₁ * (Dim.mk D F).side E₂)
          * (kleinInner κ D F E₂ * (Dim.mk D F).side E₁)
          = kleinInner κ D F E₁ * kleinInner κ D F E₂
            * ((Dim.mk D F).side E₁ * (Dim.mk D F).side E₂) := by ring
      rw [e]
      exact mul_nonneg hNN hs12.le
    have heq : kleinInner κ D F E₁ * (Dim.mk D F).side E₂
        = kleinInner κ D F E₂ * (Dim.mk D F).side E₁ := by
      have h1 : (kleinInner κ D F E₁ * (Dim.mk D F).side E₂
          - kleinInner κ D F E₂ * (Dim.mk D F).side E₁)
          * (kleinInner κ D F E₁ * (Dim.mk D F).side E₂
            + kleinInner κ D F E₂ * (Dim.mk D F).side E₁) = 0 := by
        linear_combination hmain
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · have ha : kleinInner κ D F E₁ * (Dim.mk D F).side E₂
            = -(kleinInner κ D F E₂ * (Dim.mk D F).side E₁) := by linarith
        rw [ha] at hprod
        have hb : kleinInner κ D F E₂ * (Dim.mk D F).side E₁ = 0 := by
          nlinarith [sq_nonneg (kleinInner κ D F E₂ * (Dim.mk D F).side E₁)]
        rw [ha, hb]
        ring
    have hplucker : kleinInner κ D F F * (Dim.mk D E₁).side E₂
        = kleinInner κ D F E₁ * (Dim.mk D F).side E₂
          - kleinInner κ D F E₂ * (Dim.mk D F).side E₁ := by
      simp only [kleinInner, Dim.side, Dim.dir, cross]
      ring
    have hcross : (Dim.mk D E₁).side E₂ = 0 := by
      have h : kleinInner κ D F F * (Dim.mk D E₁).side E₂ = 0 := by
        rw [hplucker, heq, sub_self]
      exact (mul_eq_zero.mp h).resolve_left hgU.ne'
    have hv1 : ((E₁.1 - D.1, E₁.2 - D.2) : ℝ × ℝ) ≠ (0, 0) := by
      intro h
      apply hE1D
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [] at h1 h2
      exact Prod.ext (by linarith) (by linarith)
    obtain ⟨l, hl⟩ := exists_mul_of_cross_eq_zero hv1 hcross
    have h1 := congrArg Prod.fst hl
    have h2 := congrArg Prod.snd hl
    simp only [] at h1 h2
    have hs2l : (Dim.mk D F).side E₂ = l * (Dim.mk D F).side E₁ := by
      simp only [Dim.side, Dim.dir, cross]
      linear_combination (F.1 - D.1) * h2 - (F.2 - D.2) * h1
    have hl0 : 0 < l := by
      have h : 0 < l * (Dim.mk D F).side E₁ ^ 2 := by
        have e : l * (Dim.mk D F).side E₁ ^ 2
            = (Dim.mk D F).side E₁ * (Dim.mk D F).side E₂ := by
          rw [hs2l]
          ring
        rw [e]
        exact hs12
      exact (mul_pos_iff_of_pos_right (by positivity)).mp h
    refine ⟨l, hl0, Prod.ext ?_ ?_⟩
    · simp only [Dim.pt]
      linarith
    · simp only [Dim.pt]
      linarith

end Congruence

section Apart

open Real

/-! ## A ray, as Hilbert has it -/

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

end Apart

end HyperbolicPlane
