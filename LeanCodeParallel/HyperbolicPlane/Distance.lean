/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import LeanCodeParallel.HyperbolicPlane.Metric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Klein's distance

`kleinDist` is the least length of a path between two points, the length measured with Klein's
metric: the infimum of the lengths of the maps of `[0, 1]` into the plane with a continuous
derivative. The two motions keep it, and under a negative bound `apart` is
`sinh² (√(-κ) d) / (-κ)`, where `d` is the distance (Theorem H18).

## Contents

* Theorem H18, Klein's distance, and `apart` as a function of it: `IsKleinPath`, `kleinLength`,
  `kleinDist`, `kleinLength_nonneg`, `segment_isKleinPath`, `kleinDist_nonempty`,
  `kleinDist_bddBelow`, `kleinLength_integrand_continuousOn`, `isKleinPath_map`,
  `kleinDist_map_le`, `shift_contDiffOn`, `shift_kleinDist`, `rot_kleinDist`, `axisDist`,
  `axisDist_zero`, `hasDerivAt_axisDist`, `axis_le_metric`, `axisDist_sub_le_kleinLength`,
  `axis_isKleinPath`, `axis_kleinLength`, `kleinDist_axis`, `exists_rot_to_axis`,
  `kleinDist_eq_arsinh`, `apart_eq_sinh_kleinDist`
-/

namespace HyperbolicPlane

open Pairs

/-! ## Klein's distance

Klein's distance is the least length of a path, the length measured with Klein's metric. Under
a negative bound, `apart` is a function of it. -/

section Distance

open Set Filter Topology Real

/-- **A path of the plane from `P` to `Q`**: a map of `[0, 1]` into the plane, with a continuous
derivative, from `P` to `Q`. -/
def IsKleinPath (κ : ℝ) (γ : ℝ → ℝ × ℝ) (P Q : ℝ × ℝ) : Prop :=
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) (plane κ) ∧ γ 0 = P ∧ γ 1 = Q

/-- **The length of a path** in Klein's metric: the integral, over `[0, 1]`, of the square root
of the metric of its derivative. -/
noncomputable def kleinLength (κ : ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    √(kleinMetric κ (γ t) (derivWithin γ (Icc 0 1) t) (derivWithin γ (Icc 0 1) t))

/-- **Klein's distance** between two points: the least length of a path from the one to the
other, as an infimum. -/
noncomputable def kleinDist (κ : ℝ) (P Q : ℝ × ℝ) : ℝ :=
  sInf (kleinLength κ '' {γ | IsKleinPath κ γ P Q})

/-- A length is not negative. -/
theorem kleinLength_nonneg (κ : ℝ) (γ : ℝ → ℝ × ℝ) : 0 ≤ kleinLength κ γ :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sqrt_nonneg _)

/-- The segment from `P` to `Q` is a path of the plane. -/
theorem segment_isKleinPath {κ : ℝ} {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    IsKleinPath κ (Dim.mk P Q).pt P Q := by
  refine ⟨?_, fun t ht => plane_convex κ hP hQ ht.1 ht.2, Dim.pt_zero _, Dim.pt_one _⟩
  have : ContDiff ℝ 1 (Dim.mk P Q).pt := by
    unfold Dim.pt
    fun_prop
  exact this.contDiffOn

/-- Two points of the plane have a path between them. -/
theorem kleinDist_nonempty {κ : ℝ} {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    (kleinLength κ '' {γ | IsKleinPath κ γ P Q}).Nonempty :=
  ⟨_, _, segment_isKleinPath hP hQ, rfl⟩

/-- The lengths are bounded below, by 0. -/
theorem kleinDist_bddBelow (κ : ℝ) (P Q : ℝ × ℝ) :
    BddBelow (kleinLength κ '' {γ | IsKleinPath κ γ P Q}) :=
  ⟨0, by rintro _ ⟨γ, -, rfl⟩; exact kleinLength_nonneg κ γ⟩

/-- The integrand of the length is continuous. -/
theorem kleinLength_integrand_continuousOn {κ : ℝ} {γ : ℝ → ℝ × ℝ} {P Q : ℝ × ℝ}
    (h : IsKleinPath κ γ P Q) :
    ContinuousOn (fun t => √(kleinMetric κ (γ t) (derivWithin γ (Icc 0 1) t)
      (derivWithin γ (Icc 0 1) t))) (Icc 0 1) := by
  have hγ : ContinuousOn γ (Icc 0 1) := h.1.continuousOn
  have hv : ContinuousOn (derivWithin γ (Icc 0 1)) (Icc 0 1) :=
    h.1.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl
  have hB : ∀ t ∈ Icc (0 : ℝ) 1, (1 + κ * ((γ t).1 ^ 2 + (γ t).2 ^ 2)) ^ 2 ≠ 0 :=
    fun t ht => pow_ne_zero 2 (mem_plane.mp (h.2.1 ht)).ne'
  unfold kleinMetric cross
  apply ContinuousOn.sqrt
  apply ContinuousOn.div _ _ hB
  · fun_prop
  · fun_prop

/-- **A motion that keeps the plane and Klein's metric keeps paths and their lengths.** -/
theorem isKleinPath_map {κ : ℝ} {M : ℝ × ℝ → ℝ × ℝ} (hM : ContDiffOn ℝ 1 M (plane κ))
    (hMp : MapsTo M (plane κ) (plane κ)) (hMd : ∀ p ∈ plane κ, DifferentiableAt ℝ M p)
    (hMg : ∀ p ∈ plane κ, ∀ v, kleinMetric κ (M p) (fderiv ℝ M p v) (fderiv ℝ M p v)
      = kleinMetric κ p v v)
    {γ : ℝ → ℝ × ℝ} {P Q : ℝ × ℝ} (h : IsKleinPath κ γ P Q) :
    IsKleinPath κ (M ∘ γ) (M P) (M Q) ∧ kleinLength κ (M ∘ γ) = kleinLength κ γ := by
  obtain ⟨hγ, hmaps, h0, h1⟩ := h
  refine ⟨⟨hM.comp hγ hmaps, hMp.comp hmaps, by simp [h0], by simp [h1]⟩, ?_⟩
  unfold kleinLength
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hd : derivWithin (M ∘ γ) (Icc 0 1) t = fderiv ℝ M (γ t) (derivWithin γ (Icc 0 1) t) :=
    ((hMd _ (hmaps ht)).hasFDerivAt.comp_hasDerivWithinAt t
      ((hγ.differentiableOn one_ne_zero t ht).hasDerivWithinAt)).derivWithin
      (uniqueDiffOn_Icc_zero_one t ht)
  simp only [Function.comp_apply, hd, hMg _ (hmaps ht)]

/-- **A motion that keeps the plane and Klein's metric does not make distances longer.** -/
theorem kleinDist_map_le {κ : ℝ} {M : ℝ × ℝ → ℝ × ℝ} (hM : ContDiffOn ℝ 1 M (plane κ))
    (hMp : MapsTo M (plane κ) (plane κ)) (hMd : ∀ p ∈ plane κ, DifferentiableAt ℝ M p)
    (hMg : ∀ p ∈ plane κ, ∀ v, kleinMetric κ (M p) (fderiv ℝ M p v) (fderiv ℝ M p v)
      = kleinMetric κ p v v)
    {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    kleinDist κ (M P) (M Q) ≤ kleinDist κ P Q := by
  apply csInf_le_csInf (kleinDist_bddBelow κ _ _) (kleinDist_nonempty hP hQ)
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨hpath, hlen⟩ := isKleinPath_map hM hMp hMd hMg hγ
  exact ⟨M ∘ γ, hpath, hlen⟩

/-- The motion along the first axis has a continuous derivative on the plane. -/
theorem shift_contDiffOn {κ a w : ℝ} (hκ : κ ≤ 0) (ha : 0 < 1 + κ * a ^ 2) :
    ContDiffOn ℝ 1 (shift κ a w) (plane κ) := by
  unfold shift
  simp only [div_eq_mul_inv]
  have hD : ∀ p ∈ plane κ, 1 - κ * a * p.1 ≠ 0 := fun p hp => (shift_den_pos hκ ha hp).ne'
  apply ContDiffOn.prodMk
  · exact ContDiffOn.mul (by fun_prop) (ContDiffOn.inv (by fun_prop) hD)
  · exact ContDiffOn.mul (by fun_prop) (ContDiffOn.inv (by fun_prop) hD)

/-- **The motion along the first axis keeps Klein's distance.** -/
theorem shift_kleinDist {κ a w : ℝ} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {P Q : ℝ × ℝ} (hP : P ∈ plane κ) (hQ : Q ∈ plane κ) :
    kleinDist κ (shift κ a w P) (shift κ a w Q) = kleinDist κ P Q := by
  have hw2 : 0 < w ^ 2 := lt_of_le_of_ne (sq_nonneg w) (pow_ne_zero 2 hw0).symm
  have ha : 0 < 1 + κ * a ^ 2 := hw ▸ hw2
  have hw' : w ^ 2 = 1 + κ * (-a) ^ 2 := by rw [hw]; ring
  have ha' : 0 < 1 + κ * (-a) ^ 2 := hw' ▸ hw2
  have key : ∀ b : ℝ, w ^ 2 = 1 + κ * b ^ 2 → 0 < 1 + κ * b ^ 2 → ∀ X Y : ℝ × ℝ,
      X ∈ plane κ → Y ∈ plane κ → kleinDist κ (shift κ b w X) (shift κ b w Y) ≤ kleinDist κ X Y :=
    fun b hb hb' X Y hX hY => kleinDist_map_le (shift_contDiffOn hκ hb')
      (fun p hp => shift_mem_plane hκ hb hw0 hp)
      (fun p hp => shift_differentiableAt (shift_den_pos hκ hb' hp).ne')
      (fun p hp v => shift_kleinMetric_fderiv hκ hb hw0 hp v v) hX hY
  apply le_antisymm (key a hw ha P Q hP hQ)
  have h := key (-a) hw' ha' _ _ (shift_mem_plane hκ hw hw0 hP) (shift_mem_plane hκ hw hw0 hQ)
  rwa [shift_neg_shift hκ hw hw0 hP, shift_neg_shift hκ hw hw0 hQ] at h

/-- **Turning keeps Klein's distance.** -/
theorem rot_kleinDist {κ c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : kleinDist κ (rot c s P) (rot c s Q) = kleinDist κ P Q := by
  have h' : c ^ 2 + (-s) ^ 2 = 1 := by rw [← h]; ring
  have key : ∀ s' : ℝ, c ^ 2 + s' ^ 2 = 1 → ∀ X Y : ℝ × ℝ,
      X ∈ plane κ → Y ∈ plane κ → kleinDist κ (rot c s' X) (rot c s' Y) ≤ kleinDist κ X Y := by
    intro s' hs' X Y hX hY
    have hrot : ContDiff ℝ 1 (rot c s') := by
      unfold rot
      fun_prop
    exact kleinDist_map_le hrot.contDiffOn (fun p hp => (rot_mem_plane hs').mpr hp)
      (fun p _ => hrot.differentiable one_ne_zero p)
      (fun p _ v => rot_kleinMetric_fderiv hs' κ p v v) hX hY
  apply le_antisymm (key s h P Q hP hQ)
  have hh := key (-s) h' _ _ ((rot_mem_plane h).mpr hP) ((rot_mem_plane h).mpr hQ)
  rwa [rot_rot_neg h, rot_rot_neg h] at hh

/-- Klein's distance from `(0, 0)` to the number `x` of the first axis, under a negative
bound. -/
noncomputable def axisDist (κ x : ℝ) : ℝ := arsinh (√(-κ) * x / √(1 + κ * x ^ 2)) / √(-κ)

/-- The distance from `(0, 0)` to itself is 0. -/
theorem axisDist_zero (κ : ℝ) : axisDist κ 0 = 0 := by
  simp [axisDist]

/-- The derivative of `axisDist` is `1 / (1 + κ x²)`. -/
theorem hasDerivAt_axisDist {κ x : ℝ} (hκ : κ < 0) (hx : 0 < 1 + κ * x ^ 2) :
    HasDerivAt (axisDist κ) (1 / (1 + κ * x ^ 2)) x := by
  have hs : 0 < √(-κ) := sqrt_pos.mpr (neg_pos.mpr hκ)
  have hs2 : √(-κ) ^ 2 = -κ := sq_sqrt (neg_nonneg.mpr hκ.le)
  have hq : 0 < √(1 + κ * x ^ 2) := sqrt_pos.mpr hx
  have hq2 : √(1 + κ * x ^ 2) ^ 2 = 1 + κ * x ^ 2 := sq_sqrt hx.le
  have hb : HasDerivAt (fun y : ℝ => 1 + κ * y ^ 2) (2 * κ * x) x := by
    have := ((hasDerivAt_pow 2 x).const_mul κ).const_add 1
    convert this using 1
    norm_num
    ring
  have hu := ((hasDerivAt_id' x).const_mul (√(-κ))).fun_div (hb.sqrt hx.ne') hq.ne'
  have ha := hu.arsinh.div_const (√(-κ))
  have h1u : 1 + (√(-κ) * x / √(1 + κ * x ^ 2)) ^ 2 = (1 / √(1 + κ * x ^ 2)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, hs2, hq2]
    field_simp
    ring
  have hsq1 : √(1 + (√(-κ) * x / √(1 + κ * x ^ 2)) ^ 2) = 1 / √(1 + κ * x ^ 2) := by
    rw [h1u, sqrt_sq (by positivity)]
  unfold axisDist
  convert ha using 1
  rw [hsq1, smul_eq_mul]
  field_simp
  rw [hq2]
  ring

/-- **Along the first axis, a direction is no longer in Klein's metric than its first
entry, divided by `1 + κ x²`.** The proof is the identity
`c N - B v₁² = (κ x y v₁ - c v₂)²`, where `c = 1 + κ x²`, `B` is the bound at the point and
`N` is the numerator of the metric. -/
theorem axis_le_metric {κ : ℝ} (hκ : κ ≤ 0) {p : ℝ × ℝ} (hp : p ∈ plane κ) (v : ℝ × ℝ) :
    1 / (1 + κ * p.1 ^ 2) * v.1 ≤ √(kleinMetric κ p v v) := by
  have hB := mem_plane.mp hp
  have hBc : 1 + κ * (p.1 ^ 2 + p.2 ^ 2) ≤ 1 + κ * p.1 ^ 2 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hκ (sq_nonneg p.2)]
  have hc : 0 < 1 + κ * p.1 ^ 2 := lt_of_lt_of_le hB hBc
  have key : (1 + κ * p.1 ^ 2) * (v.1 * v.1 + v.2 * v.2 + κ * cross p v * cross p v)
      - (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) * v.1 ^ 2
      = (κ * p.1 * p.2 * v.1 - (1 + κ * p.1 ^ 2) * v.2) ^ 2 := by
    simp only [cross]
    ring
  have hcN : (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) * v.1 ^ 2
      ≤ (1 + κ * p.1 ^ 2) * (v.1 * v.1 + v.2 * v.2 + κ * cross p v * cross p v) := by
    nlinarith [sq_nonneg (κ * p.1 * p.2 * v.1 - (1 + κ * p.1 ^ 2) * v.2)]
  have hN : 0 ≤ (1 + κ * p.1 ^ 2) * (v.1 * v.1 + v.2 * v.2 + κ * cross p v * cross p v) :=
    le_trans (mul_nonneg hB.le (sq_nonneg _)) hcN
  have hsq : (1 / (1 + κ * p.1 ^ 2) * v.1) ^ 2 ≤ kleinMetric κ p v v := by
    unfold kleinMetric
    rw [show (1 / (1 + κ * p.1 ^ 2) * v.1) ^ 2 = v.1 ^ 2 / (1 + κ * p.1 ^ 2) ^ 2 by
        rw [mul_pow, div_pow, one_pow, one_div, inv_mul_eq_div],
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcN hB.le, mul_le_mul_of_nonneg_right hBc hN]
  exact (le_abs_self _).trans (abs_le_sqrt hsq)

/-- **Every path is at least as long as the distance along the first axis between the first
entries of its ends.** -/
theorem axisDist_sub_le_kleinLength {κ : ℝ} (hκ : κ < 0) {γ : ℝ → ℝ × ℝ} {P Q : ℝ × ℝ}
    (h : IsKleinPath κ γ P Q) : axisDist κ Q.1 - axisDist κ P.1 ≤ kleinLength κ γ := by
  obtain ⟨hγ, hmaps, h0, h1⟩ := h
  have hx : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 + κ * (γ t).1 ^ 2 := fun t ht => by
    have := mem_plane.mp (hmaps ht)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hκ.le (sq_nonneg (γ t).2)]
  have hcont : ContinuousOn (fun t => axisDist κ (γ t).1) (Icc 0 1) := fun t ht =>
    ContinuousAt.comp_continuousWithinAt (f := fun t => (γ t).1)
      (hasDerivAt_axisDist hκ (hx t ht)).continuousAt (hγ.continuousOn t ht).fst
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun t => axisDist κ (γ t).1)
      (1 / (1 + κ * (γ t).1 ^ 2) * (derivWithin γ (Icc 0 1) t).1) (Ioi t) t := by
    intro t ht
    have hmem : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hd : HasDerivAt γ (derivWithin γ (Icc 0 1) t) t := by
      rw [derivWithin_of_mem_nhds hmem]
      exact ((hγ.differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).differentiableAt
        hmem).hasDerivAt
    have hd1 : HasDerivAt (fun t => (γ t).1) (derivWithin γ (Icc 0 1) t).1 t := by
      have := (hasFDerivAt_fst (𝕜 := ℝ) (p := γ t)).comp_hasDerivAt t hd
      exact this
    exact ((hasDerivAt_axisDist hκ (hx t (Ioo_subset_Icc_self ht))).comp t hd1).hasDerivWithinAt
  have hint := (kleinLength_integrand_continuousOn ⟨hγ, hmaps, h0, h1⟩).integrableOn_Icc
    (μ := MeasureTheory.volume)
  have hle : ∀ t ∈ Ioo (0 : ℝ) 1, 1 / (1 + κ * (γ t).1 ^ 2) * (derivWithin γ (Icc 0 1) t).1
      ≤ √(kleinMetric κ (γ t) (derivWithin γ (Icc 0 1) t) (derivWithin γ (Icc 0 1) t)) :=
    fun t ht => axis_le_metric hκ.le (hmaps (Ioo_subset_Icc_self ht)) _
  have := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le zero_le_one hcont hderiv hint hle
  simp only [h0, h1] at this
  exact this

/-- The path along the first axis from `(0, 0)` to `(r, 0)`. -/
theorem axis_isKleinPath {κ r : ℝ} (hκ : κ ≤ 0) (hr : (r, (0 : ℝ)) ∈ plane κ) :
    IsKleinPath κ (fun t => (t * r, 0)) (0, 0) (r, 0) := by
  refine ⟨(by fun_prop : ContDiff ℝ 1 fun t : ℝ => (t * r, (0 : ℝ))).contDiffOn, ?_, by simp,
    by simp⟩
  intro t ht
  have hr' := mem_plane.mp hr
  simp only at hr'
  rw [mem_plane]
  simp only
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg r), mul_nonpos_of_nonpos_of_nonneg hκ
    (sq_nonneg r)]

/-- **The path along the first axis has the length `axisDist`.** -/
theorem axis_kleinLength {κ r : ℝ} (hκ : κ < 0) (hr0 : 0 ≤ r) (hr : (r, (0 : ℝ)) ∈ plane κ) :
    kleinLength κ (fun t => (t * r, 0)) = axisDist κ r := by
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 + κ * (t * r) ^ 2 := fun t ht => by
    have := mem_plane.mp ((axis_isKleinPath hκ.le hr).2.1 ht)
    simp only at this
    linarith
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      derivWithin (fun t => (t * r, (0 : ℝ))) (Icc 0 1) t = (r, 0) := fun t ht =>
    (((hasDerivAt_mul_const r).prodMk (hasDerivAt_const t (0 : ℝ))).hasDerivWithinAt).derivWithin
      (uniqueDiffOn_Icc_zero_one t ht)
  have hint : ∀ t ∈ uIcc (0 : ℝ) 1,
      √(kleinMetric κ (t * r, 0) (derivWithin (fun t => (t * r, (0 : ℝ))) (Icc 0 1) t)
        (derivWithin (fun t => (t * r, (0 : ℝ))) (Icc 0 1) t))
      = 1 / (1 + κ * (t * r) ^ 2) * r := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [hderiv t ht]
    have hp := hpos t ht
    have e : kleinMetric κ (t * r, 0) (r, 0) (r, 0) = (1 / (1 + κ * (t * r) ^ 2) * r) ^ 2 := by
      simp only [kleinMetric, cross]
      field_simp
      ring
    rw [e, sqrt_sq (by positivity)]
  unfold kleinLength
  rw [intervalIntegral.integral_congr hint,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => axisDist κ (t * r))]
  · simp [axisDist_zero]
  · intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact (hasDerivAt_axisDist hκ (hpos t ht)).comp t (hasDerivAt_mul_const r)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    apply ContinuousOn.mul _ continuousOn_const
    exact ContinuousOn.div continuousOn_const (by fun_prop) (fun t ht => (hpos t ht).ne')

/-- **Klein's distance from `(0, 0)` to `(r, 0)` is `axisDist`.** -/
theorem kleinDist_axis {κ r : ℝ} (hκ : κ < 0) (hr0 : 0 ≤ r) (hr : (r, (0 : ℝ)) ∈ plane κ) :
    kleinDist κ (0, 0) (r, 0) = axisDist κ r := by
  apply le_antisymm
  · rw [← axis_kleinLength hκ hr0 hr]
    exact csInf_le (kleinDist_bddBelow κ _ _) ⟨_, axis_isKleinPath hκ.le hr, rfl⟩
  · apply le_csInf (kleinDist_nonempty (zero_mem_plane κ) hr)
    rintro _ ⟨γ, hγ, rfl⟩
    have := axisDist_sub_le_kleinLength hκ hγ
    simpa [axisDist_zero] using this

/-- A turn takes every pair to the first axis, on the side of the positive numbers. -/
theorem exists_rot_to_axis (Q : ℝ × ℝ) :
    ∃ c s r : ℝ, c ^ 2 + s ^ 2 = 1 ∧ 0 ≤ r ∧ rot c s Q = (r, 0) := by
  by_cases h0 : Q.1 ^ 2 + Q.2 ^ 2 = 0
  · have h1 : Q.1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg Q.2])
    have h2 : Q.2 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by nlinarith [sq_nonneg Q.1])
    exact ⟨1, 0, 0, by norm_num, le_rfl, by simp [rot, h1, h2]⟩
  · have hpos : 0 < Q.1 ^ 2 + Q.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    obtain ⟨r, hr0, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = Q.1 ^ 2 + Q.2 ^ 2 :=
      ⟨√(Q.1 ^ 2 + Q.2 ^ 2), sqrt_pos.mpr hpos, sq_sqrt hpos.le⟩
    refine ⟨Q.1 / r, -Q.2 / r, r, ?_, hr0.le, ?_⟩
    · field_simp
      linear_combination -hr2
    · apply Prod.ext
      · simp only [rot]
        field_simp
        linear_combination -hr2
      · simp only [rot]
        ring

/-- **Theorem H18. Klein's distance**, under a negative bound, between two points of the
plane: `arsinh √(-κ apart) / √(-κ)`. -/
theorem kleinDist_eq_arsinh {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : kleinDist κ P Q = arsinh (√(-κ * apart κ P Q)) / √(-κ) := by
  obtain ⟨c, s, a, w, hcs, hw, hw0, hPc⟩ := exists_motion_to_centre hP
  have hrP : rot c s P ∈ plane κ := (rot_mem_plane hcs).mpr hP
  have hrQ : rot c s Q ∈ plane κ := (rot_mem_plane hcs).mpr hQ
  have hQ1 : shift κ a w (rot c s Q) ∈ plane κ := shift_mem_plane hκ.le hw hw0.ne' hrQ
  obtain ⟨c2, s2, r, hcs2, hr0, hQ2⟩ := exists_rot_to_axis (shift κ a w (rot c s Q))
  have hr : (r, (0 : ℝ)) ∈ plane κ := hQ2 ▸ (rot_mem_plane hcs2).mpr hQ1
  have hrot0 : rot c2 s2 ((0 : ℝ), (0 : ℝ)) = (0, 0) := by simp [rot]
  have hd : kleinDist κ P Q = kleinDist κ (0, 0) (r, 0) :=
    calc kleinDist κ P Q = kleinDist κ (rot c s P) (rot c s Q) := (rot_kleinDist hcs hP hQ).symm
      _ = kleinDist κ (shift κ a w (rot c s P)) (shift κ a w (rot c s Q)) :=
        (shift_kleinDist hκ.le hw hw0.ne' hrP hrQ).symm
      _ = kleinDist κ (rot c2 s2 (0, 0)) (rot c2 s2 (shift κ a w (rot c s Q))) := by
        rw [hPc, rot_kleinDist hcs2 (zero_mem_plane κ) hQ1]
      _ = kleinDist κ (0, 0) (r, 0) := by rw [hrot0, hQ2]
  have ha : apart κ P Q = r ^ 2 / (1 + κ * r ^ 2) :=
    calc apart κ P Q = apart κ (rot c s P) (rot c s Q) := (rot_apart hcs κ P Q).symm
      _ = apart κ (shift κ a w (rot c s P)) (shift κ a w (rot c s Q)) :=
        (shift_apart_plane hκ.le hw hw0.ne' hrP hrQ).symm
      _ = apart κ (rot c2 s2 (0, 0)) (rot c2 s2 (shift κ a w (rot c s Q))) := by
        rw [hPc, rot_apart hcs2]
      _ = r ^ 2 / (1 + κ * r ^ 2) := by rw [hrot0, hQ2, apart_centre]
  have hr1 : 0 < 1 + κ * r ^ 2 := by
    have := mem_plane.mp hr
    simp only at this
    linarith
  rw [hd, kleinDist_axis hκ hr0 hr, ha, axisDist, sqrt_mul (neg_nonneg.mpr hκ.le),
    sqrt_div' _ hr1.le, sqrt_sq hr0, mul_div_assoc]

/-- **Theorem H18. `apart` is a function of Klein's distance**:
`apart = sinh² (√(-κ) d) / (-κ)`, under a negative bound. -/
theorem apart_eq_sinh_kleinDist {κ : ℝ} (hκ : κ < 0) {P Q : ℝ × ℝ} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) : apart κ P Q = sinh (√(-κ) * kleinDist κ P Q) ^ 2 / (-κ) := by
  have hs : √(-κ) ≠ 0 := (sqrt_pos.mpr (neg_pos.mpr hκ)).ne'
  have ha : 0 ≤ apart κ P Q := by
    rcases eq_or_ne P Q with rfl | h
    · rw [apart_self]
    · exact (apart_pos hP hQ h).le
  have e : √(-κ) * (arsinh (√(-κ * apart κ P Q)) / √(-κ)) = arsinh (√(-κ * apart κ P Q)) := by
    field_simp
  rw [kleinDist_eq_arsinh hκ hP hQ, e, sinh_arsinh, sq_sqrt (mul_nonneg (neg_nonneg.mpr hκ.le) ha)]
  field_simp [hκ.ne]

end Distance

end HyperbolicPlane
