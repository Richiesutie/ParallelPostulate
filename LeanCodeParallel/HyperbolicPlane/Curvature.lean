/-
Copyright (c) 2026 Richard Sutton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Sutton
-/
import LeanCodeParallel.HyperbolicPlane.Metric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The curvature of Klein's metric

Mathlib has no curvature for a metric given by its coefficients, so `gaussCurvature` is
Brioschi's formula, with Mathlib's derivatives along the two axes. For Klein's metric it is `κ`
at every point of the plane, under every bound (Theorem H17); for the upper half plane of
Poincaré it is `-1`, a check of the formula.

## Contents

* Theorem H17, the curvature of Klein's metric is `κ`: `partialX`, `partialY`, `gaussCurvature`,
  `kleinE`, `kleinF`, `kleinG`, `kleinMetric_coords`, `kleinMetric_curvature`,
  `halfPlane_curvature`
* derivatives and determinants: `hasDerivAt_cubic`, `hasDerivAt_div_sq`, `hasDerivAt_div_cube`,
  `det_three`
-/

namespace HyperbolicPlane

open Pairs

/-! ## The curvature of Klein's metric

Mathlib has no curvature for a metric given by its coefficients, so the curvature here is
Brioschi's formula, with Mathlib's derivatives along the two axes. -/

section Curvature

open Filter Topology

/-- The derivative of `f` along the first axis at `p`. -/
noncomputable def partialX (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun t => f (t, p.2)) p.1

/-- The derivative of `f` along the second axis at `p`. -/
noncomputable def partialY (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (fun t => f (p.1, t)) p.2

/-- **The curvature of a metric**, `E dx² + 2 F dx dy + G dy²`, at `p`, by Brioschi's formula,
with the derivatives of Mathlib. -/
noncomputable def gaussCurvature (E F G : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Matrix.det !![-partialY (partialY E) p / 2 + partialX (partialY F) p
          - partialX (partialX G) p / 2, partialX E p / 2, partialX F p - partialY E p / 2;
        partialY F p - partialX G p / 2, E p, F p;
        partialY G p / 2, F p, G p]
    - Matrix.det !![0, partialY E p / 2, partialX G p / 2;
        partialY E p / 2, E p, F p;
        partialX G p / 2, F p, G p]) / (E p * G p - F p ^ 2) ^ 2

/-- The coefficient of `dx²` in Klein's metric. -/
noncomputable def kleinE (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 + κ * p.2 ^ 2) / (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) ^ 2
/-- The coefficient of `dx dy` in Klein's metric, taken twice. -/
noncomputable def kleinF (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  -κ * p.1 * p.2 / (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) ^ 2
/-- The coefficient of `dy²` in Klein's metric. -/
noncomputable def kleinG (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 + κ * p.1 ^ 2) / (1 + κ * (p.1 ^ 2 + p.2 ^ 2)) ^ 2

/-- **Klein's metric is `E dx² + 2 F dx dy + G dy²`**, with `kleinE`, `kleinF` and `kleinG`. -/
theorem kleinMetric_coords (κ : ℝ) (p u v : ℝ × ℝ) :
    kleinMetric κ p u v
      = kleinE κ p * u.1 * v.1 + kleinF κ p * (u.1 * v.2 + u.2 * v.1) + kleinG κ p * u.2 * v.2 := by
  simp only [kleinMetric, kleinE, kleinF, kleinG, cross]
  ring

/-- The derivative of a polynomial of degree at most 3. -/
theorem hasDerivAt_cubic (c0 c1 c2 c3 : ℝ) {f : ℝ → ℝ}
    (hf : ∀ s, f s = c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3) (t : ℝ) :
    HasDerivAt f (c1 + 2 * c2 * t + 3 * c3 * t ^ 2) t := by
  have e : f = fun s => c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3 := funext hf
  subst e
  have h1 : HasDerivAt (fun s : ℝ => c1 * s) (c1 * 1) t :=
    HasDerivAt.const_mul c1 (hasDerivAt_id' t)
  have h2 : HasDerivAt (fun s : ℝ => c2 * s ^ 2) (c2 * (↑2 * t ^ (2 - 1))) t :=
    HasDerivAt.const_mul c2 (hasDerivAt_pow 2 t)
  have h3 : HasDerivAt (fun s : ℝ => c3 * s ^ 3) (c3 * (↑3 * t ^ (3 - 1))) t :=
    HasDerivAt.const_mul c3 (hasDerivAt_pow 3 t)
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.add (hasDerivAt_const t c0) h1) h2) h3
  exact HasDerivAt.congr_deriv h (by norm_num; ring)

/-- The derivative of a quotient by a square. -/
theorem hasDerivAt_div_sq {f b : ℝ → ℝ} {f' b' t : ℝ} (hf : HasDerivAt f f' t)
    (hb : HasDerivAt b b' t) (h : b t ≠ 0) :
    HasDerivAt (fun s => f s / b s ^ 2) ((f' * b t - 2 * f t * b') / b t ^ 3) t := by
  convert hf.div (hb.pow 2) (pow_ne_zero 2 h) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- The derivative of a quotient by a cube. -/
theorem hasDerivAt_div_cube {f b : ℝ → ℝ} {f' b' t : ℝ} (hf : HasDerivAt f f' t)
    (hb : HasDerivAt b b' t) (h : b t ≠ 0) :
    HasDerivAt (fun s => f s / b s ^ 3) ((f' * b t - 3 * f t * b') / b t ^ 4) t := by
  convert hf.div (hb.pow 3) (pow_ne_zero 3 h) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- The determinant of a 3 × 3 matrix. -/
theorem det_three (a b c d e f g h i : ℝ) :
    Matrix.det !![a, b, c; d, e, f; g, h, i]
      = a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g := by
  rw [Matrix.det_fin_three]
  simp

/-- **Theorem H17. The curvature of Klein's metric is `κ`**, at every point of the plane, and
under every bound: negative, 0 or positive. -/
theorem kleinMetric_curvature {κ : ℝ} {P : ℝ × ℝ} (hP : P ∈ plane κ) :
    gaussCurvature (kleinE κ) (kleinF κ) (kleinG κ) P = κ := by
  obtain ⟨x, y⟩ := P
  replace hP := mem_plane.mp hP
  simp only at hP
  have hB : 1 + κ * (x ^ 2 + y ^ 2) ≠ 0 := hP.ne'
  have bX : ∀ c t : ℝ,
      HasDerivAt (fun s => 1 + κ * (s ^ 2 + c ^ 2)) (0 + 2 * κ * t + 3 * 0 * t ^ 2) t :=
    fun c t => hasDerivAt_cubic (1 + κ * c ^ 2) 0 κ 0 (fun s => by ring) t
  have bY : ∀ c t : ℝ,
      HasDerivAt (fun s => 1 + κ * (c ^ 2 + s ^ 2)) (0 + 2 * κ * t + 3 * 0 * t ^ 2) t :=
    fun c t => hasDerivAt_cubic (1 + κ * c ^ 2) 0 κ 0 (fun s => by ring) t
  have hEx : partialX (kleinE κ) (x, y)
      = -4 * κ * x * (1 + κ * y ^ 2) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialX kleinE
    refine ((hasDerivAt_div_sq (f := fun _ => 1 + κ * y ^ 2)
      (hasDerivAt_cubic (1 + κ * y ^ 2) 0 0 0 (fun s => by ring) x) (bX y x) hB).deriv).trans ?_
    field_simp
    ring
  have hEy : partialY (kleinE κ) (x, y)
      = 2 * κ * y * (κ * x ^ 2 - κ * y ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialY kleinE
    refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
      (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) y) (bY x y) hB).deriv).trans ?_
    field_simp
    ring
  have hFx : partialX (kleinF κ) (x, y)
      = κ * y * (3 * κ * x ^ 2 - κ * y ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialX kleinF
    refine ((hasDerivAt_div_sq (f := fun s => -κ * s * y)
      (hasDerivAt_cubic 0 (-κ * y) 0 0 (fun s => by ring) x) (bX y x) hB).deriv).trans ?_
    field_simp
    ring
  have hFy : partialY (kleinF κ) (x, y)
      = κ * x * (3 * κ * y ^ 2 - κ * x ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialY kleinF
    refine ((hasDerivAt_div_sq (f := fun s => -κ * x * s)
      (hasDerivAt_cubic 0 (-κ * x) 0 0 (fun s => by ring) y) (bY x y) hB).deriv).trans ?_
    field_simp
    ring
  have hGx : partialX (kleinG κ) (x, y)
      = 2 * κ * x * (κ * y ^ 2 - κ * x ^ 2 - 1) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialX kleinG
    refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
      (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) x) (bX y x) hB).deriv).trans ?_
    field_simp
    ring
  have hGy : partialY (kleinG κ) (x, y)
      = -4 * κ * y * (1 + κ * x ^ 2) / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    unfold partialY kleinG
    refine ((hasDerivAt_div_sq (f := fun _ => 1 + κ * x ^ 2)
      (hasDerivAt_cubic (1 + κ * x ^ 2) 0 0 0 (fun s => by ring) y) (bY x y) hB).deriv).trans ?_
    field_simp
    ring
  have nX : ∀ᶠ t in 𝓝 x, 1 + κ * (t ^ 2 + y ^ 2) ≠ 0 :=
    (show Continuous fun t : ℝ => 1 + κ * (t ^ 2 + y ^ 2) by fun_prop).continuousAt.eventually_ne hB
  have nY : ∀ᶠ t in 𝓝 y, 1 + κ * (x ^ 2 + t ^ 2) ≠ 0 :=
    (show Continuous fun t : ℝ => 1 + κ * (x ^ 2 + t ^ 2) by fun_prop).continuousAt.eventually_ne hB
  have hEyy : partialY (partialY (kleinE κ)) (x, y)
      = ((2 * κ ^ 2 * x ^ 2 - 2 * κ - 6 * κ ^ 2 * y ^ 2) * (1 + κ * (x ^ 2 + y ^ 2))
        - 6 * κ * y * ((2 * κ ^ 2 * x ^ 2 - 2 * κ) * y - 2 * κ ^ 2 * y ^ 3))
          / (1 + κ * (x ^ 2 + y ^ 2)) ^ 4 := by
    have e : (fun t => partialY (kleinE κ) (x, t)) =ᶠ[𝓝 y]
        fun t => ((2 * κ ^ 2 * x ^ 2 - 2 * κ) * t - 2 * κ ^ 2 * t ^ 3)
          / (1 + κ * (x ^ 2 + t ^ 2)) ^ 3 := by
      filter_upwards [nY] with t ht
      unfold partialY kleinE
      refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
        (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) t) (bY x t) ht).deriv).trans ?_
      ring
    unfold partialY at e ⊢
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube
      (hasDerivAt_cubic 0 (2 * κ ^ 2 * x ^ 2 - 2 * κ) 0 (-2 * κ ^ 2) (fun s => by ring) y)
      (bY x y) hB).deriv).trans ?_
    ring
  have hGxx : partialX (partialX (kleinG κ)) (x, y)
      = ((2 * κ ^ 2 * y ^ 2 - 2 * κ - 6 * κ ^ 2 * x ^ 2) * (1 + κ * (x ^ 2 + y ^ 2))
        - 6 * κ * x * ((2 * κ ^ 2 * y ^ 2 - 2 * κ) * x - 2 * κ ^ 2 * x ^ 3))
          / (1 + κ * (x ^ 2 + y ^ 2)) ^ 4 := by
    have e : (fun t => partialX (kleinG κ) (t, y)) =ᶠ[𝓝 x]
        fun t => ((2 * κ ^ 2 * y ^ 2 - 2 * κ) * t - 2 * κ ^ 2 * t ^ 3)
          / (1 + κ * (t ^ 2 + y ^ 2)) ^ 3 := by
      filter_upwards [nX] with t ht
      unfold partialX kleinG
      refine ((hasDerivAt_div_sq (f := fun s => 1 + κ * s ^ 2)
        (hasDerivAt_cubic 1 0 κ 0 (fun s => by ring) t) (bX y t) ht).deriv).trans ?_
      ring
    unfold partialX at e ⊢
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube
      (hasDerivAt_cubic 0 (2 * κ ^ 2 * y ^ 2 - 2 * κ) 0 (-2 * κ ^ 2) (fun s => by ring) x)
      (bX y x) hB).deriv).trans ?_
    ring
  have hFxy : partialX (partialY (kleinF κ)) (x, y)
      = ((3 * κ ^ 2 * y ^ 2 - κ - 3 * κ ^ 2 * x ^ 2) * (1 + κ * (x ^ 2 + y ^ 2))
        - 6 * κ * x * ((3 * κ ^ 2 * y ^ 2 - κ) * x - κ ^ 2 * x ^ 3))
          / (1 + κ * (x ^ 2 + y ^ 2)) ^ 4 := by
    have e : (fun t => partialY (kleinF κ) (t, y)) =ᶠ[𝓝 x]
        fun t => ((3 * κ ^ 2 * y ^ 2 - κ) * t - κ ^ 2 * t ^ 3)
          / (1 + κ * (t ^ 2 + y ^ 2)) ^ 3 := by
      filter_upwards [nX] with t ht
      unfold partialY kleinF
      refine ((hasDerivAt_div_sq (f := fun s => -κ * t * s)
        (hasDerivAt_cubic 0 (-κ * t) 0 0 (fun s => by ring) y) (bY t y) ht).deriv).trans ?_
      ring
    unfold partialX
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube
      (hasDerivAt_cubic 0 (3 * κ ^ 2 * y ^ 2 - κ) 0 (-κ ^ 2) (fun s => by ring) x)
      (bX y x) hB).deriv).trans ?_
    ring
  have hdet : kleinE κ (x, y) * kleinG κ (x, y) - kleinF κ (x, y) ^ 2
      = 1 / (1 + κ * (x ^ 2 + y ^ 2)) ^ 3 := by
    simp only [kleinE, kleinF, kleinG]
    field_simp
    ring
  unfold gaussCurvature
  rw [hdet, hEx, hEy, hFx, hFy, hGx, hGy, hEyy, hGxx, hFxy, det_three, det_three]
  simp only [kleinE, kleinF, kleinG]
  field_simp
  ring

/-- **A check of `gaussCurvature`: the upper half plane of Poincaré has the curvature `-1`.**
Its metric is `(dx² + dy²) / y²`, and its curvature is known to be `-1`. -/
theorem halfPlane_curvature {p : ℝ × ℝ} (hp : 0 < p.2) :
    gaussCurvature (fun q => 1 / q.2 ^ 2) (fun _ => 0) (fun q => 1 / q.2 ^ 2) p = -1 := by
  obtain ⟨x, y⟩ := p
  simp only at hp
  have hEx : partialX (fun q : ℝ × ℝ => 1 / q.2 ^ 2) (x, y) = 0 := by
    simp [partialX]
  have hEy : partialY (fun q : ℝ × ℝ => 1 / q.2 ^ 2) (x, y) = -2 / y ^ 3 := by
    unfold partialY
    refine ((hasDerivAt_div_sq (f := fun _ => 1) (hasDerivAt_const y 1) (hasDerivAt_id' y)
      hp.ne').deriv).trans ?_
    ring
  have hExx : partialX (partialX (fun q : ℝ × ℝ => 1 / q.2 ^ 2)) (x, y) = 0 := by
    simp [partialX]
  have hEyy : partialY (partialY (fun q : ℝ × ℝ => 1 / q.2 ^ 2)) (x, y) = 6 / y ^ 4 := by
    have e : (fun t => partialY (fun q : ℝ × ℝ => 1 / q.2 ^ 2) (x, t)) =ᶠ[𝓝 y]
        fun t => -2 / t ^ 3 := by
      filter_upwards [eventually_gt_nhds hp] with t ht
      unfold partialY
      refine ((hasDerivAt_div_sq (f := fun _ => 1) (hasDerivAt_const t 1) (hasDerivAt_id' t)
        ht.ne').deriv).trans ?_
      ring
    unfold partialY at e ⊢
    rw [e.deriv_eq]
    refine ((hasDerivAt_div_cube (f := fun _ => -2) (hasDerivAt_const y (-2)) (hasDerivAt_id' y)
      hp.ne').deriv).trans ?_
    ring
  have hF : ∀ q : ℝ × ℝ, partialX (fun _ : ℝ × ℝ => (0 : ℝ)) q = 0 ∧
      partialY (fun _ : ℝ × ℝ => (0 : ℝ)) q = 0 := fun q => by simp [partialX, partialY]
  have hFxy : partialX (partialY (fun _ : ℝ × ℝ => (0 : ℝ))) (x, y) = 0 := by
    simp [partialX, partialY]
  unfold gaussCurvature
  rw [hEx, hEy, hExx, hEyy, (hF _).1, (hF _).2, hFxy, det_three, det_three]
  field_simp
  ring

end Curvature

end HyperbolicPlane
