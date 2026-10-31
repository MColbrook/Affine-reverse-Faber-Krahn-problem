module

public import AffineFK.OUDensityPDEGradientKernel
public import AffineFK.GaussianSmoothingRegularity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The actual spatial density derivative and its ordinary time derivative

Spatial differentiation of the actual Gaussian mixture gives a Bochner
integral of the actual Gaussian derivative. The Banach-valued OU kernel
differentiation theorem then supplies its genuine time derivative.
All Gaussian derivative bounds are proved inputs from the frozen kernel
development; there is no desired mixed-derivative premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ContDiff

theorem gaussianSmoothingDensity_fderiv_eq_integral (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (gaussianSmoothingDensity n ν a b) x =
      (b⁻¹) ^ (n + 1) • (∫ u, fderiv ℝ (standardGaussianDensity n)
        (b⁻¹ • (x - a • u)) ∂ν) := by
  let E := EuclideanSpace ℝ (Fin n)
  let r := b⁻¹
  obtain ⟨C₀, _, hC₀⟩ := standardGaussianDensity_iteratedFDeriv_bound n 0
  obtain ⟨C₁, _, hC₁⟩ := standardGaussianDensity_iteratedFDeriv_bound n 1
  have h0 (y : E) : ‖standardGaussianDensity n y‖ ≤ C₀ := by
    simpa only [norm_iteratedFDeriv_zero] using hC₀ y
  have h1 (y : E) : ‖fderiv ℝ (standardGaussianDensity n) y‖ ≤ C₁ := by
    simpa only [norm_iteratedFDeriv_one] using hC₁ y
  have hd := gaussianSmoothingRegularity_hasFDerivAt_translation_integral n ν (r * a)
    (standardGaussianDensity n) (standardGaussianDensity_smooth n) C₀ C₁ h0 h1 (r • x)
  have hlin : HasFDerivAt (fun z : E => r • z) (r • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul r
  have hcomp := (hd.comp x hlin).const_mul (r ^ n)
  have heq : gaussianSmoothingDensity n ν a b = fun z : E =>
      r ^ n * (∫ u, standardGaussianDensity n (r • z - (r * a) • u) ∂ν) := by
    funext z
    simp only [gaussianSmoothingDensity, r, inv_pow, smul_sub, smul_smul]
  have hdf := hcomp.fderiv
  change fderiv ℝ (fun z : E => r ^ n *
    (∫ u, standardGaussianDensity n (r • z - (r * a) • u) ∂ν)) x = _ at hdf
  rw [heq, hdf]
  ext v
  change r ^ n * ((∫ u, fderiv ℝ (standardGaussianDensity n) (r • x - (r * a) • u) ∂ν) (r • v)) =
    r ^ (n + 1) * ((∫ u, fderiv ℝ (standardGaussianDensity n) (r • (x - a • u)) ∂ν) v)
  simp only [map_smul, smul_eq_mul, pow_succ, smul_sub, smul_smul]
  ring

/-- The genuine kernel-chain-rule derivative of the actual Frechet density derivative. -/
def ouDensityGradientTimeDerivative (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-2 * t))
  let r := b⁻¹
  let dr := -(Real.exp (-2 * t) / b) / b ^ 2
  (((n + 1 : ℕ) : ℝ) * r ^ n * dr) • (∫ u, fderiv ℝ (standardGaussianDensity n) (r • (x - a • u)) ∂ν) +
    r ^ (n + 1) • (∫ u, fderiv ℝ (fderiv ℝ (standardGaussianDensity n)) (r • (x - a • u))
      (r • (a • u) + dr • (x - a • u)) ∂ν)

theorem ou_density_fderiv_hasDerivAt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (gaussianSmoothingDensity n ν (Real.exp (-s))
      (Real.sqrt (1 - Real.exp (-2 * s)))) x) (ouDensityGradientTimeDerivative n ν t x) t := by
  let E := EuclideanSpace ℝ (Fin n)
  let k := standardGaussianDensity n
  have hk : ContDiff ℝ ∞ (fderiv ℝ k) := (standardGaussianDensity_smooth n).fderiv_right (by simp)
  obtain ⟨C₁, _, hC₁⟩ := standardGaussianDensity_iteratedFDeriv_bound n 1
  obtain ⟨C₂, _, hC₂⟩ := standardGaussianDensity_iteratedFDeriv_bound n 2
  have h1 (y : E) : ‖fderiv ℝ k y‖ ≤ C₁ := by
    simpa only [norm_iteratedFDeriv_one] using hC₁ y
  have h2 (y : E) : ‖fderiv ℝ (fderiv ℝ k) y‖ ≤ C₂ := by
    have h := hC₂ y
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h
    exact h
  have hI := (ouDensityPDE_smooth_kernel_integral_hasDerivAt n ν hU
    (fderiv ℝ k) hk C₁ C₂ h1 h2 x t ht).2
  have h := ((ou_inverse_scale_hasDerivAt t ht).pow (n + 1)).smul hI
  have heq : (fun s : ℝ => fderiv ℝ (gaussianSmoothingDensity n ν (Real.exp (-s))
      (Real.sqrt (1 - Real.exp (-2 * s)))) x) =
      fun s : ℝ => ((Real.sqrt (1 - Real.exp (-2 * s)))⁻¹) ^ (n + 1) •
        (∫ u, fderiv ℝ k ((Real.sqrt (1 - Real.exp (-2 * s)))⁻¹ • (x - Real.exp (-s) • u)) ∂ν) :=
    funext fun s => gaussianSmoothingDensity_fderiv_eq_integral n ν _ _ x
  rw [heq]
  convert! h using 1
  simp only [ouDensityGradientTimeDerivative, Nat.add_sub_cancel, Pi.pow_apply, k, add_comm]

end AffineFKProof
