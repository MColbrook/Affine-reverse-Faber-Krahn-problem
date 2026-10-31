module

public import AffineFK.OUDensityPDEMixedKernel
public import AffineFK.OUDensityPDE
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Actual mixed spatial/time derivatives of the OU density

The spatial derivative of the genuine time-kernel formula is compared
with the previously derived ordinary time derivative of the spatial
Gaussian derivative. All integrals are proved integrable; only the
Gaussian's spatial Schwarz symmetry is used. Time/space commutation is
a conclusion. The actual classical density PDE then identifies the
mixed derivative with the derivative of its spatial operator.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ContDiff

theorem ou_density_time_derivative_hasFDerivAt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (ouDensityTimeDerivative n ν t) (ouDensityGradientTimeDerivative n ν t x) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let k := standardGaussianDensity n
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-2 * t))
  let r := b⁻¹
  let d := -(Real.exp (-2 * t) / b) / b ^ 2
  let z : E → E := fun u => r • (x - a • u)
  let v : E → E := fun u => r • (a • u) + d • (x - a • u)
  obtain ⟨K₀, _, hK₀⟩ := standardGaussianDensity_iteratedFDeriv_bound n 0
  obtain ⟨K₁, _, hK₁⟩ := standardGaussianDensity_iteratedFDeriv_bound n 1
  obtain ⟨K₂, _, hK₂⟩ := standardGaussianDensity_iteratedFDeriv_bound n 2
  have h0 (y : E) : ‖k y‖ ≤ K₀ := by simpa only [norm_iteratedFDeriv_zero] using hK₀ y
  have h1 (y : E) : ‖fderiv ℝ k y‖ ≤ K₁ := by simpa only [norm_iteratedFDeriv_one] using hK₁ y
  have h2 (y : E) : ‖fderiv ℝ (fderiv ℝ k) y‖ ≤ K₂ := by
    have h := hK₂ y
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h
    exact h
  have hk : ContDiff ℝ ∞ (fderiv ℝ k) := (standardGaussianDensity_smooth n).fderiv_right (by simp)
  have hA : Integrable (fun u => fderiv ℝ k (z u)) ν := by
    apply (integrable_const K₁).mono' ((hk.continuous.comp (by fun_prop)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun u => h1 _
  have hB : Integrable (fun u => fderiv ℝ (fderiv ℝ k) (z u) (v u)) ν := by
    exact (ouDensityPDE_smooth_kernel_integral_hasDerivAt n ν hU (fderiv ℝ k) hk
      K₁ K₂ h1 h2 x t ht).1
  let A := ∫ u, fderiv ℝ k (z u) ∂ν
  let B := ∫ u, fderiv ℝ (fderiv ℝ k) (z u) (v u) ∂ν
  have hI₁ := ouDensityPDE_time_kernel_integral_hasFDerivAt n ν hU a r d x
  have hpoint (u : E) : fderiv ℝ (fun y => ouDensityPDETimeKernel n a r d y u) x =
      r • fderiv ℝ (fderiv ℝ k) (z u) (v u) + d • fderiv ℝ k (z u) := by
    have hsym := (standardGaussianDensity_smooth n).contDiffAt.isSymmSndFDerivAt (x := z u) (by simp)
    have hflip : (fderiv ℝ (fderiv ℝ k) (z u)).flip (v u) =
        fderiv ℝ (fderiv ℝ k) (z u) (v u) := by
      ext w
      exact hsym.eq w (v u)
    rw [(ouDensityPDETimeKernel_hasFDerivAt n a r d x u).fderiv, hflip]
  have hInt : (∫ u, fderiv ℝ (fun y => ouDensityPDETimeKernel n a r d y u) x ∂ν) =
      r • B + d • A := by
    calc
      _ = ∫ u, r • fderiv ℝ (fderiv ℝ k) (z u) (v u) + d • fderiv ℝ k (z u) ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = _ := by rw [integral_add (hB.fun_smul r) (hA.fun_smul d), integral_smul, integral_smul]
  have hlin : HasFDerivAt (fun y : E => r • y) (r • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul r
  have hTr := gaussianSmoothingRegularity_hasFDerivAt_translation_integral n ν (r * a)
    k (standardGaussianDensity_smooth n) K₀ K₁ h0 h1 (r • x)
  have hI₀ : HasFDerivAt (fun y : E => ∫ u, k (r • (y - a • u)) ∂ν)
      (A.comp (r • ContinuousLinearMap.id ℝ E)) x := by
    convert! hTr.comp x hlin using 1 <;>
      simp only [A, z, Function.comp_def, smul_sub, smul_smul] <;> rfl
  have hD := (hI₀.const_mul ((n : ℝ) * r ^ (n - 1) * d)).add (hI₁.2.const_mul (r ^ n))
  have hExpected : ouDensityGradientTimeDerivative n ν t x =
      ((n : ℝ) * r ^ (n - 1) * d) • A.comp (r • ContinuousLinearMap.id ℝ E) +
        r ^ n • (∫ u, fderiv ℝ (fun y => ouDensityPDETimeKernel n a r d y u) x ∂ν) := by
    rw [hInt]
    ext w
    change (((n + 1 : ℕ) : ℝ) * r ^ n * d) * A w + r ^ (n + 1) * B w =
      ((n : ℝ) * r ^ (n - 1) * d) * A (r • w) + r ^ n * (r * B w + d * A w)
    rw [map_smul]
    simp only [smul_eq_mul]
    cases n with
    | zero => simp; ring
    | succ m => simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]; ring
  convert! hD.congr_fderiv hExpected.symm using 1

theorem ou_density_gradient_time_derivative_eq_spatial_derivative (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    ouDensityGradientTimeDerivative n ν t x =
      fderiv ℝ (ouDensitySpatialOperator n (gaussianSmoothingDensity n ν (Real.exp (-t))
        (Real.sqrt (1 - Real.exp (-2 * t))))) x := by
  have hfun : ouDensityTimeDerivative n ν t =
      ouDensitySpatialOperator n (gaussianSmoothingDensity n ν (Real.exp (-t))
        (Real.sqrt (1 - Real.exp (-2 * t)))) :=
    funext (ou_density_time_derivative_eq_spatial_operator n ν hU t ht)
  rw [← hfun, (ou_density_time_derivative_hasFDerivAt n ν hU t ht x).fderiv]

theorem ou_density_fderiv_hasDerivAt_spatial_operator (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (gaussianSmoothingDensity n ν (Real.exp (-s))
      (Real.sqrt (1 - Real.exp (-2 * s)))) x)
      (fderiv ℝ (ouDensitySpatialOperator n (gaussianSmoothingDensity n ν (Real.exp (-t))
        (Real.sqrt (1 - Real.exp (-2 * t))))) x) t := by
  rw [← ou_density_gradient_time_derivative_eq_spatial_derivative n ν hU t ht x]
  exact ou_density_fderiv_hasDerivAt n ν hU t ht x

end AffineFKProof
