module

public import AffineFK.OUDensityPDECalculus
public import AffineFK.OUDensityPDEContinuity
public import AffineFK.GaussianEntropyCalculusWeakPDE
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The classical positive-time OU equation for the actual density

The genuine kernel time derivative and the genuine spatial Fokker--Planck
operator have the same compact-test integrals. Both are continuous, so
distributional uniqueness first gives almost-everywhere equality and the
positivity of Haar measure on open sets upgrades it to pointwise equality.
The final ordinary time derivative therefore has the actual spatial
operator as its value. Fisher-information differentiation is separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

theorem ou_density_time_derivative_ae_spatial_operator (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) :
    ouDensityTimeDerivative n ν t =ᵐ[volume]
      ouDensitySpatialOperator n (gaussianSmoothingDensity n ν (Real.exp (-t))
        (Real.sqrt (1 - Real.exp (-2 * t)))) := by
  let ρ := gaussianSmoothingDensity n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
  have hρ := gaussianSmoothingDensity_smooth n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
  apply ae_eq_of_integral_contDiff_smul_eq
    (ou_density_time_derivative_continuous n ν hU t).locallyIntegrable
    (ouDensitySpatialOperator_continuous n ρ hρ).locallyIntegrable
  intro ψ hψ hc
  let φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
    ⟨ψ, hψ, hc, Set.subset_univ _⟩
  have h1 := ou_density_time_derivative_weak_pde n ν hU φ t ht
  have h2 := (ouDensitySpatialOperator_test_duality n ρ hρ φ).2.2
  change (∫ x, ψ x * ouDensityTimeDerivative n ν t x) =
    ∫ x, ψ x * ouDensitySpatialOperator n ρ x
  exact h1.trans h2.symm

theorem ou_density_time_derivative_eq_spatial_operator (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    ouDensityTimeDerivative n ν t x =
      ouDensitySpatialOperator n (gaussianSmoothingDensity n ν (Real.exp (-t))
        (Real.sqrt (1 - Real.exp (-2 * t)))) x := by
  have h := Measure.eq_of_ae_eq (ou_density_time_derivative_ae_spatial_operator n ν hU t ht)
    (ou_density_time_derivative_continuous n ν hU t)
    (ouDensitySpatialOperator_continuous n _ (gaussianSmoothingDensity_smooth n ν _ _))
  exact congrFun h x

theorem ou_density_hasDerivAt_spatial_operator (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => gaussianSmoothingDensity n ν (Real.exp (-s))
      (Real.sqrt (1 - Real.exp (-2 * s))) x)
      (ouDensitySpatialOperator n (gaussianSmoothingDensity n ν (Real.exp (-t))
        (Real.sqrt (1 - Real.exp (-2 * t)))) x) t := by
  rw [← ou_density_time_derivative_eq_spatial_operator n ν hU t ht x]
  exact ou_density_time_derivative_hasDerivAt n ν hU x t ht

end AffineFKProof
