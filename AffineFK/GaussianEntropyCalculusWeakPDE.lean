module

public import AffineFK.GaussianEntropyCalculusCompact
public import AffineFK.OUDensityTimeWeakDensity
public import AffineFK.GaussianSmoothingRegularity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Identifying the actual OU density derivative against compact tests

The genuine pointwise kernel derivative and the independent weak generator
equation are compared using uniqueness of an actual ordinary derivative.
No distributional time derivative is identified merely from notation.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped Distributions Topology

theorem ou_density_test_integral_eq (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (s : ℝ) (hs : 0 < s) :
    (∫ x, φ x ∂densityMeasure n (gaussianSmoothingDensity n ν (Real.exp (-s))
      (Real.sqrt (1 - Real.exp (-2 * s))))) =
    ∫ x : EuclideanSpace ℝ (Fin n), φ x * gaussianSmoothingDensity n ν (Real.exp (-s))
      (Real.sqrt (1 - Real.exp (-2 * s))) x := by
  let ρ := gaussianSmoothingDensity n ν (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s)))
  have hρ : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
    (gaussianSmoothingDensity_continuous n ν _ _).measurable.ennreal_ofReal
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul hρ
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (ENNReal.ofReal (ρ x)).toReal * φ x = φ x * ρ x
    rw [ENNReal.toReal_ofReal (gaussianSmoothingDensity_pos n ν _ _
      (ou_smoothing_scale_domain s hs).2.1 x).le, mul_comm]

theorem ou_density_test_spatial_integral_hasDerivAt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x => φ x * ouDensityTimeDerivative n ν t x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    HasDerivAt (fun s : ℝ => ∫ x : EuclideanSpace ℝ (Fin n), φ x *
      gaussianSmoothingDensity n ν (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s))) x)
      (∫ x : EuclideanSpace ℝ (Fin n), φ x * ouDensityTimeDerivative n ν t x) t := by
  have h := ou_compact_entropy_chain_rule n ν hU (fun q : ℝ => q) (fun _ => (1 : ℝ))
    (fun q _ => hasDerivAt_id q) measurable_const 1 (by norm_num) (by intros; norm_num) φ t ht
  have heq (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
      standardGaussianDensity n x *
        (gaussianSmoothingDensity n ν (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s))) x /
          standardGaussianDensity n x) =
      gaussianSmoothingDensity n ν (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s))) x :=
    mul_div_cancel₀ _ (standardGaussianDensity_pos n x).ne'
  simpa only [mul_one, heq] using h

theorem ou_density_time_derivative_weak_pde (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (t : ℝ) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin n), φ x * ouDensityTimeDerivative n ν t x) =
    ∫ x : EuclideanSpace ℝ (Fin n), ouTestGenerator n φ x *
      gaussianSmoothingDensity n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) x := by
  have h := ou_density_test_expectation_weak_equation n ν hU φ t ht
  rw [ou_density_test_integral_eq n ν (ouTestGenerator n φ) t ht] at h
  have h' : HasDerivAt (fun s : ℝ => ∫ x : EuclideanSpace ℝ (Fin n), φ x *
      gaussianSmoothingDensity n ν (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s))) x)
      (∫ x : EuclideanSpace ℝ (Fin n), ouTestGenerator n φ x *
        gaussianSmoothingDensity n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) x) t := by
    apply h.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds ht] with s hs
    exact (ou_density_test_integral_eq n ν φ s hs).symm
  exact (ou_density_test_spatial_integral_hasDerivAt n ν hU φ t ht).2.unique h'

end AffineFKProof
