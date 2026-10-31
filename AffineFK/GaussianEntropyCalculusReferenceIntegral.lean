module

public import AffineFK.GaussianEntropyCalculusSpatialLimits
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Genuine Gaussian-reference entropy integrals and spatial limits

The relative density is the actual positive smooth representative of the
RN derivative of a probability law. Its L1 integrability follows from the
actual RN theorem. A scalar bounded derivative gives linear growth, and
therefore integrability of every scalar entropy truncation, without
assuming finite KL or an entropy formula.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Filter Set
open scoped Distributions RealInnerProductSpace Topology

theorem entropy_function_linear_growth (ψ g : ℝ → ℝ)
    (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (g r) r) (hψ1 : ψ 1 = 0)
    (B : ℝ) (hB : 0 ≤ B) (hgb : ∀ r : ℝ, 0 < r → ‖g r‖ ≤ B)
    (r : ℝ) (hr : 0 < r) : ‖ψ r‖ ≤ B * (r + 1) := by
  have h := (convex_Ioi (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q hq => (hψ q hq).hasDerivWithinAt) (fun q hq => hgb q hq)
    (by norm_num : (1 : ℝ) ∈ Ioi 0) hr
  rw [hψ1, sub_zero] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hB)
  rw [Real.norm_eq_abs]
  exact (abs_sub _ _).trans (by rw [abs_of_pos hr, abs_one])

theorem gaussian_relative_smoothing_density_integrable (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    Integrable (gaussianSmoothingRelativeDensity n ν a b)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let μ := (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
    (fun p => a • p.1 + b • p.2)
  have hq := gaussianSmoothingRelativeDensity_properties n ν a b hb
  apply (Measure.integrable_toReal_rnDeriv (μ := μ)
    (ν := stdGaussian (EuclideanSpace ℝ (Fin n)))).congr
  filter_upwards [hq.2.2.2] with x hx
  rw [hx, ENNReal.toReal_ofReal (hq.2.1 x).le]

theorem gaussian_reference_integral_density (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∫ x : EuclideanSpace ℝ (Fin n), standardGaussianDensity n x * f x := by
  rw [stdGaussian_eq_densityMeasure n]
  exact density_integral_eq n _ (standardGaussianDensity_smooth n).continuous
    (fun x => (standardGaussianDensity_pos n x).le) f

theorem gaussian_relative_entropy_function_integrable (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) (ψ g : ℝ → ℝ)
    (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (g r) r) (hψ1 : ψ 1 = 0)
    (B : ℝ) (hB : 0 ≤ B) (hgb : ∀ r : ℝ, 0 < r → ‖g r‖ ≤ B) :
    Integrable (fun x => ψ (gaussianSmoothingRelativeDensity n ν a b x))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hq := gaussianSmoothingRelativeDensity_properties n ν a b hb
  have hc : Continuous (fun x => ψ (gaussianSmoothingRelativeDensity n ν a b x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hψ _ (hq.2.1 x)).continuousAt.comp hq.1.continuous.continuousAt
  have hi := ((gaussian_relative_smoothing_density_integrable n ν a b hb).add
    (integrable_const (1 : ℝ))).const_mul B
  apply hi.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x =>
    entropy_function_linear_growth ψ g hψ hψ1 B hB hgb _ (hq.2.1 x)

theorem gaussian_relative_entropy_spatial_cutoff_tendsto (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) (ψ g : ℝ → ℝ)
    (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (g r) r) (hψ1 : ψ 1 = 0)
    (B : ℝ) (hB : 0 ≤ B) (hgb : ∀ r : ℝ, 0 < r → ‖g r‖ ≤ B)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    Tendsto (fun k : ℕ => ∫ x : EuclideanSpace ℝ (Fin n), cutoffSequence χ k x *
      (standardGaussianDensity n x * ψ (gaussianSmoothingRelativeDensity n ν a b x))) atTop
      (𝓝 (∫ x, ψ (gaussianSmoothingRelativeDensity n ν a b x)
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let q := gaussianSmoothingRelativeDensity n ν a b
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hi : Integrable (fun x => ψ (q x)) γ :=
    gaussian_relative_entropy_function_integrable n ν a b hb ψ g hψ hψ1 B hB hgb
  have hmeas (k : ℕ) : AEStronglyMeasurable (fun x => cutoffSequence χ k x * ψ (q x)) γ :=
    (cutoffSequence χ k).continuous.aestronglyMeasurable.mul hi.aestronglyMeasurable
  have hbnd (k : ℕ) : ∀ᵐ x ∂γ, ‖cutoffSequence χ k x * ψ (q x)‖ ≤ ‖ψ (q x)‖ := by
    exact Filter.Eventually.of_forall fun x => by
      have hc := hχ (((k : ℝ) + 1)⁻¹ • x)
      have hc' : 0 ≤ cutoffSequence χ k x ∧ cutoffSequence χ k x ≤ 1 := hc
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc'.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hc'.2
  have hpt : ∀ᵐ x ∂γ, Tendsto (fun k : ℕ => cutoffSequence χ k x * ψ (q x)) atTop (𝓝 (ψ (q x))) := by
    exact Filter.Eventually.of_forall fun x => by
      have hx : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x) atTop
          (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
        simpa only [zero_smul] using tendsto_inverse_succ.smul_const x
      have hc : Tendsto (fun k : ℕ => cutoffSequence χ k x) atTop (𝓝 (1 : ℝ)) := by
        simpa only [Function.comp_def, cutoffSequence_apply, hχ0] using (χ.continuous.tendsto 0).comp hx
      simpa only [one_mul] using hc.mul_const (ψ (q x))
  have h := tendsto_integral_of_dominated_convergence (fun x => ‖ψ (q x)‖) hmeas hi.norm hbnd hpt
  have heq (k : ℕ) : (∫ x, cutoffSequence χ k x * ψ (q x) ∂γ) =
      ∫ x : EuclideanSpace ℝ (Fin n), cutoffSequence χ k x * (standardGaussianDensity n x * ψ (q x)) := by
    rw [gaussian_reference_integral_density n]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  simpa only [heq] using h

end AffineFKProof
