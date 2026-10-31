module

public import AffineFK.EuclideanLogConcavity
public import AffineFK.GaussianSmoothingDensity

/-!
# Log-concavity of the actual positive Gaussian smoothing density

Prékopa's proved marginal inequality applies to the actual joint density.
The change from integration against the original law to Lebesgue volume
uses the genuine withDensity identity. No pointwise or almost-everywhere
log-concavity assertion about the output is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem gaussianSmoothingDensity_logConcave (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (ρ x)))
    (a b : ℝ) (hb : 0 < b) :
    LogConcaveDensity (fun x =>
      ENNReal.ofReal (gaussianSmoothingDensity n (densityMeasure n ρ) a b x)) := by
  let A : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    b⁻¹ • (LinearMap.fst ℝ _ _ - a • LinearMap.snd ℝ _ _)
  let F : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (p.1 - a • p.2))) *
      ENNReal.ofReal (ρ p.2)
  have hA : LogConcaveDensity (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (p.1 - a • p.2)))) :=
    logConcaveDensity_comp_linearMap _ (logConcaveDensity_standardGaussian n) A
  have hB : LogConcaveDensity (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (ρ p.2)) :=
    logConcaveDensity_comp_linearMap _ hlc (LinearMap.snd ℝ _ _)
  have hFm : ∀ x, Measurable (fun y => F (x, y)) := fun x =>
    (((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).measurable.ennreal_ofReal).mul
      hρ.ennreal_ofReal
  have hm : LogConcaveDensity (fun x => ∫⁻ y, F (x, y)) :=
    logConcaveDensity_marginal_euclidean n F hFm (logConcaveDensity_mul _ _ hA hB)
  have hprod := logConcaveDensity_mul
    (fun _ : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal ((b ^ n)⁻¹)) _
    (logConcaveDensity_const _) hm
  have heq (x : EuclideanSpace ℝ (Fin n)) :
      ENNReal.ofReal (gaussianSmoothingDensity n (densityMeasure n ρ) a b x) =
        ENNReal.ofReal ((b ^ n)⁻¹) * ∫⁻ y, F (x, y) := by
    rw [gaussianSmoothingDensity, ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hb.le _)),
      ofReal_integral_eq_lintegral_ofReal
        (gaussianSmoothingDensity_integrand_integrable n (densityMeasure n ρ) a b x)
        (Filter.Eventually.of_forall fun y => (standardGaussianDensity_pos n _).le)]
    congr 1
    have hk : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • y)))) :=
      ((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).measurable.ennreal_ofReal
    rw [densityMeasure, lintegral_withDensity_eq_lintegral_mul _ hρ.ennreal_ofReal hk]
    apply lintegral_congr
    intro y
    change ENNReal.ofReal (ρ y) *
        ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • y))) =
      ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • y))) * ENNReal.ofReal (ρ y)
    exact mul_comm _ _
  simpa only [← heq] using hprod

end AffineFKProof
