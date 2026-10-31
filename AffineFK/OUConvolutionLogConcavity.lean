module

public import AffineFK.GaussianSmoothingLogConcavity
public import AffineFK.OUConvolutionCommutation

/-!
# Log-concavity of the genuine smoothed normalized convolution density

Two applications of the proved Euclidean Prékopa marginal theorem apply
to the actual Gaussian kernel and the two input density representatives.
The pushforward/product/withDensity identities identify the resulting
marginal with the explicit Gaussian smoothing density. No regularity or
log-concavity of an unspecified output representative is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem gaussianSmoothing_normalized_convolution_logConcave (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hlc₁ : LogConcaveDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (hlc₂ : LogConcaveDensity (fun x => ENNReal.ofReal (ρ₂ x)))
    (a b c d : ℝ) (hd : 0 < d) :
    LogConcaveDensity (fun x => ENNReal.ofReal (gaussianSmoothingDensity n
      (((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)).map
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2)) c d x)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ := (densityMeasure n ρ₁).prod (densityMeasure n ρ₂)
  let W : E × E → E := fun p => a • p.1 + b • p.2
  have hW : Measurable W := by dsimp [W]; fun_prop
  let ν := μ.map W
  let : IsProbabilityMeasure ν := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  let Z : ((E × E) × E) →ₗ[ℝ] E := (LinearMap.fst ℝ E E).comp (LinearMap.fst ℝ (E × E) E)
  let X : ((E × E) × E) →ₗ[ℝ] E := (LinearMap.snd ℝ E E).comp (LinearMap.fst ℝ (E × E) E)
  let Y : ((E × E) × E) →ₗ[ℝ] E := LinearMap.snd ℝ (E × E) E
  let A := d⁻¹ • (Z - c • (a • X + b • Y))
  let F : (E × E) × E → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (standardGaussianDensity n (d⁻¹ • (p.1.1 - c • (a • p.1.2 + b • p.2)))) *
      ENNReal.ofReal (ρ₁ p.1.2) * ENNReal.ofReal (ρ₂ p.2)
  have hgauss : LogConcaveDensity (fun p : (E × E) × E =>
      ENNReal.ofReal (standardGaussianDensity n (d⁻¹ • (p.1.1 - c • (a • p.1.2 + b • p.2))))) :=
    logConcaveDensity_comp_linearMap _ (logConcaveDensity_standardGaussian n) A
  have hlcF : LogConcaveDensity F := logConcaveDensity_mul _ _
    (logConcaveDensity_mul _ _ hgauss (logConcaveDensity_comp_linearMap _ hlc₁ X))
    (logConcaveDensity_comp_linearMap _ hlc₂ Y)
  have hF : Measurable F := by
    exact ((((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).measurable.ennreal_ofReal).mul
      (hρ₁.comp (by fun_prop)).ennreal_ofReal).mul (hρ₂.comp measurable_snd).ennreal_ofReal
  have hlcG : LogConcaveDensity (fun p : E × E => ∫⁻ y, F (p, y)) :=
    logConcaveDensity_marginal_euclidean n F (fun p => hF.comp (by fun_prop)) hlcF
  have hG : Measurable (fun p : E × E => ∫⁻ y, F (p, y)) := hF.lintegral_prod_right
  have hm := logConcaveDensity_marginal_euclidean n (fun p : E × E => ∫⁻ y, F (p, y))
    (fun x => hG.comp (by fun_prop)) hlcG
  have hout := logConcaveDensity_mul (fun _ : E => ENNReal.ofReal ((d ^ n)⁻¹)) _
    (logConcaveDensity_const _) hm
  have heq (x : E) : ENNReal.ofReal (gaussianSmoothingDensity n ν c d x) =
      ENNReal.ofReal ((d ^ n)⁻¹) * ∫⁻ u, ∫⁻ v, F ((x, u), v) := by
    rw [gaussianSmoothingDensity, ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hd.le _)),
      ofReal_integral_eq_lintegral_ofReal (gaussianSmoothingDensity_integrand_integrable n ν c d x)
        (Filter.Eventually.of_forall fun y => (standardGaussianDensity_pos n _).le)]
    congr 1
    let K : E → ℝ≥0∞ := fun z => ENNReal.ofReal (standardGaussianDensity n (d⁻¹ • (x - c • z)))
    have hK : Measurable K := ((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).measurable.ennreal_ofReal
    change (∫⁻ z, K z ∂μ.map W) = _
    rw [lintegral_map hK hW]
    change (∫⁻ p : E × E, K (W p) ∂(densityMeasure n ρ₁).prod (densityMeasure n ρ₂)) = _
    rw [lintegral_prod (fun p : E × E => K (W p)) (hK.comp hW).aemeasurable]
    have hinner : Measurable (fun u : E => ∫⁻ v, K (W (u, v)) ∂densityMeasure n ρ₂) :=
      (hK.comp hW).lintegral_prod_right'
    rw [densityMeasure, lintegral_withDensity_eq_lintegral_mul _ hρ₁.ennreal_ofReal hinner]
    apply lintegral_congr
    intro u
    change ENNReal.ofReal (ρ₁ u) * (∫⁻ v, K (W (u, v)) ∂volume.withDensity (fun v => ENNReal.ofReal (ρ₂ v))) = _
    have hKu : Measurable (fun v : E => K (W (u, v))) := hK.comp (by fun_prop)
    rw [lintegral_withDensity_eq_lintegral_mul _ hρ₂.ennreal_ofReal hKu,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro v
    dsimp only [K, W, F]
    simp only [Pi.mul_apply]
    ring
  change LogConcaveDensity (fun x : E => ENNReal.ofReal (gaussianSmoothingDensity n ν c d x))
  have hfun : (fun x : E => ENNReal.ofReal (gaussianSmoothingDensity n ν c d x)) =
      (fun x : E => ENNReal.ofReal ((d ^ n)⁻¹) * ∫⁻ u, ∫⁻ v, F ((x, u), v)) := funext heq
  rw [hfun]
  exact hout

end AffineFKProof
