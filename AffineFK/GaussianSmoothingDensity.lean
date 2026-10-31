module

public import AffineFK.StandardGaussianDensity
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# The explicit density of a Gaussian-smoothed probability measure

The density is the integral of the actual translated/scaled Gaussian
kernel against the original measure. The bounds, positivity and eventual
measure identification use Mathlib's real Gaussian, dominated integral,
Haar change of variables and Tonelli results, with their Apache-2.0
contributor attribution retained in the imported primary modules.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal

def gaussianSmoothingDensity (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (a b : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (b ^ n)⁻¹ * ∫ u, standardGaussianDensity n (b⁻¹ • (x - a • u)) ∂ν

theorem gaussianSmoothingDensity_standard_pdf_le (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 0 := by
  have hexp : Real.exp (-(x ^ 2) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num))
  simpa [gaussianPDFReal] using
    mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi)))

theorem gaussianSmoothingDensity_standard_le (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    standardGaussianDensity n x ≤ standardGaussianDensity n 0 := by
  apply Finset.prod_le_prod₀
  · intro i _
    exact gaussianPDFReal_nonneg 0 1 (x i)
  · intro i _
    exact gaussianSmoothingDensity_standard_pdf_le (x i)

theorem gaussianSmoothingDensity_integrand_integrable (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν]
    (a b : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun u => standardGaussianDensity n (b⁻¹ • (x - a • u))) ν := by
  have hc : Continuous (fun u : EuclideanSpace ℝ (Fin n) =>
      standardGaussianDensity n (b⁻¹ • (x - a • u))) :=
    (standardGaussianDensity_smooth n).continuous.comp (by fun_prop)
  apply (integrable_const (standardGaussianDensity n 0)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_pos (standardGaussianDensity_pos n _)]
    exact gaussianSmoothingDensity_standard_le n _

theorem gaussianSmoothingDensity_pos (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) (x : EuclideanSpace ℝ (Fin n)) :
    0 < gaussianSmoothingDensity n ν a b x := by
  apply mul_pos (inv_pos.mpr (pow_pos hb n))
  apply (integral_pos_iff_support_of_nonneg
    (fun u => (standardGaussianDensity_pos n (b⁻¹ • (x - a • u))).le)
    (gaussianSmoothingDensity_integrand_integrable n ν a b x)).mpr
  have hs : Function.support (fun u : EuclideanSpace ℝ (Fin n) =>
      standardGaussianDensity n (b⁻¹ • (x - a • u))) = Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (standardGaussianDensity_pos n _).ne'
  rw [hs, measure_univ]
  exact zero_lt_one

theorem gaussianSmoothingDensity_continuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν]
    (a b : ℝ) : Continuous (gaussianSmoothingDensity n ν a b) := by
  apply Continuous.const_mul
  apply continuous_of_dominated
    (bound := fun _ : EuclideanSpace ℝ (Fin n) => standardGaussianDensity n 0)
  · intro x
    exact (gaussianSmoothingDensity_integrand_integrable n ν a b x).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (standardGaussianDensity_pos n _)]
      exact gaussianSmoothingDensity_standard_le n _
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun u =>
      (standardGaussianDensity_smooth n).continuous.comp (by fun_prop)

theorem gaussianSmoothingDensity_affine_lintegral (n : ℕ) (a b : ℝ) (hb : 0 < b)
    (u : EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, f (a • u + b • g) ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ENNReal.ofReal ((b ^ n)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • u))) * f x := by
  let K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • u))) * f x
  have hk : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (standardGaussianDensity n x)) :=
    (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal
  have hK : Measurable K :=
    ((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).measurable.ennreal_ofReal.mul hf
  rw [stdGaussian_eq_densityMeasure n, densityMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hk
      (g := fun g => f (a • u + b • g)) (hf.comp (by fun_prop))]
  calc
    _ = ∫⁻ g, K (a • u + b • g) := by
      apply lintegral_congr
      intro g
      simp only [Pi.mul_apply, K, add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ hb.ne', one_smul]
    _ = ∫⁻ y, K (a • u + y) ∂(volume.map (fun g : EuclideanSpace ℝ (Fin n) => b • g)) :=
      (lintegral_map (hK.comp (by fun_prop)) (by fun_prop)).symm
    _ = _ := by
      rw [Measure.map_addHaar_smul volume hb.ne', lintegral_smul_measure,
        lintegral_add_left_eq_self]
      simp only [finrank_euclideanSpace_fin,
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hb.le n))]
      rfl

theorem gaussianSmoothingDensity_law (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2) =
      densityMeasure n (gaussianSmoothingDensity n ν a b) := by
  apply Measure.ext_of_lintegral
  intro f hf
  let K : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (p.2 - a • p.1))) * f p.2
  have hK : Measurable K :=
    ((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).measurable.ennreal_ofReal.mul
      (hf.comp measurable_snd)
  have hρ : Measurable (fun x => ENNReal.ofReal (gaussianSmoothingDensity n ν a b x)) :=
    (gaussianSmoothingDensity_continuous n ν a b).measurable.ennreal_ofReal
  rw [lintegral_map hf (by fun_prop),
    lintegral_prod (fun p => f (a • p.1 + b • p.2)) (hf.comp (by fun_prop)).aemeasurable]
  simp_rw [gaussianSmoothingDensity_affine_lintegral n a b hb _ f hf]
  calc
    _ = ENNReal.ofReal ((b ^ n)⁻¹) * ∫⁻ u, ∫⁻ x, K (u, x) ∂volume ∂ν := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal ((b ^ n)⁻¹) * ∫⁻ x, ∫⁻ u, K (u, x) ∂ν ∂volume := by
      rw [lintegral_lintegral_swap hK.aemeasurable]
    _ = ∫⁻ x, ENNReal.ofReal (gaussianSmoothingDensity n ν a b x) * f x := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      have hk : Measurable (fun u =>
          ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • u)))) :=
        ((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).measurable.ennreal_ofReal
      dsimp only [K]
      rw [lintegral_mul_const _ hk, gaussianSmoothingDensity, ENNReal.ofReal_mul,
        ofReal_integral_eq_lintegral_ofReal
          (gaussianSmoothingDensity_integrand_integrable n ν a b x)
          (Filter.Eventually.of_forall fun u => (standardGaussianDensity_pos n _).le), mul_assoc]
      exact inv_nonneg.mpr (pow_nonneg hb.le n)
    _ = ∫⁻ x, f x ∂densityMeasure n (gaussianSmoothingDensity n ν a b) :=
      (lintegral_withDensity_eq_lintegral_mul _ hρ hf).symm

end AffineFKProof
