module

public import AffineFK.EuclideanLogConcavity
public import AffineFK.GaussianReferenceScore
public import AffineFK.BridgeAffineDensityMap
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# The actual normalized Gaussian kernel for killed finite-grid iteration

The explicit kernel has covariance b^2 Id. Its mass is obtained from the
actual Gaussian law and the genuine Haar Jacobian. Its pointwise
log-concavity and evenness are proved from the standard Gaussian density.
No killed-kernel or spectral identification is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

def dirichletGaussianKernel (n : ℕ) (b : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal ((b ^ n)⁻¹) * ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • x))

theorem dirichletGaussianKernel_measurable (n : ℕ) (b : ℝ) :
    Measurable (dirichletGaussianKernel n b) :=
  measurable_const.mul (((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).measurable.ennreal_ofReal)

theorem dirichletGaussianKernel_pos (n : ℕ) (b : ℝ) (hb : 0 < b)
    (x : EuclideanSpace ℝ (Fin n)) : 0 < dirichletGaussianKernel n b x := by
  apply bot_lt_iff_ne_bot.mpr
  exact mul_ne_zero (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hb _))).ne'
    (ENNReal.ofReal_pos.mpr (standardGaussianDensity_pos n _)).ne'

theorem dirichletGaussianKernel_logConcave (n : ℕ) (b : ℝ) :
    LogConcaveDensity (dirichletGaussianKernel n b) := by
  have hk := logConcaveDensity_comp_linearMap _ (logConcaveDensity_standardGaussian n)
    (b⁻¹ • LinearMap.id : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  exact logConcaveDensity_mul _ _ (logConcaveDensity_const _) hk

theorem dirichletGaussianKernel_neg (n : ℕ) (b : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : dirichletGaussianKernel n b (-x) = dirichletGaussianKernel n b x := by
  unfold dirichletGaussianKernel
  rw [smul_neg]
  congr 2
  apply Real.log_injOn_pos (standardGaussianDensity_pos n _) (standardGaussianDensity_pos n _)
  rw [log_standardGaussianDensity, log_standardGaussianDensity, norm_neg]

theorem dirichletGaussianKernel_lintegral (n : ℕ) (b : ℝ) (hb : 0 < b) :
    (∫⁻ x, dirichletGaussianKernel n b x) = 1 := by
  have hg := bridge_affine_density_map n b hb 0
    (fun x => ENNReal.ofReal (standardGaussianDensity n x))
    (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal
  have hlaw : volume.withDensity (dirichletGaussianKernel n b) =
      (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun x => b • x) := by
    rw [stdGaussian_eq_densityMeasure]
    simpa only [densityMeasure, zero_add, sub_zero, dirichletGaussianKernel] using! hg.symm
  calc
    _ = (volume.withDensity (dirichletGaussianKernel n b)) Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = _ := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ Set.univ) hlaw
    _ = 1 := by rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, measure_univ]

theorem dirichletGaussianKernel_translate_lintegral (n : ℕ) (b : ℝ) (hb : 0 < b)
    (x : EuclideanSpace ℝ (Fin n)) : (∫⁻ y, dirichletGaussianKernel n b (x - y)) = 1 := by
  rw [lintegral_sub_left_eq_self, dirichletGaussianKernel_lintegral n b hb]

end AffineFKProof
