module

public import AffineFK.GaussianSmoothingLogConcavity
public import AffineFK.GaussianReferenceScore

/-!
# Preservation of unit strong log-concavity by Gaussian smoothing

Completing the actual Gaussian square reverses the kernel without any
assumption on the output. Prékopa's actual Euclidean marginal theorem
then preserves log-concavity of rho times exp(norm squared/2), including
densities which vanish outside their support. No smooth input, moment,
Hessian bound or Poincare conclusion is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

theorem strongLogConcave_gaussian_kernel_balance (n : ℕ)
    (a b : ℝ) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1)
    (x u : EuclideanSpace ℝ (Fin n)) :
    standardGaussianDensity n (b⁻¹ • (x - a • u)) * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2) =
      Real.exp ((1 / 2 : ℝ) * ‖u‖ ^ 2) * standardGaussianDensity n (b⁻¹ • (u - a • x)) := by
  have hx : ‖x - a • u‖ ^ 2 = ‖x‖ ^ 2 + a ^ 2 * ‖u‖ ^ 2 - 2 * a * ⟪x, u⟫ := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hu : ‖u - a • x‖ ^ 2 = ‖u‖ ^ 2 + a ^ 2 * ‖x‖ ^ 2 - 2 * a * ⟪x, u⟫ := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, real_inner_comm u x]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hnorm : ‖b⁻¹ • (x - a • u)‖ ^ 2 - ‖x‖ ^ 2 =
      ‖b⁻¹ • (u - a • x)‖ ^ 2 - ‖u‖ ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hx, hu]
    have hbinv : b⁻¹ ^ 2 * b ^ 2 = 1 := by field_simp [hb.ne']
    linear_combination (‖u‖ ^ 2 - ‖x‖ ^ 2) * b⁻¹ ^ 2 * hab +
      (‖x‖ ^ 2 - ‖u‖ ^ 2) * hbinv
  apply Real.log_injOn_pos
    (mul_pos (standardGaussianDensity_pos n _) (Real.exp_pos _))
    (mul_pos (Real.exp_pos _) (standardGaussianDensity_pos n _))
  rw [Real.log_mul (standardGaussianDensity_pos n _).ne' (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' (standardGaussianDensity_pos n _).ne',
    Real.log_exp, Real.log_exp, log_standardGaussianDensity, log_standardGaussianDensity]
  linarith

theorem strongLogConcave_gaussianSmoothingDensity_lintegral (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    [IsProbabilityMeasure (densityMeasure n ρ)] (a b : ℝ) (hb : 0 < b)
    (x : EuclideanSpace ℝ (Fin n)) :
    ENNReal.ofReal (gaussianSmoothingDensity n (densityMeasure n ρ) a b x) =
      ENNReal.ofReal ((b ^ n)⁻¹) * ∫⁻ u,
        ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • u))) * ENNReal.ofReal (ρ u) := by
  rw [gaussianSmoothingDensity, ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hb.le _)),
    ofReal_integral_eq_lintegral_ofReal
      (gaussianSmoothingDensity_integrand_integrable n (densityMeasure n ρ) a b x)
      (Filter.Eventually.of_forall fun u => (standardGaussianDensity_pos n _).le)]
  congr 1
  have hk : Measurable (fun u : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • u)))) :=
    ((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).measurable.ennreal_ofReal
  rw [densityMeasure, lintegral_withDensity_eq_lintegral_mul _ hρ.ennreal_ofReal hk]
  apply lintegral_congr
  intro u
  change ENNReal.ofReal (ρ u) *
      ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • u))) =
    ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • u))) * ENNReal.ofReal (ρ u)
  exact mul_comm _ _

theorem strongLogConcave_gaussianSmoothingDensity (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal
      (ρ x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2))))
    (a b : ℝ) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1) :
    LogConcaveDensity (fun x => ENNReal.ofReal
      (gaussianSmoothingDensity n (densityMeasure n ρ) a b x *
        Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let A : (E × E) →ₗ[ℝ] E := b⁻¹ • (LinearMap.snd ℝ _ _ - a • LinearMap.fst ℝ _ _)
  let F : E × E → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (p.2 - a • p.1))) *
      ENNReal.ofReal (ρ p.2 * Real.exp ((1 / 2 : ℝ) * ‖p.2‖ ^ 2))
  have hA : LogConcaveDensity (fun p : E × E =>
      ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (p.2 - a • p.1)))) :=
    logConcaveDensity_comp_linearMap _ (logConcaveDensity_standardGaussian n) A
  have hB : LogConcaveDensity (fun p : E × E =>
      ENNReal.ofReal (ρ p.2 * Real.exp ((1 / 2 : ℝ) * ‖p.2‖ ^ 2))) :=
    logConcaveDensity_comp_linearMap _ hlc (LinearMap.snd ℝ _ _)
  have hFm : Measurable F := by
    exact (((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).measurable.ennreal_ofReal).mul
      ((hρ.comp measurable_snd).mul (by fun_prop)).ennreal_ofReal
  have hm := logConcaveDensity_marginal_euclidean n F
    (fun x => hFm.comp (by fun_prop)) (logConcaveDensity_mul _ _ hA hB)
  have hout := logConcaveDensity_mul
    (fun _ : E => ENNReal.ofReal ((b ^ n)⁻¹)) _ (logConcaveDensity_const _) hm
  have heq (x : E) : ENNReal.ofReal
      (gaussianSmoothingDensity n (densityMeasure n ρ) a b x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)) =
      ENNReal.ofReal ((b ^ n)⁻¹) * ∫⁻ u, F (x, u) := by
    rw [ENNReal.ofReal_mul (gaussianSmoothingDensity_pos n (densityMeasure n ρ) a b hb x).le,
      strongLogConcave_gaussianSmoothingDensity_lintegral n ρ hρ a b hb, mul_assoc]
    congr 1
    have hk : Measurable (fun u : E =>
        ENNReal.ofReal (standardGaussianDensity n (b⁻¹ • (x - a • u))) * ENNReal.ofReal (ρ u)) :=
      (((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).measurable.ennreal_ofReal).mul hρ.ennreal_ofReal
    rw [← lintegral_mul_const _ hk]
    apply lintegral_congr
    intro u
    have hreal : (standardGaussianDensity n (b⁻¹ • (x - a • u)) * ρ u) *
        Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2) =
        standardGaussianDensity n (b⁻¹ • (u - a • x)) *
          (ρ u * Real.exp ((1 / 2 : ℝ) * ‖u‖ ^ 2)) := by
      calc
        _ = ρ u * (standardGaussianDensity n (b⁻¹ • (x - a • u)) *
            Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)) := by ring
        _ = _ := by rw [strongLogConcave_gaussian_kernel_balance n a b hb hab x u]; ring
    have h := congrArg ENNReal.ofReal hreal
    simpa only [F, ENNReal.ofReal_mul (standardGaussianDensity_pos n _).le,
      ENNReal.ofReal_mul (hρ0 u),
      ENNReal.ofReal_mul (mul_nonneg (standardGaussianDensity_pos n _).le (hρ0 u))] using h
  have hfun : (fun x : E => ENNReal.ofReal
      (gaussianSmoothingDensity n (densityMeasure n ρ) a b x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2))) =
      (fun x : E => ENNReal.ofReal ((b ^ n)⁻¹) * ∫⁻ u, F (x, u)) := funext heq
  rw [hfun]
  exact hout

end AffineFKProof
