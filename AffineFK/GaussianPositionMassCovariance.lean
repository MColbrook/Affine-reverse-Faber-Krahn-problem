module

public import AffineFK.GaussianPositionPoincare
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Gaussian mass and the covariance scalar of a restriction

Jensen's inequality and an exact Gaussian dilation integral give the
usual Gaussian entropy/covariance bound directly. Thus a literal
exponential Gaussian-mass lower bound implies the required uniform
covariance lower bound. The Milman intersection theorem supplying that
mass bound is a separate geometric obligation, not a premise disguised
as a conclusion about the position.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

theorem gaussianPosition_standardDensity_integrable (n : ℕ) :
    Integrable (standardGaussianDensity n) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hmass : (∫⁻ x, ENNReal.ofReal (standardGaussianDensity n x) ∂volume) = 1 := by
    have h := measure_univ (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))
    rw [stdGaussian_eq_densityMeasure, densityMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at h
    exact h
  exact (lintegral_ofReal_ne_top_iff_integrable
    (standardGaussianDensity_smooth n).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (standardGaussianDensity_pos n x).le)).mp
      (by rw [hmass]; exact ENNReal.one_ne_top)

theorem gaussianPosition_standardDensity_integral (n : ℕ) :
    (∫ x : EuclideanSpace ℝ (Fin n), standardGaussianDensity n x) = 1 := by
  have h := density_integral_eq n (standardGaussianDensity n)
    (standardGaussianDensity_smooth n).continuous (fun x => (standardGaussianDensity_pos n x).le)
    (fun _ => (1 : ℝ))
  rw [← stdGaussian_eq_densityMeasure, integral_const, probReal_univ, one_smul] at h
  simpa only [mul_one] using h.symm

theorem gaussianPosition_gaussian_tilt_scale (n : ℕ) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    standardGaussianDensity n x * Real.exp (((1 - R⁻¹ ^ 2) / 2) * ‖x‖ ^ 2) =
      standardGaussianDensity n (R⁻¹ • x) := by
  rw [← Real.exp_log (standardGaussianDensity_pos n x), ← Real.exp_add,
    ← Real.exp_log (standardGaussianDensity_pos n (R⁻¹ • x))]
  congr 1
  rw [log_standardGaussianDensity, log_standardGaussianDensity, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem gaussianPosition_gaussian_tilt_integral (n : ℕ) (R : ℝ) (hR : 0 < R) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => standardGaussianDensity n x *
      Real.exp (((1 - R⁻¹ ^ 2) / 2) * ‖x‖ ^ 2)) volume ∧
    (∫ x : EuclideanSpace ℝ (Fin n), standardGaussianDensity n x *
      Real.exp (((1 - R⁻¹ ^ 2) / 2) * ‖x‖ ^ 2)) = R ^ n := by
  have heq := funext (gaussianPosition_gaussian_tilt_scale n R)
  rw [heq]
  refine ⟨(gaussianPosition_standardDensity_integrable n).comp_smul (inv_ne_zero hR.ne'), ?_⟩
  have h := Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (standardGaussianDensity n) hR.le
  simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    gaussianPosition_standardDensity_integral, mul_one] using h

theorem gaussianPosition_cond_continuous_integrable (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) :
    Integrable f (ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) := by
  have h : Integrable f ((stdGaussian (EuclideanSpace ℝ (Fin n))).restrict K) :=
    ContinuousOn.integrableOn_compact hK hf.continuousOn
  simpa only [ProbabilityTheory.cond] using h.smul_measure (ENNReal.inv_ne_top.mpr hKpos)

theorem gaussianPosition_mass_jensen_bound (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real K *
      Real.exp (((1 - R⁻¹ ^ 2) / 2) * (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2
        ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K)) ≤ R ^ n := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let ν := ProbabilityTheory.cond γ K
  let c : ℝ := (1 - R⁻¹ ^ 2) / 2
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure hKpos
  have hq : 0 < γ.real K := ENNReal.toReal_pos hKpos (measure_ne_top γ K)
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => c * ‖x‖ ^ 2) :=
    continuous_const.mul (continuous_norm.pow 2)
  have hJ := ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => mem_univ _)
    (gaussianPosition_cond_continuous_integrable n K hK hKpos _ hc)
    (gaussianPosition_cond_continuous_integrable n K hK hKpos _ (Real.continuous_exp.comp hc))
  rw [integral_const_mul] at hJ
  obtain ⟨hInt, hIntegral⟩ := gaussianPosition_gaussian_tilt_integral n R hR
  have hsub : (∫ x in K, standardGaussianDensity n x * Real.exp (c * ‖x‖ ^ 2)) ≤ R ^ n := by
    rw [← hIntegral]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun x => mul_nonneg
        (standardGaussianDensity_pos n x).le (Real.exp_pos _).le) hInt
  have hcond : (∫ x : EuclideanSpace ℝ (Fin n), Real.exp (c * ‖x‖ ^ 2) ∂ν) =
      (γ.real K)⁻¹ * (∫ x in K, standardGaussianDensity n x * Real.exp (c * ‖x‖ ^ 2)) := by
    dsimp only [ν, γ]
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
      gaussianPosition_gaussian_set_integral n K hK.measurableSet]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hcond] at hJ
  have h := mul_le_mul_of_nonneg_left hJ hq.le
  rw [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h
  exact h.trans hsub

theorem gaussianPosition_norm_second_moment (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0)
    (α : ℝ)
    (hsecond : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x i
      ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = α) :
    (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2
      ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = (n : ℝ) * α := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, pow_two]
  calc
    _ = ∑ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x i
        ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) := by
      exact integral_finsetSum Finset.univ (fun i _ =>
        (gaussianPosition_cond_coordinate_memLp n K hKpos i).integrable_mul
          (gaussianPosition_cond_coordinate_memLp n K hKpos i))
    _ = _ := by simp only [hsecond, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem gaussianPosition_mass_log_covariance_bound (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0)
    (α : ℝ) (hα : 0 < α)
    (hsecond : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x i
      ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = α) :
    Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))).real K) ≤
      ((n : ℝ) / 2) * (1 + Real.log α - α) := by
  have hq : 0 < (stdGaussian (EuclideanSpace ℝ (Fin n))).real K :=
    ENNReal.toReal_pos hKpos (measure_ne_top _ _)
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have h := gaussianPosition_mass_jensen_bound n K hK hKpos (Real.sqrt α) hs
  rw [gaussianPosition_norm_second_moment n K hKpos α hsecond] at h
  have hlog := Real.log_le_log (mul_pos hq (Real.exp_pos _)) h
  rw [Real.log_mul hq.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_pow,
    Real.log_sqrt hα.le] at hlog
  have hinv : (Real.sqrt α)⁻¹ ^ 2 * α = 1 := by
    rw [inv_pow, Real.sq_sqrt hα.le, inv_mul_cancel₀ hα.ne']
  have hpoly : ((1 - (Real.sqrt α)⁻¹ ^ 2) / 2) * ((n : ℝ) * α) =
      ((n : ℝ) / 2) * (α - 1) := by
    calc
      _ = ((n : ℝ) / 2) * (α - (Real.sqrt α)⁻¹ ^ 2 * α) := by ring
      _ = _ := by rw [hinv]
  rw [hpoly] at hlog
  nlinarith

theorem gaussianPosition_covariance_lower_of_mass_bound (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0)
    (α : ℝ) (hα : 0 < α)
    (hsecond : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x i
      ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = α)
    (C : ℝ) (hmass : Real.exp (-C * (n : ℝ)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real K) :
    Real.exp (-2 * C - 1) ≤ α := by
  have hlog := gaussianPosition_mass_log_covariance_bound n K hK hKpos α hα hsecond
  have hmasslog := Real.log_le_log (Real.exp_pos _) hmass
  rw [Real.log_exp] at hmasslog
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlin : (n : ℝ) * (-2 * C - 1) ≤ (n : ℝ) * Real.log α := by
    nlinarith [mul_nonneg hnpos.le hα.le]
  have hlin' : (-2 * C - 1) * (n : ℝ) ≤ Real.log α * (n : ℝ) := by
    simpa only [mul_comm] using hlin
  have hαlog := (mul_le_mul_iff_left₀ hnpos).mp hlin'
  exact (Real.exp_le_exp.mpr hαlog).trans_eq (Real.exp_log hα)

end AffineFKProof
