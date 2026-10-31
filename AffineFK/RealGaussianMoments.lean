module

public import AffineFK.GaussianIntegrationByParts

/-!
# Low moments of the actual standard real Gaussian

Polynomial integrability follows from Sebastien Gouëzel's Gaussian-tail
integrability theorem in Mathlib. Haar integration by parts proves the
moment recurrence, without native numerical evaluation or assumed moments.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem gaussianPDFReal_standard_pow_integrable (k : ℕ) :
    Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * x ^ k) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ))
    (by norm_num) (s := (k : ℝ))
    (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg k))
  simp only [Real.rpow_natCast] at h
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    congr 2
    ring
  convert h.const_mul ((Real.sqrt (2 * Real.pi))⁻¹) using 1
  funext x
  rw [hpdf]
  ring

theorem gaussianReal_standard_pow_integrable (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0)]
  apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)).2
  simpa only [toReal_gaussianPDF, smul_eq_mul] using gaussianPDFReal_standard_pow_integrable k

theorem gaussianReal_standard_moment_recurrence (k : ℕ) :
    (∫ x : ℝ, x ^ (k + 2) ∂gaussianReal 0 1) =
      ((k + 1 : ℕ) : ℝ) * ∫ x : ℝ, x ^ k ∂gaussianReal 0 1 := by
  have hpoly (x : ℝ) : fderiv ℝ (fun y : ℝ => y ^ (k + 1)) x 1 =
      ((k + 1 : ℕ) : ℝ) * x ^ k := by
    have h := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1)
      (hasDerivAt_pow (k + 1) x).hasFDerivAt.fderiv
    simpa only [ContinuousLinearMap.toSpanSingleton_apply_one, Nat.add_sub_cancel] using h
  have hleft : Integrable (fun x : ℝ => fderiv ℝ (gaussianPDFReal 0 1) x 1 * x ^ (k + 1)) := by
    convert (gaussianPDFReal_standard_pow_integrable (k + 2)).neg using 1
    funext x
    rw [gaussianPDFReal_standard_fderiv_one]
    simp only [Pi.neg_apply, pow_succ]
    ring
  have hright : Integrable (fun x : ℝ =>
      gaussianPDFReal 0 1 x * fderiv ℝ (fun y : ℝ => y ^ (k + 1)) x 1) := by
    convert (gaussianPDFReal_standard_pow_integrable k).const_mul ((k + 1 : ℕ) : ℝ) using 1
    funext x
    rw [hpoly]
    ring
  have hproduct := gaussianPDFReal_standard_pow_integrable (k + 1)
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hleft hright hproduct
    (fun x _ => (gaussianPDFReal_standard_hasDerivAt x).differentiableAt)
    (fun x _ => (hasDerivAt_pow (k + 1) x).differentiableAt)
  simp only [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0),
    smul_eq_mul]
  calc
    _ = -(∫ x : ℝ, fderiv ℝ (gaussianPDFReal 0 1) x 1 * x ^ (k + 1)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change gaussianPDFReal 0 1 x * x ^ (k + 2) =
          -(fderiv ℝ (gaussianPDFReal 0 1) x 1 * x ^ (k + 1))
        rw [gaussianPDFReal_standard_fderiv_one]
        simp only [pow_succ]
        ring
    _ = ∫ x : ℝ, gaussianPDFReal 0 1 x * fderiv ℝ (fun y : ℝ => y ^ (k + 1)) x 1 := hparts.symm
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change gaussianPDFReal 0 1 x * fderiv ℝ (fun y : ℝ => y ^ (k + 1)) x 1 =
          ((k + 1 : ℕ) : ℝ) * (gaussianPDFReal 0 1 x * x ^ k)
        rw [hpoly]
        ring

theorem gaussianReal_standard_second_moment :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  simpa using gaussianReal_standard_moment_recurrence 0

theorem gaussianReal_standard_third_moment :
    (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) = 0 := by
  simpa [integral_id_gaussianReal] using gaussianReal_standard_moment_recurrence 1

theorem gaussianReal_standard_fourth_moment :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  simpa [gaussianReal_standard_second_moment] using gaussianReal_standard_moment_recurrence 2

end AffineFKProof
