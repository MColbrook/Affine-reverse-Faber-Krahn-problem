module

public import AffineFK.WeightedSobolev
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Integration by parts for the standard real Gaussian

The density is Mathlib's actual gaussianReal 0 1 density. Compact smooth
tests supply the integrability needed for the Haar-space integration-by-parts
theorem. The Gaussian definitions are due to Lorenzo Luccioli, Remy Degenne
and Alexander Bentkamp; Haar integration by parts is due to Sebastien Gouëzel.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

def realDerivativeTest (φ : 𝓓((⊤ : Opens ℝ), ℝ)) : 𝓓((⊤ : Opens ℝ), ℝ) :=
  TestFunction.lineDerivCLM ℝ (1 : ℝ) φ

theorem realDerivativeTest_fderiv
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) (x : ℝ) :
    realDerivativeTest φ x = fderiv ℝ φ x (1 : ℝ) := by
  change (TestFunction.fderivCLM ℝ ⊤ ⊤ φ) x (1 : ℝ) = _
  rw [TestFunction.fderivCLM_apply_of_le φ (by simp)]

theorem gaussianPDFReal_standard_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hq : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    convert (((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ)) using 1 <;> norm_num <;> ring
  have hfun : gaussianPDFReal 0 1 =
      fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2) := by
    funext y
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [hfun]
  convert hq.exp.const_mul ((Real.sqrt (2 * Real.pi))⁻¹) using 1 <;> ring

theorem gaussianPDFReal_standard_fderiv_one (x : ℝ) :
    fderiv ℝ (gaussianPDFReal 0 1) x (1 : ℝ) = -x * gaussianPDFReal 0 1 x := by
  have h := (gaussianPDFReal_standard_hasDerivAt x).hasFDerivAt.fderiv
  simpa using congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h

theorem gaussianReal_standard_integration_by_parts
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    Integrable (fun x : ℝ => x * φ x) (gaussianReal 0 1) ∧
    Integrable (realDerivativeTest φ) (gaussianReal 0 1) ∧
      (∫ x, x * φ x ∂gaussianReal 0 1) = ∫ x, realDerivativeTest φ x ∂gaussianReal 0 1 := by
  have hpdf : Differentiable ℝ (gaussianPDFReal 0 1) :=
    fun x => (gaussianPDFReal_standard_hasDerivAt x).differentiableAt
  have hleft : Integrable (fun x : ℝ => fderiv ℝ (gaussianPDFReal 0 1) x 1 * φ x) := by
    simp_rw [gaussianPDFReal_standard_fderiv_one]
    exact ((continuous_id.neg.mul hpdf.continuous).mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left
  have hright : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * fderiv ℝ φ x 1) := by
    simp_rw [← realDerivativeTest_fderiv]
    exact (hpdf.continuous.mul (realDerivativeTest φ).continuous).integrable_of_hasCompactSupport
      (realDerivativeTest φ).hasCompactSupport.mul_left
  have hproduct : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * φ x) :=
    (hpdf.continuous.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hleft hright hproduct
    (fun x _hx => hpdf.differentiableAt)
    (fun x _hx => (φ.contDiff.differentiable (by simp)).differentiableAt)
  have hfirst : Integrable (fun x : ℝ => x * φ x) (gaussianReal 0 1) :=
    (continuous_id.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have hderiv : Integrable (realDerivativeTest φ) (gaussianReal 0 1) :=
    (realDerivativeTest φ).continuous.integrable_of_hasCompactSupport (realDerivativeTest φ).hasCompactSupport
  refine ⟨hfirst, hderiv, ?_⟩
  symm
  calc
    _ = ∫ x, gaussianPDFReal 0 1 x * fderiv ℝ φ x 1 := by
      rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => congrArg (fun y : ℝ => gaussianPDFReal 0 1 x * y)
        (realDerivativeTest_fderiv φ x)
    _ = -(∫ x, fderiv ℝ (gaussianPDFReal 0 1) x 1 * φ x) := hparts
    _ = ∫ x, gaussianPDFReal 0 1 x * (x * φ x) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change -(fderiv ℝ (gaussianPDFReal 0 1) x 1 * φ x) = gaussianPDFReal 0 1 x * (x * φ x)
        rw [gaussianPDFReal_standard_fderiv_one]
        ring
    _ = _ := by
      simpa only [smul_eq_mul] using
        (integral_gaussianReal_eq_integral_smul (f := fun x : ℝ => x * φ x)
          (by norm_num : (1 : NNReal) ≠ 0)).symm

end AffineFKProof
