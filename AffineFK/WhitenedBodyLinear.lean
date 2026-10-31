module

public import AffineFK.WhitenedConvolutionSupport

/-! The actual invertible map defining the source's support body, with its
proved Euclidean operator-norm bound. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

def covarianceWhiteningBodyLinear (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (covarianceWhiteningLinear n M hM).trans
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) (2 : ℝ) (by norm_num)).toContinuousLinearEquiv

theorem covarianceWhiteningBodyLinear_apply (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    covarianceWhiteningBodyLinear n M hM x =
      (2 : ℝ) • Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (covarianceWhiteningMatrix n M) x := rfl

theorem covarianceWhiteningBodyLinear_norm_sq_bound (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) (α : ℝ) (hα : 0 < α)
    (hlower : (M - α • 1).PosSemidef) :
    ‖(covarianceWhiteningBodyLinear n M hM).toContinuousLinearMap‖ ^ 2 ≤ 4 / α := by
  have hA : (covarianceWhiteningBodyLinear n M hM).toContinuousLinearMap =
      (2 : ℝ) • (covarianceWhiteningLinear n M hM).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  rw [hA, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
  have h := mul_le_mul_of_nonneg_left
    (covarianceWhiteningLinear_norm_sq_bound n M hM α hα hlower) (by norm_num : (0 : ℝ) ≤ 4)
  norm_num only [pow_two] at *
  simpa only [div_eq_mul_inv] using h

theorem whitenedSupportBody_eq_linear_image (n : ℕ)
    (η : Measure (EuclideanSpace ℝ (Fin n))) (α : ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hM : (convolutionCovarianceMatrix n α η).PosDef) :
    whitenedSupportBody n η α K = covarianceWhiteningBodyLinear n _ hM '' K := rfl

end AffineFKProof
