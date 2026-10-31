module

public import AffineFK.GaussianPositionAction
public import AffineFK.CovarianceWhiteningQuadratic
public import Mathlib.Analysis.Matrix.Order

/-!
# The actual inverse-square-root covariance map

The matrix is the inverse of the genuine C-star square root. Positive
definiteness, its whitening identity and the two required operator-norm
bounds follow from literal positive-semidefinite covariance bounds.
The matrix norm is the actual Euclidean operator norm throughout.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

def covarianceWhiteningMatrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (CFC.sqrt M)⁻¹

theorem covariance_sqrt_posDef (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    (CFC.sqrt M).PosDef :=
  (CFC.sqrt_nonneg M).posSemidef.posDef_iff_isUnit.mpr
    ((CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit)

theorem covarianceWhiteningMatrix_posDef (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    (covarianceWhiteningMatrix n M).PosDef :=
  Matrix.posDef_inv_iff.mpr (covariance_sqrt_posDef n M hM)

theorem covarianceWhiteningMatrix_identity (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    covarianceWhiteningMatrix n M * M * (covarianceWhiteningMatrix n M)ᴴ = 1 := by
  have hS := covariance_sqrt_posDef n M hM
  have hunit : IsUnit (CFC.sqrt M).det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hW := covarianceWhiteningMatrix_posDef n M hM
  rw [show (covarianceWhiteningMatrix n M)ᴴ = covarianceWhiteningMatrix n M from hW.isHermitian]
  calc
    _ = (CFC.sqrt M)⁻¹ * (CFC.sqrt M * CFC.sqrt M) * (CFC.sqrt M)⁻¹ :=
      congrArg (fun N => (CFC.sqrt M)⁻¹ * N * (CFC.sqrt M)⁻¹)
        (CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg).symm
    _ = 1 := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit,
        Matrix.one_mul, Matrix.mul_nonsing_inv _ hunit]

theorem covariance_posDef_of_lower (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (α : ℝ) (hα : 0 < α) (hlower : (M - α • 1).PosSemidef) : M.PosDef := by
  have h := (Matrix.PosDef.one.smul hα).add_posSemidef hlower
  have heq : (α • (1 : Matrix (Fin n) (Fin n) ℝ)) + (M - α • 1) = M := by abel
  rwa [heq] at h

theorem covarianceWhiteningMatrix_norm_sq_bound (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) (hα : 0 < α)
    (hlower : (M - α • 1).PosSemidef) :
    ‖covarianceWhiteningMatrix n M‖ ^ 2 ≤ α⁻¹ := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
  let W := covarianceWhiteningMatrix n M
  have hM := covariance_posDef_of_lower n M α hα hlower
  have hS := covariance_sqrt_posDef n M hM
  have hunit : IsUnit (CFC.sqrt M).det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hSW (x : EuclideanSpace ℝ (Fin n)) : T (CFC.sqrt M) (T W x) = x := by
    change (T (CFC.sqrt M) * T W) x = x
    rw [← map_mul]
    dsimp only [W, covarianceWhiteningMatrix]
    rw [Matrix.mul_nonsing_inv _ hunit, map_one]
    rfl
  have hroot : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hnorm : ‖T W‖ ≤ (Real.sqrt α)⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hroot.le)
    intro x
    have hq := covariance_matrix_quadratic_lower n M α hlower (T W x)
    rw [← covariance_sqrt_apply_norm_sq n M hM, hSW] at hq
    have hsq : (Real.sqrt α * ‖T W x‖) ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hα.le]
      exact hq
    have hlin := (sq_le_sq₀ (mul_nonneg hroot.le (norm_nonneg _)) (norm_nonneg x)).mp hsq
    have hdiv := (le_div_iff₀ hroot).mpr (show ‖T W x‖ * Real.sqrt α ≤ ‖x‖ by
      simpa only [mul_comm] using hlin)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  have hsq := pow_le_pow_left₀ (norm_nonneg (T W)) hnorm 2
  rw [inv_pow, Real.sq_sqrt hα.le] at hsq
  exact hsq

theorem covarianceWhiteningMatrix_inverse_norm_sq_bound (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (hupper : ((2 : ℝ) • 1 - M).PosSemidef) :
    ‖(covarianceWhiteningMatrix n M)⁻¹‖ ^ 2 ≤ 2 := by
  have hS := covariance_sqrt_posDef n M hM
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
  have hunit : IsUnit (CFC.sqrt M).det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hnorm : ‖T (CFC.sqrt M)‖ ≤ Real.sqrt 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    have hq := covariance_matrix_quadratic_upper n M 2 hupper x
    rw [← covariance_sqrt_apply_norm_sq n M hM] at hq
    have hsq : ‖T (CFC.sqrt M) x‖ ^ 2 ≤ (Real.sqrt 2 * ‖x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact hq
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq
  rw [covarianceWhiteningMatrix, Matrix.nonsing_inv_nonsing_inv _ hunit]
  have hsq := pow_le_pow_left₀ (norm_nonneg (T (CFC.sqrt M))) hnorm 2
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsq
  exact hsq

def covarianceWhiteningLinear (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (covarianceWhiteningMatrix n M)).toLinearMap.equivOfDetNeZero
    (by rw [gaussianPosition_matrix_det]; exact (covarianceWhiteningMatrix_posDef n M hM).det_pos.ne')).toContinuousLinearEquiv

theorem covarianceWhiteningLinear_apply (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    covarianceWhiteningLinear n M hM x =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (covarianceWhiteningMatrix n M) x := rfl

theorem covarianceWhiteningLinear_inverse_apply (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    (covarianceWhiteningLinear n M hM).symm x =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (covarianceWhiteningMatrix n M)⁻¹ x := by
  have hW := covarianceWhiteningMatrix_posDef n M hM
  have hunit : IsUnit (covarianceWhiteningMatrix n M).det := isUnit_iff_ne_zero.mpr hW.det_pos.ne'
  apply (covarianceWhiteningLinear n M hM).injective
  rw [(covarianceWhiteningLinear n M hM).apply_symm_apply, covarianceWhiteningLinear_apply]
  change x = (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (covarianceWhiteningMatrix n M) *
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (covarianceWhiteningMatrix n M)⁻¹) x
  rw [← map_mul, Matrix.mul_nonsing_inv _ hunit, map_one]
  rfl

theorem covarianceWhiteningLinear_norm_sq_bound (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (α : ℝ) (hα : 0 < α) (hlower : (M - α • 1).PosSemidef) :
    ‖(covarianceWhiteningLinear n M hM).toContinuousLinearMap‖ ^ 2 ≤ α⁻¹ :=
  covarianceWhiteningMatrix_norm_sq_bound n M α hα hlower

theorem covarianceWhiteningLinear_inverse_norm_sq_bound (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (hupper : ((2 : ℝ) • 1 - M).PosSemidef) :
    ‖(covarianceWhiteningLinear n M hM).symm.toContinuousLinearMap‖ ^ 2 ≤ 2 := by
  have heq : (covarianceWhiteningLinear n M hM).symm.toContinuousLinearMap =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (covarianceWhiteningMatrix n M)⁻¹ := by
    apply ContinuousLinearMap.ext
    intro x
    exact covarianceWhiteningLinear_inverse_apply n M hM x
  rw [heq]
  exact covarianceWhiteningMatrix_inverse_norm_sq_bound n M hM hupper

end AffineFKProof
