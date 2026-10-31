module

public import AffineFK.CovarianceWhiteningMatrix
public import AffineFK.ProbabilityCovarianceMatrix

/-!
# The covariance bounds for the actual ground-state convolution

The second summand's moment matrix is computed from its original law.
Its unit Poincare bound and zero means prove the upper matrix bound.
Adding the first summand's scalar covariance supplies the lower bound;
the actual inverse square-root map then has the required two norm bounds.
The separate sum-law moment transport identifies this matrix as the
covariance of the genuine independent convolution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

def convolutionCovarianceMatrix (n : ℕ) (α : ℝ)
    (η : Measure (EuclideanSpace ℝ (Fin n))) : Matrix (Fin n) (Fin n) ℝ :=
  α • 1 + probabilitySecondMomentMatrix n η

theorem convolutionCovarianceMatrix_bounds (n : ℕ)
    (η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure η]
    (hY : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 η)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂η) = 0)
    (hP : poincareConstant n η ≤ 1) (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1) :
    (convolutionCovarianceMatrix n α η - α • 1).PosSemidef ∧
      ((2 : ℝ) • 1 - convolutionCovarianceMatrix n α η).PosSemidef ∧
      (convolutionCovarianceMatrix n α η).PosDef := by
  have hlower : (convolutionCovarianceMatrix n α η - α • 1).PosSemidef := by
    have heq : convolutionCovarianceMatrix n α η - α • 1 = probabilitySecondMomentMatrix n η := by
      unfold convolutionCovarianceMatrix
      abel
    rw [heq]
    exact probabilitySecondMomentMatrix_posSemidef n η hY
  have hupper : ((2 : ℝ) • 1 - convolutionCovarianceMatrix n α η).PosSemidef := by
    have hsmall : ((1 - α) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
      (Matrix.PosDef.one.posSemidef).smul (sub_nonneg.mpr hαone)
    have hC := probabilitySecondMomentMatrix_le_one_of_poincare n η hY hmean hP
    have heq : (1 - α) • (1 : Matrix (Fin n) (Fin n) ℝ) + (1 - probabilitySecondMomentMatrix n η) =
        (2 : ℝ) • 1 - convolutionCovarianceMatrix n α η := by
      ext i j
      simp only [convolutionCovarianceMatrix, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul]
      ring
    exact heq ▸ hsmall.add hC
  exact ⟨hlower, hupper, covariance_posDef_of_lower n _ α hα hlower⟩

theorem convolutionCovarianceWhitening_norm_bounds (n : ℕ)
    (η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure η]
    (hY : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 η)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂η) = 0)
    (hP : poincareConstant n η ≤ 1) (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1) :
    let hM := (convolutionCovarianceMatrix_bounds n η hY hmean hP α hα hαone).2.2
    let A := covarianceWhiteningLinear n (convolutionCovarianceMatrix n α η) hM
    ‖A.toContinuousLinearMap‖ ^ 2 ≤ α⁻¹ ∧ ‖A.symm.toContinuousLinearMap‖ ^ 2 ≤ 2 := by
  obtain ⟨hlower, hupper, hM⟩ := convolutionCovarianceMatrix_bounds n η hY hmean hP α hα hαone
  exact ⟨covarianceWhiteningLinear_norm_sq_bound n _ hM α hα hlower,
    covarianceWhiteningLinear_inverse_norm_sq_bound n _ hM hupper⟩

end AffineFKProof
