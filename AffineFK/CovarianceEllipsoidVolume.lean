module

public import AffineFK.CovarianceEllipsoidMass
public import AffineFK.CovarianceEllipsoidBallVolume
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Actual Jacobian volume of the covariance ellipsoid

Haar translation invariance and the genuine linear determinant formula
give the exact volume. Matrix.PosSemidef.det_sqrt supplies the CFC square
root determinant. A supplied covariance determinant bound then gives a
dimension-exponential volume bound with an explicit base.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix Set Metric
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator

theorem covarianceEllipsoid_translate_volume (n : ℕ) (m : EuclideanSpace ℝ (Fin n))
    (F : Set (EuclideanSpace ℝ (Fin n))) :
    volume ((fun x => m+x) '' F) = volume F := by
  have h := (measurePreserving_add_left volume m).measure_preimage_emb
    (Homeomorph.addLeft m).measurableEmbedding ((fun x => m+x) '' F)
  rw [Set.preimage_image_eq _ (add_right_injective m)] at h
  exact h.symm

theorem covarianceEllipsoid_inverse_det (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    |LinearMap.det ((covarianceWhiteningLinear n M hM).symm :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))| = Real.sqrt M.det := by
  have hEq : ((covarianceWhiteningLinear n M hM).symm :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (CFC.sqrt M)).toLinearMap := by
    apply LinearMap.ext
    intro x
    exact covarianceEllipsoid_inverse_sqrt_apply n M hM x
  rw [hEq,gaussianPosition_matrix_det]
  have hroot : (CFC.sqrt M).det = Real.sqrt M.det := by
    simpa only [RCLike.sqrt_real] using hM.posSemidef.det_sqrt
  rw [hroot,abs_of_nonneg (Real.sqrt_nonneg _)]

theorem covarianceEllipsoidSet_volume (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (m : EuclideanSpace ℝ (Fin n))
    (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef) :
    volume (covarianceEllipsoidSet n μ m hM) =
      ENNReal.ofReal (Real.sqrt (covarianceEllipsoidMomentMatrix n μ m).det) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ)))) := by
  let W := covarianceWhiteningLinear n (covarianceEllipsoidMomentMatrix n μ m) hM
  rw [covarianceEllipsoidSet_inverse_image]
  calc
    _ = volume ((fun x => m+x) '' (W.symm ''
        closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ))))) := by
      rw [image_image]
    _ = volume (W.symm '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ)))) :=
      covarianceEllipsoid_translate_volume n m _
    _ = _ := by
      rw [Measure.addHaar_image_continuousLinearEquiv,covarianceEllipsoid_inverse_det]

theorem covarianceEllipsoidSet_real_volume (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (m : EuclideanSpace ℝ (Fin n))
    (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef) :
    (volume (covarianceEllipsoidSet n μ m hM)).toReal =
      Real.sqrt (covarianceEllipsoidMomentMatrix n μ m).det *
        (volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ))))).toReal := by
  rw [covarianceEllipsoidSet_volume,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

theorem covarianceEllipsoidSet_volume_bound (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (m : EuclideanSpace ℝ (Fin n))
    (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef)
    (C : ℝ) (hC : 0 ≤ C) (hdet : (covarianceEllipsoidMomentMatrix n μ m).det ≤ C^n) :
    (volume (covarianceEllipsoidSet n μ m hM)).toReal ≤
      (Real.sqrt C*covarianceEllipsoidBallVolumeBase)^n := by
  have hsqrtpow : Real.sqrt (C^n) = (Real.sqrt C)^n := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) n)).mp
    rw [Real.sq_sqrt (pow_nonneg hC n),← pow_mul,Nat.mul_comm n 2,pow_mul,Real.sq_sqrt hC]
  have hsqrt : Real.sqrt (covarianceEllipsoidMomentMatrix n μ m).det ≤ (Real.sqrt C)^n :=
    (Real.sqrt_le_sqrt hdet).trans_eq hsqrtpow
  rw [covarianceEllipsoidSet_real_volume]
  calc
    _ ≤ (Real.sqrt C)^n * covarianceEllipsoidBallVolumeBase^n :=
      mul_le_mul hsqrt (covarianceEllipsoid_ball_volume n) ENNReal.toReal_nonneg
        (pow_nonneg (Real.sqrt_nonneg _) n)
    _ = _ := (mul_pow _ _ _).symm

theorem covarianceEllipsoid_volume_base_pos (C : ℝ) (hC : 0 < C) :
    0 < Real.sqrt C*covarianceEllipsoidBallVolumeBase :=
  mul_pos (Real.sqrt_pos.mpr hC) covarianceEllipsoidBallVolumeBase_pos

end AffineFKProof
