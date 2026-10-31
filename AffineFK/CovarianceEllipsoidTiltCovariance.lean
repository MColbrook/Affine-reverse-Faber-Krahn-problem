module

public import AffineFK.CovarianceEllipsoidConstruction
public import AffineFK.GaussianPositionTiltMeanMap
public import AffineFK.GaussianPositionTiltBounds

/-!
# Actual tilted covariance, positive definiteness and the mean Jacobian

The center is the genuine gradient of the log-Laplace function. Its
proved expectation formula supplies the mean. The matrix is the actual
centered coordinate integral, identified with the actual derivative of
the mean map through the already proved covariance formula. Strict
variance positivity proves positive definiteness; neither a covariance
identity nor a positive-definiteness conclusion is supplied as a premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

def covarianceEllipsoidTiltMatrix (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (y : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  covarianceEllipsoidMomentMatrix n (gaussianPositionTiltLaw n K y)
    (gradient (gaussianPositionLogLaplace n K) y)

theorem covarianceEllipsoidTilt_identity_memLp (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) :
    MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (gaussianPositionTiltLaw n K y) := by
  apply (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr
  exact gaussianPositionTiltLaw_continuous_integrable n K hK hvol y
    (fun x => ‖x‖^2) (continuous_norm.pow 2)

theorem covarianceEllipsoidTilt_mean_coordinate (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i ∂gaussianPositionTiltLaw n K y) =
      (gradient (gaussianPositionLogLaplace n K) y) i := by
  rw [gaussianPositionLogLaplace_gradient_mean n K hK hvol y]
  have h := (coordinateFunctional n i).integral_comp_comm
    (gaussianPositionTiltLaw_continuous_integrable n K hK hvol y id continuous_id)
  simpa only [coordinateFunctional_apply,id_eq] using h

theorem covarianceEllipsoidTiltMatrix_entry (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    covarianceEllipsoidTiltMatrix n K y i j =
      covariance (fun x : EuclideanSpace ℝ (Fin n) => x i) (fun x => x j)
        (gaussianPositionTiltLaw n K y) :=
  covarianceEllipsoidMomentMatrix_covariance n _ _
    (covarianceEllipsoidTilt_mean_coordinate n K hK hvol y) i j

theorem covarianceEllipsoid_matrix_basis_entry (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M (EuclideanSpace.basisFun (Fin n) ℝ j)) i = M i j := by
  change (WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M
    (EuclideanSpace.basisFun (Fin n) ℝ j))) i = M i j
  rw [Matrix.ofLp_toEuclideanCLM,EuclideanSpace.basisFun_apply,PiLp.ofLp_single]
  simp [Matrix.mulVec,dotProduct,Pi.single_apply]

set_option maxHeartbeats 800000 in
theorem covarianceEllipsoidTiltMatrix_operator (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (covarianceEllipsoidTiltMatrix n K y) =
      fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y := by
  let : IsProbabilityMeasure (gaussianPositionTiltLaw n K y) :=
    gaussianPositionTiltLaw_isProbabilityMeasure n K hK hvol y
  have hX := covarianceEllipsoidTilt_identity_memLp n K hK hvol y
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro j
  ext i
  change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (covarianceEllipsoidTiltMatrix n K y)
    (EuclideanSpace.basisFun (Fin n) ℝ j)) i =
      ((fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) i
  have h := gaussianPositionLogLaplace_gradient_derivative_covariance n K hK hvol y
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
  simp_rw [EuclideanSpace.inner_basisFun_real] at h
  have hi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 (gaussianPositionTiltLaw n K y) :=
    hX.eval_piLp i
  have hj : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x j) 2 (gaussianPositionTiltLaw n K y) :=
    hX.eval_piLp j
  rw [covarianceEllipsoid_matrix_basis_entry,covarianceEllipsoidTiltMatrix_entry n K hK hvol]
  rw [covariance_eq_sub hi hj]
  exact h.symm

set_option maxHeartbeats 800000 in
theorem covarianceEllipsoidTiltMatrix_posDef (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) : (covarianceEllipsoidTiltMatrix n K y).PosDef := by
  let μ := gaussianPositionTiltLaw n K y
  let m := gradient (gaussianPositionLogLaplace n K) y
  let M := covarianceEllipsoidTiltMatrix n K y
  let : IsProbabilityMeasure μ := gaussianPositionTiltLaw_isProbabilityMeasure n K hK hvol y
  have hX := covarianceEllipsoidTilt_identity_memLp n K hK hvol y
  have hPSD : M.PosSemidef := probabilitySecondMomentMatrix_posSemidef n
    (covarianceEllipsoidCenteredLaw n μ m) (covarianceEllipsoidCenteredLaw_memLp n μ hX m)
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hPSD.isHermitian
  intro v hv
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  have hw : w ≠ 0 := by
    intro hz
    exact hv ((WithLp.toLp_eq_zero 2).mp hz)
  have hF := gaussianPositionTiltLaw_continuous_memLp_two n K hK hvol y
    (fun x => ⟪x,w⟫) (continuous_id.inner continuous_const)
  have hpositive := gaussianPositionTiltLaw_linear_variance_pos n K hK hvol y w hw
  rw [variance_eq_sub hF] at hpositive
  simp only [Pi.pow_apply,pow_two] at hpositive
  have hderivative := gaussianPositionLogLaplace_gradient_derivative_covariance n K hK hvol y w w
  have hinner : 0 < ⟪w,Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M w⟫ := by
    rw [covarianceEllipsoidTiltMatrix_operator n K hK hvol,real_inner_comm,hderivative]
    exact hpositive
  have hstar : star v = v := by funext i; exact star_trivial _
  rw [hstar]
  simpa only [Matrix.inner_toEuclideanCLM,w,WithLp.ofLp_toLp] using hinner

theorem covarianceEllipsoidTiltMatrix_det_derivative (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) :
    (covarianceEllipsoidTiltMatrix n K y).det =
      LinearMap.det ((fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) := by
  rw [← covarianceEllipsoidTiltMatrix_operator n K hK hvol,gaussianPosition_matrix_det]

end AffineFKProof
