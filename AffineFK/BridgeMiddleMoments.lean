module

public import AffineFK.BridgeMiddleGaussianComponents

/-!
# Actual means and component covariances of the Gaussian-middle bridge

Every moment is evaluated under the genuine coefficient product and
standard Gaussian laws. The cross terms vanish by proved independence,
not by an assumed covariance specification for the assembled process.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

theorem bridgeMiddleFirstProcess_mean (n : ℕ) (s t : ℝ) (hs : 0 < s)
    (q : Icc (0 : ℝ) (s+t) × Fin n) :
    (∫ ω, bridgeMiddleFirstProcess n s t hs q ω ∂bridgeCoefficientMeasure n) = 0 := by
  unfold bridgeMiddleFirstProcess
  rw [integral_const_mul, bridgeContinuousSeries_coordinate_mean, mul_zero]

theorem bridgeMiddleSecondProcess_mean (n : ℕ) (s t : ℝ) (ht : 0 < t)
    (q : Icc (0 : ℝ) (s+t) × Fin n) :
    (∫ ω, bridgeMiddleSecondProcess n s t ht q ω ∂bridgeCoefficientMeasure n) = 0 := by
  unfold bridgeMiddleSecondProcess
  rw [integral_const_mul, bridgeContinuousSeries_coordinate_mean, mul_zero]

theorem bridgeMiddleEndpointProcess_mean (n : ℕ) (s t : ℝ)
    (q : Icc (0 : ℝ) (s+t) × Fin n) :
    (∫ z, bridgeMiddleEndpointProcess n s t q z ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
  unfold bridgeMiddleEndpointProcess
  rw [integral_const_mul, bridgeGaussian_coordinate_mean, mul_zero]

theorem bridgeSplitCenteredPath_mean (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (q : Icc (0 : ℝ) (s+t) × Fin n) :
    (∫ p, bridgeSplitCenteredPath n s t hs ht p q.1 q.2 ∂bridgeMiddleMeasure n) = 0 := by
  let X := bridgeMiddleFirstProcess n s t hs
  let Y := bridgeMiddleSecondProcess n s t ht
  let Z := bridgeMiddleEndpointProcess n s t
  have hX := bridgeMiddleFirstProcess_gaussian n s t hs
  have hY := bridgeMiddleSecondProcess_gaussian n s t ht
  have hZ := bridgeMiddleEndpointProcess_gaussian n s t
  have hpair := bridge_gaussian_process_prod_sum (bridgeCoefficientMeasure n) (bridgeCoefficientMeasure n)
    X Y hX hY
  have heq : (fun p : BridgeMiddleSample n => bridgeSplitCenteredPath n s t hs ht p q.1 q.2) =
      fun p => (X q p.1.1+Y q p.1.2)+Z q p.2 := by
    funext p
    exact bridgeSplitCenteredPath_components n s t hs ht p q
  rw [heq]
  change (∫ p : BridgeMiddleSample n, (X q p.1.1+Y q p.1.2)+Z q p.2
    ∂((bridgeCoefficientMeasure n).prod (bridgeCoefficientMeasure n)).prod
      (stdGaussian (EuclideanSpace ℝ (Fin n)))) = 0
  rw [bridge_integral_prod_sum _ _ _ _
    ((hpair.hasGaussianLaw_eval q).memLp_two.integrable (by norm_num))
    ((hZ.hasGaussianLaw_eval q).memLp_two.integrable (by norm_num)),
    bridge_integral_prod_sum _ _ _ _
      ((hX.hasGaussianLaw_eval q).memLp_two.integrable (by norm_num))
      ((hY.hasGaussianLaw_eval q).memLp_two.integrable (by norm_num))]
  rw [bridgeMiddleFirstProcess_mean, bridgeMiddleSecondProcess_mean, bridgeMiddleEndpointProcess_mean]
  norm_num

theorem bridgeMiddleFirstProcess_covariance (n : ℕ) (s t : ℝ) (hs : 0 < s)
    (q r : Icc (0 : ℝ) (s+t) × Fin n) :
    cov[bridgeMiddleFirstProcess n s t hs q, bridgeMiddleFirstProcess n s t hs r; bridgeCoefficientMeasure n] =
      (bridgeMiddleFirstFactor s q.1 * bridgeMiddleFirstFactor s r.1) *
        (min (bridgeMiddleFirstTime s t hs q.1:ℝ) (bridgeMiddleFirstTime s t hs r.1:ℝ) -
          (bridgeMiddleFirstTime s t hs q.1:ℝ)*(bridgeMiddleFirstTime s t hs r.1:ℝ)) *
        (if q.2=r.2 then 1 else 0) := by
  unfold bridgeMiddleFirstProcess
  rw [covariance_const_mul_left, covariance_const_mul_right, bridgeContinuousSeries_brownian_covariance]
  ring

theorem bridgeMiddleSecondProcess_covariance (n : ℕ) (s t : ℝ) (ht : 0 < t)
    (q r : Icc (0 : ℝ) (s+t) × Fin n) :
    cov[bridgeMiddleSecondProcess n s t ht q, bridgeMiddleSecondProcess n s t ht r; bridgeCoefficientMeasure n] =
      (bridgeMiddleSecondFactor s t q.1 * bridgeMiddleSecondFactor s t r.1) *
        (min (bridgeMiddleSecondTime s t ht q.1:ℝ) (bridgeMiddleSecondTime s t ht r.1:ℝ) -
          (bridgeMiddleSecondTime s t ht q.1:ℝ)*(bridgeMiddleSecondTime s t ht r.1:ℝ)) *
        (if q.2=r.2 then 1 else 0) := by
  unfold bridgeMiddleSecondProcess
  rw [covariance_const_mul_left, covariance_const_mul_right, bridgeContinuousSeries_brownian_covariance]
  ring

theorem bridgeMiddleEndpointProcess_covariance (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (q r : Icc (0 : ℝ) (s+t) × Fin n) :
    cov[bridgeMiddleEndpointProcess n s t q, bridgeMiddleEndpointProcess n s t r;
      stdGaussian (EuclideanSpace ℝ (Fin n))] =
      bridgeMiddleLinearCoefficient s t q.1 * bridgeMiddleLinearCoefficient s t r.1 *
        (s*t/(s+t)) * (if q.2=r.2 then 1 else 0) := by
  have hGi (i : Fin n) : MemLp (fun z : EuclideanSpace ℝ (Fin n) => z i) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa only [coordinateFunctional_apply, Function.comp_def, id_eq] using
      ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (coordinateFunctional n i)).memLp_two
  have hc : cov[fun z : EuclideanSpace ℝ (Fin n) => z q.2, fun z => z r.2;
      stdGaussian (EuclideanSpace ℝ (Fin n))] = if q.2=r.2 then 1 else 0 := by
    rw [covariance_eq_sub (hGi q.2) (hGi r.2), bridgeGaussian_coordinate_mean,
      bridgeGaussian_coordinate_mean, zero_mul, sub_zero]
    exact bridgeGaussian_coordinate_cross_moment n q.2 r.2
  unfold bridgeMiddleEndpointProcess
  rw [covariance_const_mul_left, covariance_const_mul_right, hc]
  calc
    _ = bridgeMiddleLinearCoefficient s t q.1 * bridgeMiddleLinearCoefficient s t r.1 *
      (bridgeMiddleScale s t)^2 * (if q.2=r.2 then 1 else 0) := by ring
    _ = _ := by rw [bridgeMiddleScale_sq s t hs ht]

end AffineFKProof
