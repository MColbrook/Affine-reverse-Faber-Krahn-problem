module

public import AffineFK.BridgeMiddleMoments
public import AffineFK.BridgeMiddleCovarianceAlgebra
public import Mathlib.Tactic.LinearCombination

/-!
# Actual full bridge covariance of the Gaussian-middle construction

Product independence eliminates the cross terms. The three actual
component covariances and their exact scalar identity give the full
centered Brownian-bridge covariance on `[0,s+t]`.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

theorem bridgeMiddleFirstTime_value (s t : ℝ) (hs : 0 < s) (r : Icc (0 : ℝ) (s+t)) :
    (bridgeMiddleFirstTime s t hs r:ℝ) = if (r:ℝ) ≤ s then (r:ℝ)/s else 0 := by
  unfold bridgeMiddleFirstTime
  split_ifs <;> rfl

theorem bridgeMiddleSecondTime_value (s t : ℝ) (ht : 0 < t) (r : Icc (0 : ℝ) (s+t)) :
    (bridgeMiddleSecondTime s t ht r:ℝ) = if (r:ℝ) ≤ s then 0 else ((r:ℝ)-s)/t := by
  unfold bridgeMiddleSecondTime
  split_ifs <;> rfl

theorem bridgeSplitCenteredPath_covariance_components (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (q r : Icc (0 : ℝ) (s+t) × Fin n) :
    cov[fun p => bridgeSplitCenteredPath n s t hs ht p q.1 q.2,
      fun p => bridgeSplitCenteredPath n s t hs ht p r.1 r.2; bridgeMiddleMeasure n] =
      (bridgeMiddleFirstFactor s q.1 * bridgeMiddleFirstFactor s r.1) *
        (min (bridgeMiddleFirstTime s t hs q.1:ℝ) (bridgeMiddleFirstTime s t hs r.1:ℝ) -
          (bridgeMiddleFirstTime s t hs q.1:ℝ)*(bridgeMiddleFirstTime s t hs r.1:ℝ)) *
        (if q.2=r.2 then 1 else 0) +
      (bridgeMiddleSecondFactor s t q.1 * bridgeMiddleSecondFactor s t r.1) *
        (min (bridgeMiddleSecondTime s t ht q.1:ℝ) (bridgeMiddleSecondTime s t ht r.1:ℝ) -
          (bridgeMiddleSecondTime s t ht q.1:ℝ)*(bridgeMiddleSecondTime s t ht r.1:ℝ)) *
        (if q.2=r.2 then 1 else 0) +
      bridgeMiddleLinearCoefficient s t q.1 * bridgeMiddleLinearCoefficient s t r.1 *
        (s*t/(s+t)) * (if q.2=r.2 then 1 else 0) := by
  let X := bridgeMiddleFirstProcess n s t hs
  let Y := bridgeMiddleSecondProcess n s t ht
  let Z := bridgeMiddleEndpointProcess n s t
  let V := fun q (p : (∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n)) ×
      (∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n))) => X q p.1+Y q p.2
  have hX := bridgeMiddleFirstProcess_gaussian n s t hs
  have hY := bridgeMiddleSecondProcess_gaussian n s t ht
  have hZ := bridgeMiddleEndpointProcess_gaussian n s t
  have hV : IsGaussianProcess V ((bridgeCoefficientMeasure n).prod (bridgeCoefficientMeasure n)) :=
    bridge_gaussian_process_prod_sum _ _ X Y hX hY
  have heq (a : Icc (0 : ℝ) (s+t) × Fin n) :
      (fun p : BridgeMiddleSample n => bridgeSplitCenteredPath n s t hs ht p a.1 a.2) =
        fun p => V a p.1+Z a p.2 := by
    funext p
    exact bridgeSplitCenteredPath_components n s t hs ht p a
  rw [heq q, heq r]
  change cov[fun p : BridgeMiddleSample n => V q p.1+Z q p.2, fun p => V r p.1+Z r p.2;
    ((bridgeCoefficientMeasure n).prod (bridgeCoefficientMeasure n)).prod
      (stdGaussian (EuclideanSpace ℝ (Fin n)))] = _
  rw [bridge_covariance_prod_sum _ _ (V q) (V r) (Z q) (Z r)
    (hV.hasGaussianLaw_eval q).memLp_two (hV.hasGaussianLaw_eval r).memLp_two
    (hZ.hasGaussianLaw_eval q).memLp_two (hZ.hasGaussianLaw_eval r).memLp_two]
  rw [bridge_covariance_prod_sum _ _ (X q) (X r) (Y q) (Y r)
    (hX.hasGaussianLaw_eval q).memLp_two (hX.hasGaussianLaw_eval r).memLp_two
    (hY.hasGaussianLaw_eval q).memLp_two (hY.hasGaussianLaw_eval r).memLp_two]
  rw [bridgeMiddleFirstProcess_covariance, bridgeMiddleSecondProcess_covariance,
    bridgeMiddleEndpointProcess_covariance n s t hs ht]

theorem bridgeSplitCenteredPath_bridge_covariance (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (q r : Icc (0 : ℝ) (s+t) × Fin n) :
    cov[fun p => bridgeSplitCenteredPath n s t hs ht p q.1 q.2,
      fun p => bridgeSplitCenteredPath n s t hs ht p r.1 r.2; bridgeMiddleMeasure n] =
      (min (q.1:ℝ) (r.1:ℝ)-(q.1:ℝ)*(r.1:ℝ)/(s+t)) * (if q.2=r.2 then 1 else 0) := by
  rw [bridgeSplitCenteredPath_covariance_components n s t hs ht q r]
  simp_rw [bridgeMiddleFirstTime_value, bridgeMiddleSecondTime_value]
  dsimp [bridgeMiddleFirstFactor, bridgeMiddleSecondFactor, bridgeMiddleLinearCoefficient]
  have h := bridge_middle_covariance_algebra s t (q.1:ℝ) (r.1:ℝ) hs ht
  linear_combination (if q.2=r.2 then (1:ℝ) else 0) * h

end AffineFKProof
