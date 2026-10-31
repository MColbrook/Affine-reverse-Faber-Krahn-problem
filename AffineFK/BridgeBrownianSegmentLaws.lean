module

public import AffineFK.BridgeBrownianSegments
public import AffineFK.BridgeGaussianPathImage

/-!
# Actual Brownian laws of the past and future increment segments

Both laws are identified from the genuine jointly Gaussian law and its
proved means and covariances. In particular the consistency and the
stationarity of the increment-path law are conclusions, not premises.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

theorem bridgeBrownian_past_hasLaw (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    HasLaw (bridgePastPath n s t ht.le) (bridgeScaledBrownianLaw n s hs)
      (bridgeScaledBrownianLaw n (s+t) (add_pos hs ht)) := by
  let μ := bridgeScaledBrownianLaw n (s+t) (add_pos hs ht)
  have hB := bridgeScaledBrownianLaw_gaussian_process n (s+t) (add_pos hs ht)
  refine ⟨(bridgePastPath_measurable n s t ht.le).aemeasurable, ?_⟩
  apply bridge_gaussian_continuous_image_law_ext n μ (bridgePastPath n s t ht.le)
    (bridgePastPath_measurable n s t ht.le) (bridgeScaledBrownianLaw n s hs)
    (hB.comp_right (fun q : Icc (0 : ℝ) s × Fin n =>
      (bridgePastTime s t ht.le q.1, q.2)))
    (bridgeScaledBrownianLaw_gaussian_process n s hs)
  · intro r i
    exact (bridgeScaledBrownianLaw_coordinate_mean n _ _ _ _).trans
      (bridgeScaledBrownianLaw_coordinate_mean n s hs r i).symm
  · intro r u i j
    exact (bridgeScaledBrownianLaw_coordinate_covariance n _ _ _ _ _ _).trans
      (bridgeScaledBrownianLaw_coordinate_covariance n s hs r u i j).symm

theorem bridgeBrownian_future_hasLaw (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    HasLaw (bridgeFutureIncrementPath n s t hs.le ht.le) (bridgeScaledBrownianLaw n t ht)
      (bridgeScaledBrownianLaw n (s+t) (add_pos hs ht)) := by
  classical
  let μ := bridgeScaledBrownianLaw n (s+t) (add_pos hs ht)
  let B := fun q : Icc (0 : ℝ) (s+t) × Fin n =>
    fun f : C(Icc (0 : ℝ) (s+t), EuclideanSpace ℝ (Fin n)) => f q.1 q.2
  have hB : IsGaussianProcess B μ := bridgeScaledBrownianLaw_gaussian_process n _ _
  have hG : IsGaussianProcess (fun q : Icc (0 : ℝ) t × Fin n =>
      fun f => bridgeFutureIncrementPath n s t hs.le ht.le f q.1 q.2) μ := by
    apply hB.of_isGaussianProcess
    intro q
    let p := (bridgeFutureTime s t hs.le q.1, q.2)
    let r := (bridgeSplitTime s t hs.le ht.le, q.2)
    refine ⟨{p,r}, ContinuousLinearMap.proj ⟨p, by simp⟩ -
      ContinuousLinearMap.proj ⟨r, by simp⟩, ?_⟩
    intro f
    rfl
  refine ⟨(bridgeFutureIncrementPath_measurable n s t hs.le ht.le).aemeasurable, ?_⟩
  apply bridge_gaussian_continuous_image_law_ext n μ
    (bridgeFutureIncrementPath n s t hs.le ht.le)
    (bridgeFutureIncrementPath_measurable n s t hs.le ht.le)
    (bridgeScaledBrownianLaw n t ht) hG (bridgeScaledBrownianLaw_gaussian_process n t ht)
  · intro r i
    change (∫ f, B (bridgeFutureTime s t hs.le r, i) f -
      B (bridgeSplitTime s t hs.le ht.le, i) f ∂μ) = _
    rw [integral_sub ((hB.hasGaussianLaw_eval _).memLp_two.integrable (by norm_num))
      ((hB.hasGaussianLaw_eval _).memLp_two.integrable (by norm_num))]
    dsimp [B, μ]
    rw [bridgeScaledBrownianLaw_coordinate_mean, bridgeScaledBrownianLaw_coordinate_mean,
      bridgeScaledBrownianLaw_coordinate_mean, sub_self]
  · intro r u i j
    change cov[fun f => B (bridgeFutureTime s t hs.le r, i) f -
      B (bridgeSplitTime s t hs.le ht.le, i) f,
      fun f => B (bridgeFutureTime s t hs.le u, j) f -
        B (bridgeSplitTime s t hs.le ht.le, j) f; μ] = _
    rw [covariance_fun_sub_fun_sub
      (hB.hasGaussianLaw_eval _).memLp_two (hB.hasGaussianLaw_eval _).memLp_two
      (hB.hasGaussianLaw_eval _).memLp_two (hB.hasGaussianLaw_eval _).memLp_two]
    dsimp [B, μ]
    simp_rw [bridgeScaledBrownianLaw_coordinate_covariance]
    change min (s+(r:ℝ)) (s+(u:ℝ)) * (if i=j then 1 else 0) -
      min (s+(r:ℝ)) s * (if i=j then 1 else 0) -
      min s (s+(u:ℝ)) * (if i=j then 1 else 0) +
      min s s * (if i=j then 1 else 0) = min (r:ℝ) u * (if i=j then 1 else 0)
    rw [min_add_add_left, min_eq_right (le_add_of_nonneg_right r.2.1),
      min_eq_left (le_add_of_nonneg_right u.2.1), min_self]
    ring

end AffineFKProof
