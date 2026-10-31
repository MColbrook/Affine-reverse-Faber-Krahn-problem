module

public import AffineFK.BridgeBrownianSegments

/-!
# Genuine independence of the past and future increment paths

The proof uses the actual jointly Gaussian continuous Brownian law and
its already proved `min(s,t)` covariance. Mathlib's Gaussian-process
independence theorem (Etienne Marion) then proves independence of every
scalar coordinate jointly; the Borel path-space sigma algebra transfers
this to the two complete continuous vector paths.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

theorem bridge_continuous_euclidean_paths_indep {Ω X Y : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] [TopologicalSpace Y] [SecondCountableTopology Y]
    [LocallyCompactSpace Y] (n : ℕ) (μ : Measure Ω)
    (f : Ω → C(X, EuclideanSpace ℝ (Fin n)))
    (g : Ω → C(Y, EuclideanSpace ℝ (Fin n)))
    (h : IndepFun (fun ω (q : X × Fin n) => f ω q.1 q.2)
      (fun ω (q : Y × Fin n) => g ω q.1 q.2) μ) : IndepFun f g μ := by
  let F : ((X × Fin n) → ℝ) → X → EuclideanSpace ℝ (Fin n) := fun v t =>
    WithLp.toLp 2 (fun i => v (t,i))
  let G : ((Y × Fin n) → ℝ) → Y → EuclideanSpace ℝ (Fin n) := fun v t =>
    WithLp.toLp 2 (fun i => v (t,i))
  have hF : Measurable F := Measurable.of_eval (fun t =>
    (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
      (Measurable.of_eval (fun i => measurable_pi_apply (t,i))))
  have hG : Measurable G := Measurable.of_eval (fun t =>
    (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
      (Measurable.of_eval (fun i => measurable_pi_apply (t,i))))
  have hi := h.comp hF hG
  exact bridge_indepFun_of_comap μ f g (fun v t => v t) (fun v t => v t)
    bridge_continuousMap_measurableSpace_eq_comap_eval
    bridge_continuousMap_measurableSpace_eq_comap_eval hi

theorem bridgeBrownian_past_future_indep (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    IndepFun (bridgePastPath n s t ht.le) (bridgeFutureIncrementPath n s t hs.le ht.le)
      (bridgeScaledBrownianLaw n (s+t) (add_pos hs ht)) := by
  classical
  let μ := bridgeScaledBrownianLaw n (s+t) (add_pos hs ht)
  let B := fun q : Icc (0 : ℝ) (s+t) × Fin n =>
    fun f : C(Icc (0 : ℝ) (s+t), EuclideanSpace ℝ (Fin n)) => f q.1 q.2
  have hB : IsGaussianProcess B μ := bridgeScaledBrownianLaw_gaussian_process n _ _
  let X := fun q : Icc (0 : ℝ) s × Fin n =>
    fun f : C(Icc (0 : ℝ) (s+t), EuclideanSpace ℝ (Fin n)) =>
      f (bridgePastTime s t ht.le q.1) q.2
  let Y := fun q : Icc (0 : ℝ) t × Fin n =>
    fun f : C(Icc (0 : ℝ) (s+t), EuclideanSpace ℝ (Fin n)) =>
      f (bridgeFutureTime s t hs.le q.1) q.2 - f (bridgeSplitTime s t hs.le ht.le) q.2
  have hJ : IsGaussianProcess (Sum.elim X Y) μ := by
    apply hB.of_isGaussianProcess
    intro q
    rcases q with q | q
    · let p := (bridgePastTime s t ht.le q.1, q.2)
      refine ⟨{p}, ContinuousLinearMap.proj ⟨p, by simp⟩, ?_⟩
      intro f
      rfl
    · let p := (bridgeFutureTime s t hs.le q.1, q.2)
      let r := (bridgeSplitTime s t hs.le ht.le, q.2)
      refine ⟨{p,r}, ContinuousLinearMap.proj ⟨p, by simp⟩ -
        ContinuousLinearMap.proj ⟨r, by simp⟩, ?_⟩
      intro f
      rfl
  have hind := hJ.indepFun_of_covariance_eq_zero
    (fun q => hB.aemeasurable (bridgePastTime s t ht.le q.1, q.2))
    (fun q => (hB.aemeasurable (bridgeFutureTime s t hs.le q.1, q.2)).sub
      (hB.aemeasurable (bridgeSplitTime s t hs.le ht.le, q.2))) (fun q r => ?_)
  · exact bridge_continuous_euclidean_paths_indep n μ
      (bridgePastPath n s t ht.le) (bridgeFutureIncrementPath n s t hs.le ht.le) hind
  change cov[B (bridgePastTime s t ht.le q.1, q.2),
    fun f => B (bridgeFutureTime s t hs.le r.1, r.2) f -
      B (bridgeSplitTime s t hs.le ht.le, r.2) f; μ] = 0
  rw [covariance_fun_sub_right
    (hB.hasGaussianLaw_eval _).memLp_two
    (hB.hasGaussianLaw_eval _).memLp_two
    (hB.hasGaussianLaw_eval _).memLp_two]
  dsimp [B, μ]
  rw [bridgeScaledBrownianLaw_coordinate_covariance,
    bridgeScaledBrownianLaw_coordinate_covariance]
  change min (q.1 : ℝ) (s + r.1) * (if q.2 = r.2 then 1 else 0) -
    min (q.1 : ℝ) s * (if q.2 = r.2 then 1 else 0) = 0
  rw [min_eq_left (q.1.2.2.trans (le_add_of_nonneg_right r.1.2.1)),
    min_eq_left q.1.2.2, sub_self]

end AffineFKProof
