module

public import AffineFK.BridgeBrownianScaling

/-!
# Brownian properties of the actual scaled continuous-path image law

These proofs transport the genuine scaled process to its actual measurable
image. In particular, independent increments concern full vector-valued
increments under the image probability, not only its coordinate marginals.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridge_iIndepFun_map {Ω Λ ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [MeasurableSpace E] [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Λ) (hX : Measurable X) (Y : ι → Λ → E) (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun (fun i ω => Y i (X ω)) μ) : iIndepFun Y (μ.map X) := by
  letI : IsProbabilityMeasure (μ.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr inferInstance
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hY i).aemeasurable)).mpr
  have hmap : (μ.map X).map (fun z i => Y i z) = μ.map (fun ω i => Y i (X ω)) :=
    Measure.map_map (Measurable.of_eval hY) hX
  have hsingle : (fun i => (μ.map X).map (Y i)) = fun i => μ.map (fun ω => Y i (X ω)) := by
    funext i
    exact Measure.map_map (hY i) hX
  rw [hmap, hsingle]
  exact hind.map_fun_eq_pi_map (fun i => ((hY i).comp hX).aemeasurable)

theorem bridgeScaledBrownianLaw_gaussian_process (n : ℕ) (T : ℝ) (hT : 0 < T) :
    IsGaussianProcess (fun q : Icc (0 : ℝ) T × Fin n =>
      fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => f q.1 q.2)
        (bridgeScaledBrownianLaw n T hT) := by
  constructor
  intro I
  have hG := (bridgeScaledBrownianPath_gaussian_process n T hT).hasGaussianLaw I
  let g : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) → I → ℝ := fun f q => f q.1.1 q.1.2
  have hg : Measurable g := by fun_prop
  refine ⟨hg.aemeasurable, ?_⟩
  change IsGaussian ((bridgeScaledBrownianLaw n T hT).map g)
  rw [bridgeScaledBrownianLaw, Measure.map_map hg (bridgeScaledBrownianPath_measurable n T hT)]
  exact hG.isGaussian_map

theorem bridgeScaledBrownianLaw_coordinate_mean (n : ℕ) (T : ℝ) (hT : 0 < T)
    (t : Icc (0 : ℝ) T) (i : Fin n) :
    (∫ f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)), f t i
      ∂bridgeScaledBrownianLaw n T hT) = 0 := by
  have hm : Measurable (fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => f t i) := by
    simpa only [Function.comp_def, coordinateFunctional_apply] using
      (coordinateFunctional n i).measurable.comp (ContinuousMap.measurable_eval t)
  rw [bridgeScaledBrownianLaw, integral_map (bridgeScaledBrownianPath_measurable n T hT).aemeasurable
    hm.aestronglyMeasurable]
  exact bridgeScaledBrownianPath_coordinate_mean n T hT t i

theorem bridgeScaledBrownianLaw_coordinate_covariance (n : ℕ) (T : ℝ) (hT : 0 < T)
    (s t : Icc (0 : ℝ) T) (i l : Fin n) :
    cov[fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => f s i,
      fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => f t l;
        bridgeScaledBrownianLaw n T hT] = min (s : ℝ) t * (if i = l then 1 else 0) := by
  have hm (q : Icc (0 : ℝ) T) (k : Fin n) :
      Measurable (fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => f q k) := by
    simpa only [Function.comp_def, coordinateFunctional_apply] using
      (coordinateFunctional n k).measurable.comp (ContinuousMap.measurable_eval q)
  rw [bridgeScaledBrownianLaw, covariance_map (hm s i).aestronglyMeasurable (hm t l).aestronglyMeasurable
    (bridgeScaledBrownianPath_measurable n T hT).aemeasurable]
  exact bridgeScaledBrownianPath_coordinate_covariance n T hT s t i l

set_option maxHeartbeats 600000 in
theorem bridgeScaledBrownianLaw_hasIndepIncrements (n : ℕ) (T : ℝ) (hT : 0 < T) :
    HasIndepIncrements (fun t : Icc (0 : ℝ) T =>
      fun f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) => f t)
        (bridgeScaledBrownianLaw n T hT) := by
  intro m t ht
  exact bridge_iIndepFun_map (bridgeBrownianLaw n) (bridgeScaledBrownianPath n T hT)
    (bridgeScaledBrownianPath_measurable n T hT)
    (fun (i : Fin m) (f : C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n))) =>
      f (t i.succ) - f (t i.castSucc))
    (fun i => (ContinuousMap.measurable_eval (t i.succ)).sub
      (ContinuousMap.measurable_eval (t i.castSucc)))
    (bridgeScaledBrownianPath_hasIndepIncrements n T hT m t ht)

end AffineFKProof
