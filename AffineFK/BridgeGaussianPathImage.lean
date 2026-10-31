module

public import AffineFK.BridgeGaussianPathLawExt
public import Mathlib.Probability.Moments.Covariance

/-!
# Identifying an actual Gaussian continuous-path image

The hypotheses concern the constructed random continuous path itself;
the conclusion identifies its measurable image law. This is a general
transport lemma, not an assumed Brownian consistency law.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem bridge_gaussian_continuous_image_law_ext {Ω K : Type*} [MeasurableSpace Ω]
    [TopologicalSpace K] [SecondCountableTopology K] [LocallyCompactSpace K]
    (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → C(K, EuclideanSpace ℝ (Fin n))) (hF : Measurable F)
    (ν : Measure C(K, EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hμ : IsGaussianProcess (fun q : K × Fin n => fun ω => F ω q.1 q.2) μ)
    (hν : IsGaussianProcess (fun q : K × Fin n =>
      fun f : C(K, EuclideanSpace ℝ (Fin n)) => f q.1 q.2) ν)
    (hm : ∀ t i, (∫ ω, F ω t i ∂μ) = ∫ f, f t i ∂ν)
    (hc : ∀ s t i j, cov[fun ω => F ω s i, fun ω => F ω t j; μ] =
      cov[fun f => f s i, fun f => f t j; ν]) : μ.map F = ν := by
  letI : IsProbabilityMeasure (μ.map F) :=
    (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).mpr inferInstance
  have himage : IsGaussianProcess (fun q : K × Fin n =>
      fun f : C(K, EuclideanSpace ℝ (Fin n)) => f q.1 q.2) (μ.map F) := by
    constructor
    intro I
    let Y := fun f : C(K, EuclideanSpace ℝ (Fin n)) => fun q : I => f q.1.1 q.1.2
    have hY : Measurable Y := by fun_prop
    refine ⟨hY.aemeasurable, ?_⟩
    change IsGaussian ((μ.map F).map Y)
    rw [Measure.map_map hY hF]
    exact (hμ.hasGaussianLaw I).isGaussian_map
  apply bridge_gaussian_continuous_path_law_ext n (μ.map F) ν himage hν
  · intro t i
    have he : Measurable (fun f : C(K, EuclideanSpace ℝ (Fin n)) => f t i) :=
      (measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 (Fin n → ℝ)).comp
        (ContinuousMap.measurable_eval t))
    rw [integral_map hF.aemeasurable he.aestronglyMeasurable]
    exact hm t i
  · intro s t i j
    have he (r : K) (l : Fin n) :
        Measurable (fun f : C(K, EuclideanSpace ℝ (Fin n)) => f r l) :=
      (measurable_pi_apply l).comp ((WithLp.measurable_ofLp 2 (Fin n → ℝ)).comp
        (ContinuousMap.measurable_eval r))
    rw [covariance_map (he s i).aestronglyMeasurable (he t j).aestronglyMeasurable hF.aemeasurable]
    exact hc s t i j

end AffineFKProof
