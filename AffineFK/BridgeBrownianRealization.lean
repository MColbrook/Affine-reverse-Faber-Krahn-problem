module

public import AffineFK.BridgeBrownianCovariance
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# A finite-horizon Brownian realization from the actual bridge

On the genuine product of the coefficient probability and an independent
standard Gaussian endpoint, define `B(t) = beta(t) + t Z` for `0 ≤ t ≤ 1`.
All paths are continuous, and subtraction of the terminal linear path is
literally the original coefficient series, for every product sample.
No infinite-time Brownian assertion is made by this construction.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

abbrev BridgeBrownianSample (n : ℕ) :=
  (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)

def bridgeBrownianProductMeasure (n : ℕ) : Measure (BridgeBrownianSample n) :=
  (bridgeCoefficientMeasure n).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))

instance bridgeBrownianProductMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (bridgeBrownianProductMeasure n) := by
  unfold bridgeBrownianProductMeasure
  infer_instance

def bridgeBrownianPath (n : ℕ) (p : BridgeBrownianSample n) :
    C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) where
  toFun t := bridgeContinuousSeries n p.1 t + (t : ℝ) • p.2
  continuous_toFun := (bridgeContinuousSeries n p.1).continuous.add
    (continuous_subtype_val.smul continuous_const)

theorem bridgeBrownianPath_measurable (n : ℕ) : Measurable (bridgeBrownianPath n) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun p : BridgeBrownianSample n =>
    bridgeContinuousSeries n p.1 t + (t : ℝ) • p.2)
  exact (((ContinuousMap.measurable_eval t).comp (bridgeContinuousSeries_measurable n)).comp
    measurable_fst).add (measurable_snd.const_smul (t : ℝ))

theorem bridgeBrownianPath_zero (n : ℕ) (p : BridgeBrownianSample n) :
    bridgeBrownianPath n p ⟨0, by norm_num⟩ = 0 := by
  change bridgeContinuousSeries n p.1 ⟨0, by norm_num⟩ + (0 : ℝ) • p.2 = 0
  rw [bridgeContinuousSeries_zero]
  simp

theorem bridgeBrownianPath_one (n : ℕ) (p : BridgeBrownianSample n) :
    bridgeBrownianPath n p ⟨1, by norm_num⟩ = p.2 := by
  change bridgeContinuousSeries n p.1 ⟨1, by norm_num⟩ + (1 : ℝ) • p.2 = p.2
  rw [bridgeContinuousSeries_one]
  simp

theorem bridgeBrownianPath_sub_terminal (n : ℕ) (p : BridgeBrownianSample n)
    (t : Icc (0 : ℝ) 1) :
    bridgeBrownianPath n p t - (t : ℝ) • bridgeBrownianPath n p ⟨1, by norm_num⟩ =
      bridgeContinuousSeries n p.1 t := by
  rw [bridgeBrownianPath_one]
  exact add_sub_cancel_right _ _

def bridgeBrownianBridgePath (n : ℕ) (p : BridgeBrownianSample n) :
    C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) where
  toFun t := bridgeBrownianPath n p t - (t : ℝ) • bridgeBrownianPath n p ⟨1, by norm_num⟩
  continuous_toFun := (bridgeBrownianPath n p).continuous.sub
    (continuous_subtype_val.smul continuous_const)

theorem bridgeBrownianBridgePath_eq (n : ℕ) (p : BridgeBrownianSample n) :
    bridgeBrownianBridgePath n p = bridgeContinuousSeries n p.1 := by
  apply ContinuousMap.ext
  intro t
  exact bridgeBrownianPath_sub_terminal n p t

theorem bridgeBrownianBridgePath_hasLaw (n : ℕ) :
    HasLaw (bridgeBrownianBridgePath n) (bridgeSeriesLaw n) (bridgeBrownianProductMeasure n) := by
  have hseries : HasLaw (bridgeContinuousSeries n) (bridgeSeriesLaw n) (bridgeCoefficientMeasure n) :=
    ⟨(bridgeContinuousSeries_measurable n).aemeasurable, rfl⟩
  have heq : bridgeBrownianBridgePath n = fun p : BridgeBrownianSample n =>
      bridgeContinuousSeries n p.1 := funext (bridgeBrownianBridgePath_eq n)
  rw [heq]
  change HasLaw (fun p : BridgeBrownianSample n => bridgeContinuousSeries n p.1)
    (bridgeSeriesLaw n) ((bridgeCoefficientMeasure n).prod
      (stdGaussian (EuclideanSpace ℝ (Fin n))))
  exact
    hseries.comp (measurePreserving_fst (μ := bridgeCoefficientMeasure n)
      (ν := stdGaussian (EuclideanSpace ℝ (Fin n)))).hasLaw

theorem bridgeBrownianPath_endpoint_hasLaw (n : ℕ) :
    HasLaw (fun p : BridgeBrownianSample n => bridgeBrownianPath n p ⟨1, by norm_num⟩)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (bridgeBrownianProductMeasure n) := by
  simp_rw [bridgeBrownianPath_one]
  change HasLaw Prod.snd (stdGaussian (EuclideanSpace ℝ (Fin n)))
    ((bridgeCoefficientMeasure n).prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
  exact
    (measurePreserving_snd (μ := bridgeCoefficientMeasure n)
      (ν := stdGaussian (EuclideanSpace ℝ (Fin n)))).hasLaw

theorem bridgeBrownianBridgePath_indep_endpoint (n : ℕ) :
    IndepFun (bridgeBrownianBridgePath n)
      (fun p : BridgeBrownianSample n => bridgeBrownianPath n p ⟨1, by norm_num⟩)
      (bridgeBrownianProductMeasure n) := by
  have heq : bridgeBrownianBridgePath n = fun p : BridgeBrownianSample n =>
      bridgeContinuousSeries n p.1 := funext (bridgeBrownianBridgePath_eq n)
  rw [heq]
  simp_rw [bridgeBrownianPath_one]
  exact indepFun_prod (μ := bridgeCoefficientMeasure n)
    (ν := stdGaussian (EuclideanSpace ℝ (Fin n))) (bridgeContinuousSeries_measurable n)
      (measurable_id : Measurable (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)))

def bridgeBrownianLaw (n : ℕ) : Measure C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) :=
  (bridgeBrownianProductMeasure n).map (bridgeBrownianPath n)

instance bridgeBrownianLaw_probability (n : ℕ) : IsProbabilityMeasure (bridgeBrownianLaw n) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (bridgeBrownianPath_measurable n).aemeasurable).mpr inferInstance

end AffineFKProof
