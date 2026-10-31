module

public import AffineFK.BridgeBrownianMoments

/-!
# Actual path-law means, covariances and bridge subtraction

The assertions are on the continuous-path probability law constructed from
the actual independent endpoint. They are restricted to the unit interval.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

def bridgeRemoveEndpoint (n : ℕ) (f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n))) :
    C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) where
  toFun t := f t - (t : ℝ) • f ⟨1, by norm_num⟩
  continuous_toFun := f.continuous.sub (continuous_subtype_val.smul continuous_const)

theorem bridgeRemoveEndpoint_measurable (n : ℕ) : Measurable (bridgeRemoveEndpoint n) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (ContinuousMap.measurable_eval t).sub
    ((ContinuousMap.measurable_eval (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1)).const_smul (t : ℝ))

theorem bridgeBrownianLaw_remove_endpoint_hasLaw (n : ℕ) :
    HasLaw (bridgeRemoveEndpoint n) (bridgeSeriesLaw n) (bridgeBrownianLaw n) := by
  refine ⟨(bridgeRemoveEndpoint_measurable n).aemeasurable, ?_⟩
  rw [bridgeBrownianLaw, Measure.map_map (bridgeRemoveEndpoint_measurable n)
    (bridgeBrownianPath_measurable n)]
  change (bridgeBrownianProductMeasure n).map (bridgeBrownianBridgePath n) = bridgeSeriesLaw n
  exact (bridgeBrownianBridgePath_hasLaw n).map_eq

theorem bridgeBrownianLaw_endpoint_hasLaw (n : ℕ) :
    HasLaw (fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f ⟨1, by norm_num⟩)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (bridgeBrownianLaw n) := by
  refine ⟨(ContinuousMap.measurable_eval _).aemeasurable, ?_⟩
  rw [bridgeBrownianLaw, Measure.map_map (ContinuousMap.measurable_eval _)
    (bridgeBrownianPath_measurable n)]
  exact (bridgeBrownianPath_endpoint_hasLaw n).map_eq

theorem bridgeBrownianLaw_coordinate_mean (n : ℕ) (t : Icc (0 : ℝ) 1) (i : Fin n) :
    (∫ f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)), f t i ∂bridgeBrownianLaw n) = 0 := by
  have hm : Measurable (fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f t i) := by
    simpa only [Function.comp_def, coordinateFunctional_apply] using
      (coordinateFunctional n i).measurable.comp (ContinuousMap.measurable_eval t)
  rw [bridgeBrownianLaw, integral_map (bridgeBrownianPath_measurable n).aemeasurable
    hm.aestronglyMeasurable]
  exact bridgeBrownianPath_coordinate_mean n t i

theorem bridgeBrownianLaw_coordinate_covariance (n : ℕ) (s t : Icc (0 : ℝ) 1) (i l : Fin n) :
    cov[fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f s i,
      fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f t l; bridgeBrownianLaw n] =
        min (s : ℝ) t * (if i = l then 1 else 0) := by
  have hm (q : Icc (0 : ℝ) 1) (k : Fin n) :
      Measurable (fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f q k) := by
    simpa only [Function.comp_def, coordinateFunctional_apply] using
      (coordinateFunctional n k).measurable.comp (ContinuousMap.measurable_eval q)
  rw [bridgeBrownianLaw, covariance_map (hm s i).aestronglyMeasurable (hm t l).aestronglyMeasurable
    (bridgeBrownianPath_measurable n).aemeasurable]
  exact bridgeBrownianPath_coordinate_covariance n s t i l

theorem bridgeBrownianLaw_remove_endpoint_indep (n : ℕ) :
    IndepFun (bridgeRemoveEndpoint n)
      (fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f ⟨1, by norm_num⟩)
      (bridgeBrownianLaw n) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (bridgeRemoveEndpoint_measurable n).aemeasurable
    (ContinuousMap.measurable_eval _).aemeasurable).mpr
  rw [(bridgeBrownianLaw_remove_endpoint_hasLaw n).map_eq,
    (bridgeBrownianLaw_endpoint_hasLaw n).map_eq]
  rw [bridgeBrownianLaw, Measure.map_map
    ((bridgeRemoveEndpoint_measurable n).prodMk (ContinuousMap.measurable_eval _))
      (bridgeBrownianPath_measurable n)]
  change (bridgeBrownianProductMeasure n).map
    (fun p : BridgeBrownianSample n => (bridgeBrownianBridgePath n p,
      bridgeBrownianPath n p ⟨1, by norm_num⟩)) = _
  rw [(bridgeBrownianBridgePath_indep_endpoint n).map_prod_eq_prod_map_map
    (bridgeBrownianBridgePath_hasLaw n).aemeasurable
    (bridgeBrownianPath_endpoint_hasLaw n).aemeasurable]
  rw [(bridgeBrownianBridgePath_hasLaw n).map_eq,
    (bridgeBrownianPath_endpoint_hasLaw n).map_eq]

end AffineFKProof
