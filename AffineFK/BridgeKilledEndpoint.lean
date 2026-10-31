module

public import AffineFK.BridgeBrownianLaw

/-!
# The actual killed endpoint measure and its bridge density

Killing means restricting the genuine finite-horizon Brownian path law
to paths whose values, including both endpoints, lie in the open domain.
The terminal image of that restricted measure has the explicit Gaussian
relative density given by the independent bridge survival probability.
This is a measure-theoretic construction; a Dirichlet semigroup or
variational spectral comparison is not a premise or conclusion here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

def bridgeAffineEndpointPath (n : ℕ)
    (p : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)) :
    C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) where
  toFun t := p.1 t + (t : ℝ) • p.2
  continuous_toFun := p.1.continuous.add (continuous_subtype_val.smul continuous_const)

theorem bridgeAffineEndpointPath_continuous (n : ℕ) : Continuous (bridgeAffineEndpointPath n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p :
    (C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)) ×
      Icc (0 : ℝ) 1 => p.1.1 p.2 + (p.2 : ℝ) • p.1.2)
  exact (continuous_eval.comp
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).add
      ((continuous_subtype_val.comp continuous_snd).smul (continuous_snd.comp continuous_fst))

def bridgeBrownianSurvivalSet (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Set C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) := {f | ∀ t, f t ∈ Ω}

theorem bridgeBrownianSurvivalSet_isOpen (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) : IsOpen (bridgeBrownianSurvivalSet n Ω) := by
  simpa only [bridgeBrownianSurvivalSet, Set.MapsTo, Set.mem_univ, forall_true_left] using
    ContinuousMap.isOpen_setOfPred_mapsTo (X := Icc (0 : ℝ) 1) isCompact_univ hΩ

theorem bridgeAffineEndpointSurvival_measurableSet (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    MeasurableSet {p : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) |
      ∀ t : Icc (0 : ℝ) 1, p.1 t + (t : ℝ) • p.2 ∈ Ω} := by
  exact ((bridgeBrownianSurvivalSet_isOpen n Ω hΩ).preimage
    (bridgeAffineEndpointPath_continuous n)).measurableSet

def bridgeKilledSurvivalProbability (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  bridgeSeriesLaw n {f | ∀ t : Icc (0 : ℝ) 1, f t + (t : ℝ) • z ∈ Ω}

theorem bridgeKilledSurvivalProbability_measurable (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    Measurable (bridgeKilledSurvivalProbability n Ω) :=
  measurable_measure_prodMk_right (μ := bridgeSeriesLaw n)
    (bridgeAffineEndpointSurvival_measurableSet n Ω hΩ)

def bridgeKilledEndpointMeasure (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  ((bridgeBrownianLaw n).restrict (bridgeBrownianSurvivalSet n Ω)).map
    (fun f => f ⟨1, by norm_num⟩)

theorem bridgeBrownianLaw_bridge_endpoint_joint (n : ℕ) :
    HasLaw (fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) =>
      (bridgeRemoveEndpoint n f, f ⟨1, by norm_num⟩))
      ((bridgeSeriesLaw n).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) (bridgeBrownianLaw n) := by
  refine ⟨((bridgeRemoveEndpoint_measurable n).prodMk (ContinuousMap.measurable_eval _)).aemeasurable, ?_⟩
  rw [(bridgeBrownianLaw_remove_endpoint_indep n).map_prod_eq_prod_map_map
    (bridgeRemoveEndpoint_measurable n).aemeasurable (ContinuousMap.measurable_eval _).aemeasurable,
    (bridgeBrownianLaw_remove_endpoint_hasLaw n).map_eq,
    (bridgeBrownianLaw_endpoint_hasLaw n).map_eq]

theorem bridgeKilledEndpointMeasure_eq_gaussian_withDensity (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeKilledEndpointMeasure n Ω =
      (stdGaussian (EuclideanSpace ℝ (Fin n))).withDensity (bridgeKilledSurvivalProbability n Ω) := by
  apply Measure.ext
  intro S hS
  let H : Set (C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)) :=
    {p | ∀ t : Icc (0 : ℝ) 1, p.1 t + (t : ℝ) • p.2 ∈ Ω} ∩ Prod.snd ⁻¹' S
  have hH : MeasurableSet H :=
    (bridgeAffineEndpointSurvival_measurableSet n Ω hΩ).inter (hS.preimage measurable_snd)
  rw [bridgeKilledEndpointMeasure, Measure.map_apply (ContinuousMap.measurable_eval _) hS,
    Measure.restrict_apply (hS.preimage (ContinuousMap.measurable_eval _)),
    withDensity_apply _ hS]
  have heq : (fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f ⟨1, by norm_num⟩) ⁻¹' S ∩
      bridgeBrownianSurvivalSet n Ω =
      {f | (bridgeRemoveEndpoint n f, f ⟨1, by norm_num⟩) ∈ H} := by
    ext f
    simp only [H, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq,
      bridgeBrownianSurvivalSet, bridgeRemoveEndpoint, ContinuousMap.coe_mk]
    simp only [sub_add_cancel]
    exact and_comm
  have hmeasure : (bridgeBrownianLaw n)
      {f | (bridgeRemoveEndpoint n f, f ⟨1, by norm_num⟩) ∈ H} =
      ((bridgeSeriesLaw n).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) H :=
    (bridgeBrownianLaw_bridge_endpoint_joint n).measure_eq (p := fun p => p ∈ H) hH
  rw [heq, hmeasure, Measure.prod_apply_symm hH]
  have hsection (z : EuclideanSpace ℝ (Fin n)) :
      bridgeSeriesLaw n ((fun f => (f, z)) ⁻¹' H) =
        S.indicator (bridgeKilledSurvivalProbability n Ω) z := by
    change bridgeSeriesLaw n {f | (∀ t : Icc (0 : ℝ) 1, f t + (t : ℝ) • z ∈ Ω) ∧ z ∈ S} = _
    by_cases hz : z ∈ S
    · simp only [hz, and_true, Set.indicator_of_mem hz]
      rfl
    · simp only [hz, and_false, Set.setOf_false, measure_empty, Set.indicator_of_notMem hz]
  simp_rw [hsection]
  exact lintegral_indicator hS _

end AffineFKProof
