module

public import AffineFK.BridgeScaledBrownianLaw
public import AffineFK.BridgeKilledEndpointDensity

/-!
# Actual Brownian paths from an arbitrary start and their killed endpoints

The law is the measurable image `x + sqrt(T) B(t/T)` on `[0,T]`.
Killing restricts this actual path probability to the open all-time event,
including both endpoints. Its endpoint measure is the genuine affine
image of the time-one killed endpoint measure on the pullback domain.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridgeUnitTime_surjective (T : ℝ) (hT : 0 < T) :
    Function.Surjective (bridgeUnitTime T hT) := by
  intro u
  refine ⟨⟨T * (u : ℝ), mul_nonneg hT.le u.property.1,
    mul_le_of_le_one_right hT.le u.property.2⟩, ?_⟩
  apply Subtype.ext
  change T * (u : ℝ) / T = (u : ℝ)
  field_simp

theorem bridgeUnitTime_terminal (T : ℝ) (hT : 0 < T) :
    bridgeUnitTime T hT ⟨T, hT.le, le_rfl⟩ = (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1) := by
  apply Subtype.ext
  exact div_self hT.ne'

def bridgeStartedBrownianPath (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) (f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n))) :
    C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) where
  toFun t := x + bridgeScaledBrownianPath n T hT f t
  continuous_toFun := continuous_const.add (bridgeScaledBrownianPath n T hT f).continuous

theorem bridgeStartedBrownianPath_measurable (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) : Measurable (bridgeStartedBrownianPath n T hT x) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact measurable_const.add
    ((ContinuousMap.measurable_eval t).comp (bridgeScaledBrownianPath_measurable n T hT))

theorem bridgeStartedBrownianPath_terminal (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) (f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n))) :
    bridgeStartedBrownianPath n T hT x f ⟨T, hT.le, le_rfl⟩ =
      x + Real.sqrt T • f ⟨1, by norm_num⟩ := by
  change x + Real.sqrt T • f (bridgeUnitTime T hT ⟨T, hT.le, le_rfl⟩) = _
  rw [bridgeUnitTime_terminal]

def bridgeStartedBrownianLaw (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) : Measure C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) :=
  (bridgeBrownianLaw n).map (bridgeStartedBrownianPath n T hT x)

instance bridgeStartedBrownianLaw_probability (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) : IsProbabilityMeasure (bridgeStartedBrownianLaw n T hT x) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (bridgeStartedBrownianPath_measurable n T hT x).aemeasurable).mpr inferInstance

def bridgeFiniteSurvivalSet (n : ℕ) (T : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Set C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) := {f | ∀ t, f t ∈ Ω}

theorem bridgeFiniteSurvivalSet_isOpen (n : ℕ) (T : ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    IsOpen (bridgeFiniteSurvivalSet n T Ω) := by
  simpa only [bridgeFiniteSurvivalSet, Set.MapsTo, Set.mem_univ, forall_true_left] using
    ContinuousMap.isOpen_setOfPred_mapsTo (X := Icc (0 : ℝ) T) isCompact_univ hΩ

def bridgeStartPullbackDomain (n : ℕ) (T : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | x + Real.sqrt T • z ∈ Ω}

theorem bridgeStartPullbackDomain_isOpen (n : ℕ) (T : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    IsOpen (bridgeStartPullbackDomain n T x Ω) := hΩ.preimage (by fun_prop)

theorem bridgeStartedBrownianPath_survival_iff (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n))) :
    bridgeStartedBrownianPath n T hT x f ∈ bridgeFiniteSurvivalSet n T Ω ↔
      f ∈ bridgeBrownianSurvivalSet n (bridgeStartPullbackDomain n T x Ω) := by
  change (∀ t : Icc (0 : ℝ) T, x + Real.sqrt T • f (bridgeUnitTime T hT t) ∈ Ω) ↔
    ∀ u : Icc (0 : ℝ) 1, x + Real.sqrt T • f u ∈ Ω
  constructor
  · intro hf u
    obtain ⟨t, ht⟩ := bridgeUnitTime_surjective T hT u
    simpa only [ht] using hf t
  · intro hf t
    exact hf (bridgeUnitTime T hT t)

def bridgeStartedKilledEndpointMeasure (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  ((bridgeStartedBrownianLaw n T hT x).restrict (bridgeFiniteSurvivalSet n T Ω)).map
    (fun f => f ⟨T, hT.le, le_rfl⟩)

theorem bridgeStartedKilledEndpointMeasure_eq_map_unit (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeStartedKilledEndpointMeasure n T hT x Ω =
      (bridgeKilledEndpointMeasure n (bridgeStartPullbackDomain n T x Ω)).map
        (fun z => x + Real.sqrt T • z) := by
  have he : Measurable (fun z : EuclideanSpace ℝ (Fin n) => x + Real.sqrt T • z) := by fun_prop
  apply Measure.ext
  intro S hS
  rw [bridgeStartedKilledEndpointMeasure, Measure.map_apply (ContinuousMap.measurable_eval _) hS,
    Measure.restrict_apply (hS.preimage (ContinuousMap.measurable_eval _)),
    bridgeStartedBrownianLaw, Measure.map_apply (bridgeStartedBrownianPath_measurable n T hT x)
      ((hS.preimage (ContinuousMap.measurable_eval _)).inter
        (bridgeFiniteSurvivalSet_isOpen n T Ω hΩ).measurableSet),
    Measure.map_apply he hS, bridgeKilledEndpointMeasure,
    Measure.map_apply (ContinuousMap.measurable_eval _) (hS.preimage he),
    Measure.restrict_apply ((hS.preimage he).preimage (ContinuousMap.measurable_eval _))]
  congr 1
  ext f
  change (bridgeStartedBrownianPath n T hT x f ⟨T, hT.le, le_rfl⟩ ∈ S ∧
    bridgeStartedBrownianPath n T hT x f ∈ bridgeFiniteSurvivalSet n T Ω) ↔
      x + Real.sqrt T • f ⟨1, by norm_num⟩ ∈ S ∧
        f ∈ bridgeBrownianSurvivalSet n (bridgeStartPullbackDomain n T x Ω)
  rw [bridgeStartedBrownianPath_terminal, bridgeStartedBrownianPath_survival_iff]

end AffineFKProof
