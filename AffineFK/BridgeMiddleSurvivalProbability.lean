module

public import AffineFK.BridgeMiddleSurvival

/-!
# Actual probability transport for affine bridge survival

The proved whole-path split law transports the full closed-interval
survival event to the explicit two-short-bridge product event. No desired
probability identity or conditional-distribution premise is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

/-- Whole closed-interval survival of the affine endpoint interpolation
plus the given centered continuous path. -/
def bridgeAffineSurvivalSet (n : ℕ) (T : ℝ) (x z : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Set C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) :=
  {f | ∀ r, bridgeAffineCenteredPath n T x z f r ∈ Ω}

theorem bridgeAffineSurvivalSet_measurable (n : ℕ) (T : ℝ)
    (x z : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    MeasurableSet (bridgeAffineSurvivalSet n T x z Ω) :=
  (bridgeFiniteSurvivalSet_isOpen n T Ω hΩ).measurableSet.preimage
    (bridgeAffineCenteredPath_measurable n T x z)

theorem bridgeScaledBridgeLaw_affine_survival (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x z : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeScaledBridgeLaw n T hT (bridgeAffineSurvivalSet n T x z Ω) =
      bridgeSeriesLaw n {f | ∀ u : Icc (0 : ℝ) 1,
        bridgeEndpointBridgePath n T x z f u ∈ Ω} := by
  rw [bridgeScaledBridgeLaw, Measure.map_apply (bridgeScaledBrownianPath_measurable n T hT)
    (bridgeAffineSurvivalSet_measurable n T x z Ω hΩ)]
  congr 1
  ext f
  change (∀ r : Icc (0 : ℝ) T,
    bridgeEndpointBridgePath n T x z f (bridgeUnitTime T hT r) ∈ Ω) ↔ _
  constructor
  · intro h u
    obtain ⟨r,hr⟩ := bridgeUnitTime_surjective T hT u
    simpa only [hr] using h r
  · intro h r
    exact h _

/-- The actual independent two-coefficient-bridge survival event with its
common Gaussian middle point, including that point in both intervals. -/
def bridgeMiddleSurvivalEvent (n : ℕ) (s t : ℝ) (x z : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : Set (BridgeMiddleSample n) :=
  {p | (∀ u : Icc (0 : ℝ) 1,
      bridgeEndpointBridgePath n s x (bridgeSplitMiddlePoint n s t x z p.2)
        (bridgeContinuousSeries n p.1.1) u ∈ Ω) ∧
    (∀ u : Icc (0 : ℝ) 1,
      bridgeEndpointBridgePath n t (bridgeSplitMiddlePoint n s t x z p.2) z
        (bridgeContinuousSeries n p.1.2) u ∈ Ω)}

theorem bridgeMiddleSurvivalEvent_measurable (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x z : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    MeasurableSet (bridgeMiddleSurvivalEvent n s t x z Ω) := by
  have he : bridgeMiddleSurvivalEvent n s t x z Ω =
      bridgeSplitCenteredPath n s t hs ht ⁻¹' bridgeAffineSurvivalSet n (s+t) x z Ω := by
    ext p
    exact (bridgeMiddleAffinePath_survival_iff n s t hs ht x z Ω p).symm
  rw [he]
  exact (bridgeAffineSurvivalSet_measurable n (s+t) x z Ω hΩ).preimage
    (bridgeSplitCenteredPath_measurable n s t hs ht)

theorem bridge_full_survival_probability_eq_middle (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x z : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeSeriesLaw n {f | ∀ u : Icc (0 : ℝ) 1,
      bridgeEndpointBridgePath n (s+t) x z f u ∈ Ω} =
      bridgeMiddleMeasure n (bridgeMiddleSurvivalEvent n s t x z Ω) := by
  rw [← bridgeScaledBridgeLaw_affine_survival n (s+t) (add_pos hs ht) x z Ω hΩ,
    ← (bridgeSplitCenteredPath_hasLaw n s t hs ht).map_eq,
    Measure.map_apply (bridgeSplitCenteredPath_measurable n s t hs ht)
      (bridgeAffineSurvivalSet_measurable n (s+t) x z Ω hΩ)]
  congr 1
  ext p
  exact bridgeMiddleAffinePath_survival_iff n s t hs ht x z Ω p

end AffineFKProof
