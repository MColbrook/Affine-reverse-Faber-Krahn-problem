module

public import AffineFK.BridgeMiddleSurvivalProbability

/-!
# Genuine product-probability factorization of affine bridge survival

The middle variable is an actual independent Gaussian vector. The two
coefficient-array events form an actual rectangle at each fixed middle
point. Tonelli and the proved whole-path law supply the factorization.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Probability that the actual continuous centered unit bridge, scaled
to duration T and affinely interpolated from x to z, stays in Ω at every
time of the closed interval, including both endpoints. -/
def bridgeAffineSurvivalProbability (n : ℕ) (T : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  bridgeSeriesLaw n {f | ∀ u : Icc (0 : ℝ) 1, bridgeEndpointBridgePath n T x z f u ∈ Ω}

theorem bridgeAffineSurvivalProbability_joint_measurable (n : ℕ) (T : ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      bridgeAffineSurvivalProbability n T p.1 Ω p.2) := by
  let A : Set ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
      C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n))) :=
    {p | ∀ u : Icc (0 : ℝ) 1, bridgeEndpointBridgePath n T p.1.1 p.1.2 p.2 u ∈ Ω}
  have hA : MeasurableSet A := (bridgeFiniteSurvivalSet_isOpen n 1 Ω hΩ).measurableSet.preimage
    (bridgeEndpointBridgePath_joint_measurable n T)
  exact measurable_measure_prodMk_left (ν := bridgeSeriesLaw n) hA

theorem bridge_coefficient_affine_survival_probability (n : ℕ) (T : ℝ)
    (x z : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeCoefficientMeasure n {ω | ∀ u : Icc (0 : ℝ) 1,
      bridgeEndpointBridgePath n T x z (bridgeContinuousSeries n ω) u ∈ Ω} =
      bridgeAffineSurvivalProbability n T x Ω z := by
  unfold bridgeAffineSurvivalProbability bridgeSeriesLaw
  exact (Measure.map_apply (bridgeContinuousSeries_measurable n)
    (bridgeEndpointBridgePath_survival_measurable n T x z Ω hΩ)).symm

theorem bridgeAffineSurvivalProbability_middle_factorization (n : ℕ) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (x z : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeAffineSurvivalProbability n (s+t) x Ω z =
      ∫⁻ w : EuclideanSpace ℝ (Fin n),
        bridgeAffineSurvivalProbability n s x Ω (bridgeSplitMiddlePoint n s t x z w) *
        bridgeAffineSurvivalProbability n t (bridgeSplitMiddlePoint n s t x z w) Ω z
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  change bridgeSeriesLaw n {f | ∀ u : Icc (0 : ℝ) 1,
    bridgeEndpointBridgePath n (s+t) x z f u ∈ Ω} = _
  rw [bridge_full_survival_probability_eq_middle n s t hs ht x z Ω hΩ,
    bridgeMiddleMeasure,
    Measure.prod_apply_symm (bridgeMiddleSurvivalEvent_measurable n s t hs ht x z Ω hΩ)]
  apply lintegral_congr
  intro w
  have he : (fun q : (∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n)) ×
        (∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n)) => (q,w)) ⁻¹'
      bridgeMiddleSurvivalEvent n s t x z Ω =
      {ω | ∀ u : Icc (0 : ℝ) 1,
        bridgeEndpointBridgePath n s x (bridgeSplitMiddlePoint n s t x z w)
          (bridgeContinuousSeries n ω) u ∈ Ω} ×ˢ
      {ω | ∀ u : Icc (0 : ℝ) 1,
        bridgeEndpointBridgePath n t (bridgeSplitMiddlePoint n s t x z w) z
          (bridgeContinuousSeries n ω) u ∈ Ω} := rfl
  rw [he, Measure.prod_prod,
    bridge_coefficient_affine_survival_probability n s _ _ Ω hΩ,
    bridge_coefficient_affine_survival_probability n t _ _ Ω hΩ]

end AffineFKProof
