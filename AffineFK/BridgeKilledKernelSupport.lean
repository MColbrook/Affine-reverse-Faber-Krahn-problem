module

public import AffineFK.BridgeAffineSurvivalProbability

/-!
# Pointwise endpoint support of the actual killed bridge density

The coefficient construction has zero bridge endpoints for every sample.
Whole closed-interval survival therefore forces both prescribed endpoints
to lie in the open killing domain, with no almost-everywhere ambiguity.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

theorem bridgeEndpointBridgePath_coefficient_zero (n : ℕ) (T : ℝ)
    (x z : EuclideanSpace ℝ (Fin n))
    (ω : ∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n)) :
    bridgeEndpointBridgePath n T x z (bridgeContinuousSeries n ω) ⟨0,by norm_num⟩ = x := by
  change x+Real.sqrt T • bridgeContinuousSeries n ω ⟨0,by norm_num⟩+(0:ℝ) • (z-x) = x
  rw [bridgeContinuousSeries_zero]
  simp

theorem bridgeEndpointBridgePath_coefficient_one (n : ℕ) (T : ℝ)
    (x z : EuclideanSpace ℝ (Fin n))
    (ω : ∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n)) :
    bridgeEndpointBridgePath n T x z (bridgeContinuousSeries n ω) ⟨1,by norm_num⟩ = z := by
  change x+Real.sqrt T • bridgeContinuousSeries n ω ⟨1,by norm_num⟩+(1:ℝ) • (z-x) = z
  rw [bridgeContinuousSeries_one,smul_zero,one_smul]
  abel

theorem bridgeAffineSurvivalProbability_zero_of_start (n : ℕ) (T : ℝ)
    (x z : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (hx : x ∉ Ω) : bridgeAffineSurvivalProbability n T x Ω z = 0 := by
  rw [← bridge_coefficient_affine_survival_probability n T x z Ω hΩ]
  have he : {ω : ∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n) |
      ∀ u : Icc (0 : ℝ) 1, bridgeEndpointBridgePath n T x z (bridgeContinuousSeries n ω) u ∈ Ω} = ∅ := by
    ext ω
    change (∀ u : Icc (0 : ℝ) 1, bridgeEndpointBridgePath n T x z (bridgeContinuousSeries n ω) u ∈ Ω) ↔ False
    constructor
    · intro h
      exact hx (by simpa only [bridgeEndpointBridgePath_coefficient_zero] using h ⟨0,by norm_num⟩)
    · exact False.elim
  rw [he,measure_empty]

theorem bridgeAffineSurvivalProbability_zero_of_end (n : ℕ) (T : ℝ)
    (x z : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (hz : z ∉ Ω) : bridgeAffineSurvivalProbability n T x Ω z = 0 := by
  rw [← bridge_coefficient_affine_survival_probability n T x z Ω hΩ]
  have he : {ω : ∀ j : ℕ, Fin (2^j) → EuclideanSpace ℝ (Fin n) |
      ∀ u : Icc (0 : ℝ) 1, bridgeEndpointBridgePath n T x z (bridgeContinuousSeries n ω) u ∈ Ω} = ∅ := by
    ext ω
    change (∀ u : Icc (0 : ℝ) 1, bridgeEndpointBridgePath n T x z (bridgeContinuousSeries n ω) u ∈ Ω) ↔ False
    constructor
    · intro h
      exact hz (by simpa only [bridgeEndpointBridgePath_coefficient_one] using h ⟨1,by norm_num⟩)
    · exact False.elim
  rw [he,measure_empty]

theorem bridgeKilledKernel_zero_of_start (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x z : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (hx : x ∉ Ω) : bridgeKilledKernel n T x Ω z = 0 := by
  rw [bridgeKilledKernel_bridge_formula n T hT x z Ω]
  change ENNReal.ofReal (bridgeFreeHeatDensity n T x z) * bridgeAffineSurvivalProbability n T x Ω z = 0
  rw [bridgeAffineSurvivalProbability_zero_of_start n T x z Ω hΩ hx,mul_zero]

theorem bridgeKilledKernel_zero_of_end (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x z : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (hz : z ∉ Ω) : bridgeKilledKernel n T x Ω z = 0 := by
  rw [bridgeKilledKernel_bridge_formula n T hT x z Ω]
  change ENNReal.ofReal (bridgeFreeHeatDensity n T x z) * bridgeAffineSurvivalProbability n T x Ω z = 0
  rw [bridgeAffineSurvivalProbability_zero_of_end n T x z Ω hΩ hz,mul_zero]

end AffineFKProof
