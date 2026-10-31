module

public import AffineFK.BridgeTimeReversal
public import AffineFK.BridgeKilledKernelJoint

/-!
# Pointwise symmetry of the selected actual killed bridge kernel

Time reversal is proved for the actual constructed bridge probability.
The deterministic affine path reversal then yields symmetry of this
particular density at every pair of endpoints, including the diagonal.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

theorem bridge_endpoint_survival_reverse_iff (n : ℕ) (T : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n))) :
    (∀ u : Icc (0 : ℝ) 1, x+Real.sqrt T • f u+(u:ℝ) • (y-x) ∈ Ω) ↔
      ∀ u : Icc (0 : ℝ) 1,
        y+Real.sqrt T • bridgeReversePath n f u+(u:ℝ) • (x-y) ∈ Ω := by
  have he (u : Icc (0 : ℝ) 1) :
      y+Real.sqrt T • bridgeReversePath n f u+(u:ℝ) • (x-y) =
        x+Real.sqrt T • f (bridgeReverseUnitTime u)+(bridgeReverseUnitTime u:ℝ) • (y-x) := by
    change y+Real.sqrt T • f (bridgeReverseUnitTime u)+(u:ℝ) • (x-y) =
      x+Real.sqrt T • f (bridgeReverseUnitTime u)+(1-(u:ℝ)) • (y-x)
    module
  constructor
  · intro h u
    rw [he]
    exact h _
  · intro h u
    have h' := h (bridgeReverseUnitTime u)
    rw [he, bridgeReverseUnitTime_involutive] at h'
    exact h'

theorem bridge_endpoint_survival_probability_symmetric (n : ℕ) (T : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeSeriesLaw n {f | ∀ u : Icc (0 : ℝ) 1,
      x+Real.sqrt T • f u+(u:ℝ) • (y-x) ∈ Ω} =
    bridgeSeriesLaw n {f | ∀ u : Icc (0 : ℝ) 1,
      y+Real.sqrt T • f u+(u:ℝ) • (x-y) ∈ Ω} := by
  let A := {f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) |
    ∀ u : Icc (0 : ℝ) 1, x+Real.sqrt T • f u+(u:ℝ) • (y-x) ∈ Ω}
  let B := {f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) |
    ∀ u : Icc (0 : ℝ) 1, y+Real.sqrt T • f u+(u:ℝ) • (x-y) ∈ Ω}
  have heq : A = bridgeReversePath n ⁻¹' B := by
    ext f
    exact bridge_endpoint_survival_reverse_iff n T x y Ω f
  have hB : MeasurableSet B := bridgeEndpointBridgePath_survival_measurable n T y x Ω hΩ
  change bridgeSeriesLaw n A = bridgeSeriesLaw n B
  rw [heq, ← Measure.map_apply (bridgeReversePath_measurable n) hB,
    (bridgeSeriesLaw_reverse_hasLaw n).map_eq]

theorem bridgeFreeHeatDensity_symmetric (n : ℕ) (T : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    bridgeFreeHeatDensity n T x y = bridgeFreeHeatDensity n T y x := by
  have he : x-y = -(y-x) := by abel
  unfold bridgeFreeHeatDensity
  rw [he, smul_neg]
  congr 1
  apply Real.log_injOn_pos (standardGaussianDensity_pos n _) (standardGaussianDensity_pos n _)
  simp only [log_standardGaussianDensity, norm_neg]

theorem bridgeKilledKernel_symmetric (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x y : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeKilledKernel n T x Ω y = bridgeKilledKernel n T y Ω x := by
  rw [bridgeKilledKernel_bridge_formula n T hT x y Ω,
    bridgeKilledKernel_bridge_formula n T hT y x Ω,
    bridgeFreeHeatDensity_symmetric n T x y,
    bridge_endpoint_survival_probability_symmetric n T x y Ω hΩ]

end AffineFKProof
