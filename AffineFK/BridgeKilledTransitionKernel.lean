module

public import AffineFK.BridgeKilledChapmanKolmogorov
public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# The genuine finite killed Brownian transition kernel

For each positive duration this is the actual killed endpoint measure
from every starting point. Its mass is at most one. The semigroup identity
is derived from the constructed Brownian path law and its proved split,
not assumed as an abstract kernel property.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- The actual Brownian endpoint law restricted to open-domain survival over
the whole closed time interval, including both endpoints; covariance is
`min(s,t)` and the corresponding free heat generator is `Delta/2`. -/
def bridgeKilledTransitionKernel (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun x := bridgeStartedKilledEndpointMeasure n T hT x Ω
  measurable' := Measure.measurable_of_measurable_coe _
    (fun S hS => bridge_killed_endpoint_apply_measurable n T hT Ω S hΩ hS)

theorem bridgeKilledTransitionKernel_mass_le_one (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (x : EuclideanSpace ℝ (Fin n)) : bridgeKilledTransitionKernel n T hT Ω hΩ x univ ≤ 1 := by
  change bridgeStartedKilledEndpointMeasure n T hT x Ω univ ≤ 1
  rw [bridge_killed_endpoint_apply_eq_section n T hT x Ω univ hΩ MeasurableSet.univ]
  exact (measure_mono (subset_univ _)).trans_eq (measure_univ (μ := bridgeScaledBrownianLaw n T hT))

instance bridgeKilledTransitionKernel_finite (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    IsFiniteKernel (bridgeKilledTransitionKernel n T hT Ω hΩ) :=
  ⟨⟨1, by simp, bridgeKilledTransitionKernel_mass_le_one n T hT Ω hΩ⟩⟩

theorem bridgeKilledTransitionKernel_semigroup (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeKilledTransitionKernel n (s+t) (add_pos hs ht) Ω hΩ =
      bridgeKilledTransitionKernel n t ht Ω hΩ ∘ₖ bridgeKilledTransitionKernel n s hs Ω hΩ := by
  ext x S hS
  rw [Kernel.comp_apply' _ _ _ hS]
  exact bridge_killed_chapman_kolmogorov n s t hs ht x Ω S hΩ hS

end AffineFKProof
