module

public import AffineFK.OUGaussianEntropyBound
public import AffineFK.OUDensityEntropyInitialLimit

/-!
# The two actual OU entropy endpoints

For an absolutely continuous initial probability with finite second moment,
the actual extended-valued relative entropy contracts, is finite at every
positive time, converges to the initial entropy at zero and to zero at
infinite time. Initial entropy may be infinite. The positive-time entropy
dissipation identity is a separate assertion.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal Topology

theorem OU_entropy_endpoints (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ volume)
    (hsecond : Integrable (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ ^ 2) ν) :
    (∀ t : ℝ, 0 < t →
      klDiv (ouInitialLaw n ν t) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞) ∧
    (∀ t : ℝ, 0 ≤ t →
      klDiv (ouInitialLaw n ν t) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
        klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    Tendsto (fun t : ℝ => klDiv (ouInitialLaw n ν t)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))) (𝓝[>] 0)
      (𝓝 (klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))))) ∧
    Tendsto (fun t : ℝ => klDiv (ouInitialLaw n ν t)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by
  refine ⟨?_, fun t ht => ouInitial_entropy_contraction n ν t ht,
    ouInitial_entropy_tendsto_of_volume_ac n ν hac, ?_⟩
  · intro t ht
    simpa only [ouInitialLaw] using gaussian_mixture_entropy_finite n ν hsecond
      (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
      (ou_smoothing_scale_domain t ht).2.1
  · simpa only [ouInitialLaw] using ou_gaussian_entropy_tendsto_zero n ν hsecond

end AffineFKProof
