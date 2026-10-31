module

public import AffineFK.OrdinaryFisherConvolution
public import AffineFK.FiniteSobolevDensityScore

/-!
# Convolution from the genuine square-root-density Sobolev domain

The second law has exactly the manuscript's finite ordinary Sobolev domain:
its actual nonnegative square root is a graph value. The other law remains
an arbitrary probability measure. The resulting weak score has energy at
most four times the squared L2 norm of that actual graph gradient.

The conclusion is deliberately a weak-score statement. Membership of the
output square root in H1 is not a premise and is not asserted here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem ordinaryFisher_convolution_square_density
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (v : unweightedSobolevGraph n)
    [IsProbabilityMeasure (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))] :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧
      MemLp r 2 ((ν.prod (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))).map
        (fun p => p.1 + p.2)) ∧
      (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        r (p.1 + p.2) = condExp
          ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
            (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => q.1 + q.2))
          (ν.prod (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)))
          (fun q => ordinaryFisherGraphScore n v q.2) p) ∧
      (∫ x, ‖r x‖ ^ 2
        ∂(ν.prod (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))).map
          (fun p => p.1 + p.2)) ≤ 4 * ∫ x, ‖unweightedGradient n v x‖ ^ 2 ∧
      ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
        Integrable (fun x => ⟪r x, F x⟫)
          ((ν.prod (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))).map
            (fun p => p.1 + p.2)) ∧
        Integrable (vectorDivergence n F)
          ((ν.prod (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))).map
            (fun p => p.1 + p.2)) ∧
        (∫ x, ⟪r x, F x⟫
          ∂(ν.prod (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))).map
            (fun p => p.1 + p.2)) =
          -(∫ x, vectorDivergence n F x
            ∂(ν.prod (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))).map
              (fun p => p.1 + p.2)) := by
  have hs := ordinaryFisherGraphScore_memLp_energy n v
  obtain ⟨r, hr, hrLp, hrep, hbound, hweak⟩ := ordinaryFisher_convolution_conditional_score n ν
    (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))
    (ordinaryFisherGraphScore n v) hs.1
    (fun i φ => (ordinaryFisherGraphScore_component_identity n v i φ).2.2)
  exact ⟨r, hr, hrLp, hrep, hbound.trans hs.2, hweak⟩

theorem ordinaryFisher_convolution_sqrt_density
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x)) [IsProbabilityMeasure (densityMeasure n ρ)] :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧ MemLp r 2 ((ν.prod (densityMeasure n ρ)).map
        (fun p => p.1 + p.2)) ∧
      (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        r (p.1 + p.2) = condExp
          ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
            (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => q.1 + q.2))
          (ν.prod (densityMeasure n ρ)) (fun q => ordinaryFisherGraphScore n v q.2) p) ∧
      (∫ x, ‖r x‖ ^ 2 ∂(ν.prod (densityMeasure n ρ)).map (fun p => p.1 + p.2)) ≤
        4 * ∫ x, ‖unweightedGradient n v x‖ ^ 2 ∧
      ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
        Integrable (fun x => ⟪r x, F x⟫)
          ((ν.prod (densityMeasure n ρ)).map (fun p => p.1 + p.2)) ∧
        Integrable (vectorDivergence n F)
          ((ν.prod (densityMeasure n ρ)).map (fun p => p.1 + p.2)) ∧
        (∫ x, ⟪r x, F x⟫ ∂(ν.prod (densityMeasure n ρ)).map (fun p => p.1 + p.2)) =
          -(∫ x, vectorDivergence n F x ∂(ν.prod (densityMeasure n ρ)).map
            (fun p => p.1 + p.2)) := by
  have heq := finiteSobolev_square_density_eq n ρ hρ0 v hv
  let : IsProbabilityMeasure (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) := by
    rw [← heq]
    infer_instance
  simpa only [heq] using ordinaryFisher_convolution_square_density n ν v

end AffineFKProof
