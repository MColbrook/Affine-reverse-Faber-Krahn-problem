module

public import AffineFK.OrdinaryFisherConvolutionSobolev
public import AffineFK.OrdinaryFisherConvolutionDensity
public import AffineFK.VectorTestUniqueness

/-!
# The convolution weak score on the actual output density

The scalar component equations below follow from the already constructed
single output field and genuine one-coordinate vector tests. The output
density is the real version of the extended convolution kernel, so it is
an actual probability density even when the first law is singular.
These are weak-score/energy conclusions, before the independent Sobolev
converse needed to identify the output ordinary Fisher information.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem ordinaryFisher_weak_vector_components (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      Integrable (fun x => ⟪r x, F x⟫) μ ∧ Integrable (vectorDivergence n F) μ ∧
      (∫ x, ⟪r x, F x⟫ ∂μ) = -(∫ x, vectorDivergence n F x ∂μ)) :
    ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      Integrable (fun x => r x i * φ x) μ ∧ Integrable (partialTest n i φ) μ ∧
      (∫ x, r x i * φ x ∂μ) = -(∫ x, partialTest n i φ x ∂μ) := by
  intro i φ
  have h := hweak (singleComponentTest n i φ)
  have hd : vectorDivergence n (singleComponentTest n i φ) =
      (partialTest n i φ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    funext fun x => vectorDivergence_singleComponentTest n i φ x
  simpa only [singleComponentTest_inner_at, hd] using h

theorem ordinaryFisher_convolution_actual_density_weak_score
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x)) [IsProbabilityMeasure (densityMeasure n ρ)] :
    ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable r ∧
      MemLp r 2 (densityMeasure n (ordinaryFisherConvolutionDensity n ν ρ)) ∧
      (∫ x, ‖r x‖ ^ 2 ∂densityMeasure n (ordinaryFisherConvolutionDensity n ν ρ)) ≤
        4 * ∫ x, ‖unweightedGradient n v x‖ ^ 2 ∧
      ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
        Integrable (fun x => r x i * φ x) (densityMeasure n (ordinaryFisherConvolutionDensity n ν ρ)) ∧
        Integrable (partialTest n i φ) (densityMeasure n (ordinaryFisherConvolutionDensity n ν ρ)) ∧
        (∫ x, r x i * φ x ∂densityMeasure n (ordinaryFisherConvolutionDensity n ν ρ)) =
          -(∫ x, partialTest n i φ x ∂densityMeasure n (ordinaryFisherConvolutionDensity n ν ρ)) := by
  obtain ⟨r, hr, hrLp, _hrep, hbound, hweak⟩ :=
    ordinaryFisher_convolution_sqrt_density n ν ρ hρ0 v hv
  have hlaw := ordinaryFisherConvolutionDensity_law n ν ρ hρ
  rw [hlaw] at hrLp hbound hweak
  exact ⟨r, hr, hrLp, hbound, ordinaryFisher_weak_vector_components n _ r hweak⟩

end AffineFKProof
