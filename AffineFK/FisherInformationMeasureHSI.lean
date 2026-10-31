module

public import AffineFK.FisherInformationMeasure
public import AffineFK.FisherInformationHSI

/-! The HSI inequality for the actual probability law, with finite relative
Sobolev information as its sole information-domain assumption. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ENNReal

theorem second_order_entropy_stein_information_measure (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hI : relativeFisherMeasure n ν ≠ ∞)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν)
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) =
        ∫ x, vectorHessianContraction n T F x ∂ν) :
    klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
    klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal (Real.sqrt 2 * Real.sqrt (∫ x, ‖T x‖ ^ 2 ∂ν) *
        Real.sqrt (relativeFisherMeasure n ν).toReal) := by
  classical
  have hac : ν ≪ volume := by
    by_contra h
    exact hI (by simp only [relativeFisherMeasure, ite_eq_right h])
  let ρ := canonicalLebesgueDensity n ν
  have hlaw : densityMeasure n ρ = ν := canonicalLebesgueDensity_reconstruct n ν hac
  let : IsProbabilityMeasure (densityMeasure n ρ) := by rw [hlaw]; infer_instance
  have hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x :=
    Filter.Eventually.of_forall (canonicalLebesgueDensity_nonneg n ν)
  have hIeq : relativeFisherMeasure n ν = relativeFisherInformation n ρ := by
    simp only [relativeFisherMeasure, ite_eq_left hac, ρ]
  have hI' : relativeFisherInformation n ρ ≠ ∞ := hIeq ▸ hI
  have hT' : MemLp T 2 (densityMeasure n ρ) := by rw [hlaw]; exact hT
  have hidentity' : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂densityMeasure n ρ) =
        ∫ x, vectorHessianContraction n T F x ∂densityMeasure n ρ := by
    simpa only [hlaw] using hidentity
  have h := second_order_entropy_stein_information n ρ hρ0 hI' T hT' hidentity'
  simpa only [hlaw, ← hIeq] using h

end AffineFKProof
