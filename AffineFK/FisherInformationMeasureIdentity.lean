module

public import AffineFK.FisherInformationMeasure
public import AffineFK.FisherInformationIdentity

/-! The numerical relative--ordinary information identity for the actual
probability law. Absolute continuity follows from finite ordinary information. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem fisherMeasure_relative_ordinary_identity (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hJ : ordinaryFisherMeasure n ν ≠ ∞)
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) ν) :
    relativeFisherMeasure n ν ≠ ∞ ∧
    (relativeFisherMeasure n ν).toReal = (ordinaryFisherMeasure n ν).toReal +
      (∫ x, ‖x‖ ^ 2 ∂ν) - 2 * n := by
  classical
  have hac : ν ≪ volume := by
    by_contra h
    exact hJ (by simp only [ordinaryFisherMeasure, ite_eq_right h])
  let ρ := canonicalLebesgueDensity n ν
  have hlaw : densityMeasure n ρ = ν := canonicalLebesgueDensity_reconstruct n ν hac
  let : IsProbabilityMeasure (densityMeasure n ρ) := by rw [hlaw]; infer_instance
  have hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x :=
    Filter.Eventually.of_forall (canonicalLebesgueDensity_nonneg n ν)
  have hJ' : fisherInformation n ρ ≠ ∞ := by
    simpa only [ordinaryFisherMeasure, ite_eq_left hac] using hJ
  have hsecond' : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ) := by
    rw [hlaw]
    exact hsecond
  have h := fisherInformation_relative_ordinary_identity n ρ hρ0 hJ' hsecond'
  simpa only [hlaw, ordinaryFisherMeasure, relativeFisherMeasure, ite_eq_left hac, ρ] using h

theorem fisherMeasure_unit_second_moment_identity (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hJ : ordinaryFisherMeasure n ν ≠ ∞)
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) ν)
    (hmoment : (∫ x, ‖x‖ ^ 2 ∂ν) = n) :
    relativeFisherMeasure n ν ≠ ∞ ∧
    (relativeFisherMeasure n ν).toReal = (ordinaryFisherMeasure n ν).toReal - n := by
  have h := fisherMeasure_relative_ordinary_identity n ν hJ hsecond
  refine ⟨h.1, ?_⟩
  rw [hmoment] at h
  linarith [h.2]

end AffineFKProof
