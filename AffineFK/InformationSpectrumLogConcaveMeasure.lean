module

public import AffineFK.LogConcaveMeasureDensity
public import AffineFK.InformationSpectrumLaw

/-!
# The information-spectrum estimate for a log-concave probability measure

This is the original set-based domain of Theorem information-spectrum.
Finite Gaussian-relative Fisher information gives absolute continuity.
Closed-ball differentiation then constructs the actual pointwise log-concave
density needed by the previously proved information-spectrum bound. The
constant depends only on the prescribed Poincaré bound and is chosen before
the dimension, probability law and supporting body.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal

theorem information_spectrum_logConcaveMeasure_bound (P : ℝ) (hPtwo : 2 ≤ P)
    (n : ℕ) (hn : 0 < n) (ν : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [Measure.IsNegInvariant ν]
    (hlc : IsLogConcaveMeasure n ν)
    (hmean : ∀ i : Fin n, (∫ x, x i ∂ν) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0)
    (hP : poincareConstant n ν ≤ ENNReal.ofReal P) (hI : relativeFisherMeasure n ν ≠ ∞)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D) (hD : Convex ℝ D)
    (hinterior : (interior D).Nonempty) (hsymmetric : ∀ x, -x ∈ D ↔ x ∈ D)
    (hsupp : ∀ᵐ x ∂ν, x ∈ D) :
    dirichletEigenvalue n (⟨interior D, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal (informationSpectrumConstant P * ((n : ℝ) +
        Real.sqrt ((n : ℝ) * (relativeFisherMeasure n ν).toReal))) := by
  obtain ⟨ρ, hρ, _hρ0, hlaw, hρlc, _hAE⟩ :=
    finite_relativeFisher_logConcaveMeasure_exists_density n ν hlc hI
  exact information_spectrum_law_bound P hPtwo n hn ν ⟨ρ, hρ, hlaw, hρlc⟩
    hmean hcov hP hI D hcompact hD hinterior hsymmetric hsupp

theorem information_spectrum_logConcaveMeasure_uniform_constant (P : ℝ) (hPtwo : 2 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
      ∀ (ν : Measure (EuclideanSpace ℝ (Fin n)))
        (_hprob : IsProbabilityMeasure ν) (_heven : Measure.IsNegInvariant ν),
      IsLogConcaveMeasure n ν →
      (∀ i : Fin n, (∫ x, x i ∂ν) = 0) →
      (∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0) →
      poincareConstant n ν ≤ ENNReal.ofReal P → relativeFisherMeasure n ν ≠ ∞ →
      ∀ (D : Set (EuclideanSpace ℝ (Fin n))), IsCompact D → Convex ℝ D →
        (interior D).Nonempty → (∀ x, -x ∈ D ↔ x ∈ D) → (∀ᵐ x ∂ν, x ∈ D) →
      dirichletEigenvalue n (⟨interior D, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
        ENNReal.ofReal (C * ((n : ℝ) + Real.sqrt ((n : ℝ) * (relativeFisherMeasure n ν).toReal))) := by
  refine ⟨informationSpectrumConstant P, informationSpectrumConstant_pos P hPtwo, ?_⟩
  intro n hn ν hprob heven hlc hmean hcov hP hI D hcompact hD hinterior hsymmetric hsupp
  let := hprob
  let := heven
  exact information_spectrum_logConcaveMeasure_bound P hPtwo n hn ν hlc hmean hcov hP hI
    D hcompact hD hinterior hsymmetric hsupp

end AffineFKProof
