module

public import AffineFK.InformationSpectrum

/-!
# Uniform information-spectrum constant on actual probability laws

Log-concavity is expressed by a genuine measurable log-concave Lebesgue
density representing the same law. The constant is selected before the
dimension, body and probability law. Equivalence with a separately
defined set-based notion of log-concave measure is not asserted here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal NNReal

theorem information_spectrum_law_bound (P : ℝ) (hPtwo : 2 ≤ P)
    (n : ℕ) (hn : 0 < n) (ν : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [Measure.IsNegInvariant ν]
    (hlc : ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      Measurable f ∧ ν = densityMeasure n f ∧ LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x, x i ∂ν) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0)
    (hP : poincareConstant n ν ≤ ENNReal.ofReal P) (hI : relativeFisherMeasure n ν ≠ ∞)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D) (hD : Convex ℝ D)
    (hinterior : (interior D).Nonempty) (hsymmetric : ∀ x, -x ∈ D ↔ x ∈ D)
    (hsupp : ∀ᵐ x ∂ν, x ∈ D) :
    dirichletEigenvalue n (⟨interior D, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal (informationSpectrumConstant P * ((n : ℝ) +
        Real.sqrt ((n : ℝ) * (relativeFisherMeasure n ν).toReal))) := by
  obtain ⟨f, hf, hlaw, hlc⟩ := hlc
  subst ν
  let P' : ℝ≥0 := ⟨P, by linarith⟩
  have hP' : poincareConstant n (densityMeasure n f) ≤ (P' : ℝ≥0∞) := by
    have heq : ENNReal.ofReal P = (P' : ℝ≥0∞) := by
      change ENNReal.ofReal (P' : ℝ) = (P' : ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    rwa [heq] at hP
  exact information_spectrum_density_bound n hn f hf hlc hmean hcov P' hP' hPtwo hI
    D hcompact hD hinterior hsymmetric hsupp

theorem information_spectrum_uniform_constant (P : ℝ) (hPtwo : 2 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
      ∀ (ν : Measure (EuclideanSpace ℝ (Fin n)))
        (_hprob : IsProbabilityMeasure ν) (_heven : Measure.IsNegInvariant ν),
      (∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
        Measurable f ∧ ν = densityMeasure n f ∧ LogConcaveDensity (fun x => ENNReal.ofReal (f x))) →
      (∀ i : Fin n, (∫ x, x i ∂ν) = 0) →
      (∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0) →
      poincareConstant n ν ≤ ENNReal.ofReal P → relativeFisherMeasure n ν ≠ ∞ →
      ∀ (D : Set (EuclideanSpace ℝ (Fin n))), IsCompact D → Convex ℝ D →
        (interior D).Nonempty → (∀ x, -x ∈ D ↔ x ∈ D) → (∀ᵐ x ∂ν, x ∈ D) →
      dirichletEigenvalue n (⟨interior D, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
        ENNReal.ofReal (C * ((n : ℝ) + Real.sqrt ((n : ℝ) * (relativeFisherMeasure n ν).toReal))) := by
  refine ⟨informationSpectrumConstant P, informationSpectrumConstant_pos P hPtwo, ?_⟩
  intro n hn ν hprob heven hlc hmean hcov hP hI D hcompact hD hinterior hsymmetric hsupp
  letI := hprob
  letI := heven
  exact information_spectrum_law_bound P hPtwo n hn ν hlc hmean hcov hP hI D hcompact hD
    hinterior hsymmetric hsupp

end AffineFKProof
