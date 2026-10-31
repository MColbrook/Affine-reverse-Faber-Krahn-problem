module

public import AffineFK.FiniteSobolevDensityScore

/-!
# The extended numerical Fisher informations of a Lebesgue density

The ordinary information is four times the actual square-root H1 gradient
energy, and is infinity outside that domain. The relative information is
the manuscript's square-root Sobolev expression on the finite-second-moment
domain, and is infinity otherwise. The injective H1 value map proves that
the chosen graph representative is unique. These definitions contain no
assumed score equation or information inequality.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal Classical

/-- Membership of the actual square root of a density in unweighted H1. -/
def sqrtDensitySobolev (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ v : unweightedSobolevGraph n,
    (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x)

/-- Four times the square-root H1 gradient energy; infinity off its domain. -/
def fisherInformation (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ≥0∞ :=
  if h : sqrtDensitySobolev n ρ then
    ENNReal.ofReal (4 * ∫ x, ‖unweightedGradient n h.choose x‖ ^ 2)
  else ∞

/-- The Gaussian-relative square-root Sobolev energy on its finite-moment domain. -/
def relativeFisherInformation (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ≥0∞ :=
  if h : sqrtDensitySobolev n ρ ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ) then
    ENNReal.ofReal (∫ x,
      ‖(2 : ℝ) • unweightedGradient n h.1.choose x + Real.sqrt (ρ x) • x‖ ^ 2)
  else ∞

theorem fisherInformation_eq_graph (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x)) :
    fisherInformation n ρ = ENNReal.ofReal (4 * ∫ x, ‖unweightedGradient n v x‖ ^ 2) := by
  have h : sqrtDensitySobolev n ρ := ⟨v, hv⟩
  have heq : h.choose = v := finiteSobolev_square_root_graph_unique n ρ _ v h.choose_spec hv
  simp only [fisherInformation, dite_eq_left h, heq]

theorem fisherInformation_ne_top_iff (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) :
    fisherInformation n ρ ≠ ∞ ↔ sqrtDensitySobolev n ρ := by
  classical
  constructor
  · intro hf
    by_contra h
    exact hf (by simp only [fisherInformation, dite_eq_right h])
  · intro h
    simp only [fisherInformation, dite_eq_left h]
    exact ENNReal.ofReal_ne_top

theorem relativeFisherInformation_eq_graph (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x))
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ)) :
    relativeFisherInformation n ρ = ENNReal.ofReal (∫ x,
      ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2) := by
  have h : sqrtDensitySobolev n ρ ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ) := ⟨⟨v, hv⟩, hsecond⟩
  have heq : h.1.choose = v := finiteSobolev_square_root_graph_unique n ρ _ v h.1.choose_spec hv
  simp only [relativeFisherInformation, dite_eq_left h, heq]

theorem relativeFisherInformation_ne_top_iff (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) :
    relativeFisherInformation n ρ ≠ ∞ ↔ sqrtDensitySobolev n ρ ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ) := by
  classical
  by_cases h : sqrtDensitySobolev n ρ ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ) <;>
    simp [relativeFisherInformation, h]

end AffineFKProof
