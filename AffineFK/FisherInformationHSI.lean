module

public import AffineFK.FisherInformation
public import AffineFK.FiniteSobolevHSI

/-!
# The numerical second-order entropy--Stein--information inequality

Finite relative Fisher information is the actual extended Sobolev
definition. Its finite-domain equivalence supplies the unique square-root
H1 graph and the second moment; no extra regularity assumption is added.
The full-domain HSI proof then gives the entropy bound with the exact
sqrt(2) constant, including zero information and zero tensor energy.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ENNReal

theorem second_order_entropy_stein_information (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hI : relativeFisherInformation n ρ ≠ ∞)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 (densityMeasure n ρ))
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂densityMeasure n ρ) =
        ∫ x, vectorHessianContraction n T F x ∂densityMeasure n ρ) :
    klDiv (densityMeasure n ρ) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
    klDiv (densityMeasure n ρ) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal (Real.sqrt 2 * Real.sqrt (∫ x, ‖T x‖ ^ 2 ∂densityMeasure n ρ) *
        Real.sqrt (relativeFisherInformation n ρ).toReal) := by
  obtain ⟨⟨v, hv⟩, hsecond⟩ := (relativeFisherInformation_ne_top_iff n ρ).mp hI
  have h := finiteSobolev_second_order_HSI n ρ hρ0 v hv hsecond T hT hidentity
  have hIeq := relativeFisherInformation_eq_graph n ρ v hv hsecond
  have hInonneg : 0 ≤ ∫ x,
      ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  refine ⟨h.2.1, ?_⟩
  simpa only [hIeq, ENNReal.toReal_ofReal hInonneg] using h.2.2.2.2

end AffineFKProof
