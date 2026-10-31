module

public import AffineFK.FisherInformation
public import AffineFK.OrdinaryFisherConvolutionIndependent

/-!
# The actual extended ordinary Fisher inequality under convolution

The functional is the manuscript's actual square-root H1 energy, with
infinity outside its domain. The finite case uses the genuinely proved
output H1 square root and its gradient-energy contraction. The infinite
case is an actual extended-order inequality. The first summand remains
an arbitrary probability law and has no density or moment hypothesis.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Distributions RealInnerProductSpace

theorem fisherInformation_convolution (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) [IsProbabilityMeasure (densityMeasure n ρ)] :
    fisherInformation n (ordinaryFisherConvolutionDensity n ν ρ) ≤ fisherInformation n ρ := by
  by_cases htop : fisherInformation n ρ = ∞
  · rw [htop]
    exact le_top
  · obtain ⟨v, hv⟩ := (fisherInformation_ne_top_iff n ρ).mp htop
    obtain ⟨_hlaw, w, hw, henergy⟩ := ordinaryFisher_convolution_H1_energy n ν ρ hρ hρ0 v hv
    rw [fisherInformation_eq_graph n _ w hw, fisherInformation_eq_graph n ρ v hv]
    exact ENNReal.ofReal_le_ofReal henergy

theorem fisherInformation_convolution_with_law (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) [IsProbabilityMeasure (densityMeasure n ρ)] :
    (ν.prod (densityMeasure n ρ)).map (fun p => p.1 + p.2) =
      densityMeasure n (ordinaryFisherConvolutionDensity n ν ρ) ∧
    fisherInformation n (ordinaryFisherConvolutionDensity n ν ρ) ≤ fisherInformation n ρ := by
  exact ⟨ordinaryFisherConvolutionDensity_law n ν ρ hρ,
    fisherInformation_convolution n ν ρ hρ hρ0⟩

theorem fisherInformation_independent_convolution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X Y : Ω → EuclideanSpace ℝ (Fin n))
    (hX : AEMeasurable X μ) (hind : IndepFun X Y μ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) (hY : HasLaw Y (densityMeasure n ρ) μ) :
    μ.map (fun ω => X ω + Y ω) =
      densityMeasure n (ordinaryFisherConvolutionDensity n (μ.map X) ρ) ∧
    fisherInformation n (ordinaryFisherConvolutionDensity n (μ.map X) ρ) ≤ fisherInformation n ρ := by
  let : IsProbabilityMeasure (μ.map X) := (hasLaw_map hX).isProbabilityMeasure_iff.mp inferInstance
  let : IsProbabilityMeasure (densityMeasure n ρ) := hY.isProbabilityMeasure_iff.mp inferInstance
  have h := fisherInformation_convolution_with_law n (μ.map X) ρ hρ hρ0
  have hlaw := ordinaryFisher_independent_convolution_law μ n X Y hX hY.aemeasurable hind
  rw [hY.map_eq] at hlaw
  rwa [hlaw] at h

end AffineFKProof
