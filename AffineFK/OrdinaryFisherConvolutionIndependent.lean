module

public import AffineFK.OrdinaryFisherConvolutionH1
public import Mathlib.Probability.Independence.Basic

/-!
# The ordinary Sobolev convolution inequality for actual independent vectors

Independence identifies the actual joint law with the product law already
handled by the analytic proof. The original probability space is arbitrary.
Only Y has a density or a Sobolev-domain premise; X is merely measurable.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem ordinaryFisher_independent_convolution_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X Y : Ω → EuclideanSpace ℝ (Fin n))
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hind : IndepFun X Y μ) :
    ((μ.map X).prod (μ.map Y)).map (fun p => p.1 + p.2) =
      μ.map (fun ω => X ω + Y ω) := by
  rw [← hind.map_prod_eq_prod_map_map hX hY,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hX.prodMk hY)]
  rfl

theorem ordinaryFisher_independent_convolution_H1_energy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X Y : Ω → EuclideanSpace ℝ (Fin n))
    (hX : AEMeasurable X μ) (hind : IndepFun X Y μ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) (hY : HasLaw Y (densityMeasure n ρ) μ)
    (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x)) :
    μ.map (fun ω => X ω + Y ω) =
      densityMeasure n (ordinaryFisherConvolutionDensity n (μ.map X) ρ) ∧
    ∃ w : unweightedSobolevGraph n,
      (unweightedValue n w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        (fun z => Real.sqrt (ordinaryFisherConvolutionDensity n (μ.map X) ρ z)) ∧
      (4 * ∫ z, ‖unweightedGradient n w z‖ ^ 2) ≤ 4 * ∫ x, ‖unweightedGradient n v x‖ ^ 2 := by
  let : IsProbabilityMeasure (μ.map X) := (hasLaw_map hX).isProbabilityMeasure_iff.mp inferInstance
  let : IsProbabilityMeasure (densityMeasure n ρ) := hY.isProbabilityMeasure_iff.mp inferInstance
  have h := ordinaryFisher_convolution_H1_energy n (μ.map X) ρ hρ hρ0 v hv
  have hlaw := ordinaryFisher_independent_convolution_law μ n X Y hX hY.aemeasurable hind
  rw [hY.map_eq] at hlaw
  rwa [hlaw] at h

end AffineFKProof
