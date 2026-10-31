module

public import AffineFK.FisherInformationMeasure
public import AffineFK.OrdinaryFisherConvolutionInformation

/-!
# Ordinary Fisher information of the actual sum law

The first law is an arbitrary probability measure. A finite information
assumption is unnecessary in the extended inequality: an absolutely
continuous second law has its actual canonical density, and the remaining
case has infinite input information. No moment or density is required of
the first summand.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem ordinaryFisherMeasure_convolution (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
    ordinaryFisherMeasure n ((ν.prod η).map (fun p => p.1 + p.2)) ≤
      ordinaryFisherMeasure n η := by
  classical
  by_cases hac : η ≪ volume
  · let ρ := canonicalLebesgueDensity n η
    have hρ : Measurable ρ := canonicalLebesgueDensity_measurable n η
    have hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x :=
      Filter.Eventually.of_forall (canonicalLebesgueDensity_nonneg n η)
    have hη : densityMeasure n ρ = η := canonicalLebesgueDensity_reconstruct n η hac
    let : IsProbabilityMeasure (densityMeasure n ρ) := by rw [hη]; infer_instance
    have h := fisherInformation_convolution_with_law n ν ρ hρ hρ0
    have hκ : Measurable (ordinaryFisherConvolutionDensity n ν ρ) :=
      (ordinaryFisherConvolutionDensityENNReal_measurable n ν ρ hρ).ennreal_toReal
    have hκ0 : ∀ᵐ x ∂volume, 0 ≤ ordinaryFisherConvolutionDensity n ν ρ x :=
      Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
    calc
      _ = ordinaryFisherMeasure n
          (densityMeasure n (ordinaryFisherConvolutionDensity n ν ρ)) := by
            rw [← hη, h.1]
      _ = fisherInformation n (ordinaryFisherConvolutionDensity n ν ρ) :=
        ordinaryFisherMeasure_density n _ hκ hκ0
      _ ≤ fisherInformation n ρ := h.2
      _ = ordinaryFisherMeasure n η := by
        simp only [ordinaryFisherMeasure, ite_eq_left hac, ρ]
  · have htop : ordinaryFisherMeasure n η = ∞ := by
      simp only [ordinaryFisherMeasure, ite_eq_right hac]
    rw [htop]
    exact le_top

theorem ordinaryFisherMeasure_independent_convolution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X Y : Ω → EuclideanSpace ℝ (Fin n))
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hind : IndepFun X Y μ) :
    ordinaryFisherMeasure n (μ.map (fun ω => X ω + Y ω)) ≤
      ordinaryFisherMeasure n (μ.map Y) := by
  let : IsProbabilityMeasure (μ.map X) := (hasLaw_map hX).isProbabilityMeasure_iff.mp inferInstance
  let : IsProbabilityMeasure (μ.map Y) := (hasLaw_map hY).isProbabilityMeasure_iff.mp inferInstance
  have h := ordinaryFisherMeasure_convolution n (μ.map X) (μ.map Y)
  rwa [ordinaryFisher_independent_convolution_law μ n X Y hX hY hind] at h

end AffineFKProof
