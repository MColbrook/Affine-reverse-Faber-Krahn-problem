module

public import AffineFK.OrdinaryFisherConvolutionComponents
public import AffineFK.OrdinaryWeakScoreSobolevConverse

/-!
# Ordinary Sobolev Fisher-energy contraction under convolution

The original square root belongs to the actual unweighted H1 graph. The
arbitrary first law has no density or moment hypothesis. The genuine
conditional ordinary score on the actual convolution density is fed to
the independently proved weak-score Sobolev converse; that theorem
constructs the output square root and bounds its actual gradient energy.
No output H1 membership or information inequality is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem ordinaryFisher_convolution_H1_energy
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x)) [IsProbabilityMeasure (densityMeasure n ρ)] :
    (ν.prod (densityMeasure n ρ)).map (fun p => p.1 + p.2) =
      densityMeasure n (ordinaryFisherConvolutionDensity n ν ρ) ∧
    ∃ w : unweightedSobolevGraph n,
      (unweightedValue n w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        (fun z => Real.sqrt (ordinaryFisherConvolutionDensity n ν ρ z)) ∧
      (4 * ∫ z, ‖unweightedGradient n w z‖ ^ 2) ≤ 4 * ∫ x, ‖unweightedGradient n v x‖ ^ 2 := by
  have hlaw := ordinaryFisherConvolutionDensity_law n ν ρ hρ
  let : IsProbabilityMeasure (densityMeasure n (ordinaryFisherConvolutionDensity n ν ρ)) := by
    rw [← hlaw]
    infer_instance
  obtain ⟨r, _hrmeas, hr, hbound, hweak⟩ :=
    ordinaryFisher_convolution_actual_density_weak_score n ν ρ hρ hρ0 v hv
  obtain ⟨w, hw, henergy⟩ := ordinaryWeakScore_sqrt_sobolev_ae n
    (ordinaryFisherConvolutionDensity n ν ρ)
    (ordinaryFisherConvolutionDensityENNReal_measurable n ν ρ hρ).ennreal_toReal
    (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) r hr
    (fun i φ => (hweak i φ).2.2)
  exact ⟨hlaw, w, hw, henergy.trans hbound⟩

end AffineFKProof
