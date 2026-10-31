module

public import AffineFK.FisherInformation
public import AffineFK.SobolevFisherIdentityGraph

/-!
# The numerical relative--ordinary Fisher identity

The square-root product rule and the full cutoff integration formula have
already been proved on the actual H1 graph. Thus the identity below has no
integration-by-parts premise. Finite ordinary information and the actual
second moment suffice; no mean or covariance assumption is needed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem fisherInformation_relative_ordinary_identity (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hJ : fisherInformation n ρ ≠ ∞)
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ)) :
    relativeFisherInformation n ρ ≠ ∞ ∧
    (relativeFisherInformation n ρ).toReal = (fisherInformation n ρ).toReal +
      (∫ x, ‖x‖ ^ 2 ∂densityMeasure n ρ) - 2 * n := by
  obtain ⟨v, hv⟩ := (fisherInformation_ne_top_iff n ρ).mp hJ
  have hlaw := finiteSobolev_square_density_eq n ρ hρ0 v hv
  let : IsProbabilityMeasure (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) := by
    rw [← hlaw]
    infer_instance
  have hsecond' : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      (densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) := by
    rw [← hlaw]
    exact hsecond
  have hxf := finiteSobolev_x_value_memLp_of_second_moment n v hsecond'
  have h := (sobolevFisher_graph_relative_ordinary_identity n v hxf).2
  have heq : (fun x => ‖(2 : ℝ) • unweightedGradient n v x + unweightedValue n v x • x‖ ^ 2) =ᵐ[volume]
      fun x => ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2 := by
    filter_upwards [hv] with x hx
    rw [hx]
  rw [integral_congr_ae heq, ← hlaw] at h
  refine ⟨(relativeFisherInformation_ne_top_iff n ρ).mpr ⟨⟨v, hv⟩, hsecond⟩, ?_⟩
  rw [relativeFisherInformation_eq_graph n ρ v hv hsecond,
    fisherInformation_eq_graph n ρ v hv,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg _)),
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (integral_nonneg (fun x => sq_nonneg _)))]
  exact h

theorem fisherInformation_unit_second_moment_identity (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hJ : fisherInformation n ρ ≠ ∞)
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ))
    (hmoment : (∫ x, ‖x‖ ^ 2 ∂densityMeasure n ρ) = n) :
    relativeFisherInformation n ρ ≠ ∞ ∧
    (relativeFisherInformation n ρ).toReal = (fisherInformation n ρ).toReal - n := by
  have h := fisherInformation_relative_ordinary_identity n ρ hρ0 hJ hsecond
  refine ⟨h.1, ?_⟩
  rw [hmoment] at h
  linarith [h.2]

end AffineFKProof
