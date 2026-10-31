module

public import AffineFK.FisherInformation

/-!
# Independence of the density representative

Both numerical Sobolev informations depend only on the almost-everywhere
class of the density. The argument uses the injective graph value map,
actual withDensity congruence, and equality of genuine Lebesgue energies.
It does not differentiate an arbitrary Radon--Nikodym representative.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal Classical

theorem sqrtDensitySobolev_congr_ae (n : ℕ)
    (ρ η : EuclideanSpace ℝ (Fin n) → ℝ) (heq : ρ =ᵐ[volume] η) :
    sqrtDensitySobolev n ρ ↔ sqrtDensitySobolev n η := by
  have hs := heq.fun_comp Real.sqrt
  exact ⟨fun ⟨v, hv⟩ => ⟨v, hv.trans hs⟩, fun ⟨v, hv⟩ => ⟨v, hv.trans hs.symm⟩⟩

theorem fisherInformation_congr_ae (n : ℕ)
    (ρ η : EuclideanSpace ℝ (Fin n) → ℝ) (heq : ρ =ᵐ[volume] η) :
    fisherInformation n ρ = fisherInformation n η := by
  by_cases hρ : sqrtDensitySobolev n ρ
  · obtain ⟨v, hv⟩ := hρ
    rw [fisherInformation_eq_graph n ρ v hv,
      fisherInformation_eq_graph n η v (hv.trans (heq.fun_comp Real.sqrt))]
  · have hη : ¬sqrtDensitySobolev n η :=
      fun h => hρ ((sqrtDensitySobolev_congr_ae n ρ η heq).mpr h)
    simp only [fisherInformation, dite_eq_right hρ, dite_eq_right hη]

theorem relativeFisherInformation_congr_ae (n : ℕ)
    (ρ η : EuclideanSpace ℝ (Fin n) → ℝ) (heq : ρ =ᵐ[volume] η) :
    relativeFisherInformation n ρ = relativeFisherInformation n η := by
  have hμ : densityMeasure n ρ = densityMeasure n η :=
    withDensity_congr_ae (heq.fun_comp ENNReal.ofReal)
  have hdom : (sqrtDensitySobolev n ρ ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ)) ↔
      sqrtDensitySobolev n η ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n η) := by
    rw [hμ, sqrtDensitySobolev_congr_ae n ρ η heq]
  by_cases hρ : sqrtDensitySobolev n ρ ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ)
  · obtain ⟨⟨v, hv⟩, hsecond⟩ := hρ
    have hsecond' : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n η) :=
      hμ ▸ hsecond
    rw [relativeFisherInformation_eq_graph n ρ v hv hsecond,
      relativeFisherInformation_eq_graph n η v (hv.trans (heq.fun_comp Real.sqrt)) hsecond']
    congr 1
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  · have hη := fun h => hρ (hdom.mpr h)
    simp only [relativeFisherInformation, dite_eq_right hρ, dite_eq_right hη]

end AffineFKProof
