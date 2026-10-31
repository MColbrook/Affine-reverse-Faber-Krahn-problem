module

public import AffineFK.BridgeFreeHeatDerivative
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lebesgue conservation for actual Gaussian translation averages

The product integrability needed for Fubini is derived from Haar
translation invariance and the probability normalization of the Gaussian.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem bridgeGaussian_translation_prod_integrable (n : ℕ) (c : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) (hi : Integrable f volume) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      f (p.1 + c • p.2)) (volume.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  have hm : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => f (p.1 + c • p.2))
      (volume.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) :=
    (hf.comp (by fun_prop)).aestronglyMeasurable
  apply (integrable_prod_iff' hm).mpr
  refine ⟨Filter.Eventually.of_forall (fun u => ?_), ?_⟩
  · exact (measurePreserving_add_right volume (c • u)).integrable_comp_of_integrable hi
  · have he (u : EuclideanSpace ℝ (Fin n)) :
        (∫ x, ‖f (x + c • u)‖ ∂volume) = ∫ x, ‖f x‖ ∂volume :=
      (measurePreserving_add_right volume (c • u)).hasLaw.integral_comp hi.norm.aestronglyMeasurable
    simp_rw [he]
    exact integrable_const _

theorem bridgeFreeHeatAverage_integrable_and_integral (n : ℕ) (t : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) (hi : Integrable f volume) :
    Integrable (bridgeFreeHeatAverage n t f) volume ∧
      (∫ x, bridgeFreeHeatAverage n t f x ∂volume) = ∫ x, f x ∂volume := by
  have hp := bridgeGaussian_translation_prod_integrable n (Real.sqrt t) f hf hi
  refine ⟨hp.integral_prod_left, ?_⟩
  unfold bridgeFreeHeatAverage
  rw [integral_integral_swap hp]
  have he (u : EuclideanSpace ℝ (Fin n)) :
      (∫ x, f (x + Real.sqrt t • u) ∂volume) = ∫ x, f x ∂volume :=
    (measurePreserving_add_right volume (Real.sqrt t • u)).hasLaw.integral_comp hi.aestronglyMeasurable
  simp_rw [he]
  simp

end AffineFKProof
