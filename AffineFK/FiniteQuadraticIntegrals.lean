module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Squared finite sums with genuine integrability premises

This is a finite expansion of Bochner integrals. Every product is proved
integrable before the finite sums pass through the integral. It uses
Mathlib's finite-sum linearity theorem and commutative ring identities.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory

theorem integral_sq_fintype_sum
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (f : ι → X → ℝ)
    (hpair : ∀ a b, Integrable (fun x => f a x * f b x) μ) :
    Integrable (fun x => (∑ a, f a x) ^ 2) μ ∧
      (∫ x, (∑ a, f a x) ^ 2 ∂μ) = ∑ a, ∑ b, ∫ x, f a x * f b x ∂μ := by
  classical
  have hrow (a : ι) : Integrable (fun x => ∑ b, f a x * f b x) μ :=
    integrable_finsetSum _ fun b _ => hpair a b
  have hall : Integrable (fun x => ∑ a, ∑ b, f a x * f b x) μ :=
    integrable_finsetSum _ fun a _ => hrow a
  have heq : (fun x => (∑ a, f a x) ^ 2) = (fun x => ∑ a, ∑ b, f a x * f b x) := by
    funext x
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.mul_sum _ _ _
  rw [heq]
  refine ⟨hall, ?_⟩
  rw [integral_finsetSum _ fun a _ => hrow a]
  apply Finset.sum_congr rfl
  intro a _
  exact integral_finsetSum _ fun b _ => hpair a b

end AffineFKProof
