module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Star.Real

/-!
# The inverse-Hessian bound under unit strong convexity

A genuine positive-semidefinite lower bound A-I supplies invertibility
and the quadratic bound for A inverse. The proof uses only the matrix
inverse identities, positivity, and the finite Cauchy--Schwarz inequality.
It applies to empty matrices as well. This is a pointwise algebraic
ingredient for Brascamp--Lieb, not an assumed Poincare inequality.

Mathlib's matrix positivity and finite-sum Cauchy--Schwarz results retain
their Apache-2.0 attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open scoped Matrix BigOperators

theorem strongConvex_matrix_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : (A - 1).PosSemidef) : A.PosDef := by
  have h := (Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).add_posSemidef hA
  have heq : (1 : Matrix ι ι ℝ) + (A - 1) = A := by abel
  simpa only [heq] using h

theorem strongConvex_inverse_quadratic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : (A - 1).PosSemidef) (v : ι → ℝ) :
    v ⬝ᵥ A⁻¹ *ᵥ v ≤ ∑ i, (v i) ^ 2 := by
  letI := (strongConvex_matrix_posDef A hA).isUnit.invertible
  let w := A⁻¹ *ᵥ v
  have hw : A *ᵥ w = v := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (Matrix.isUnit_det_of_invertible A),
      Matrix.one_mulVec]
  have hlower : w ⬝ᵥ w ≤ w ⬝ᵥ v := by
    have h := hA.dotProduct_mulVec_nonneg w
    simpa only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hw,
      sub_nonneg] using h
  have hCS : (w ⬝ᵥ v) ^ 2 ≤ (w ⬝ᵥ w) * (v ⬝ᵥ v) := by
    simpa only [dotProduct, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w v
  have hv : 0 ≤ v ⬝ᵥ v := by
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have hw0 : 0 ≤ w ⬝ᵥ w := by
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  have hp := hCS.trans (mul_le_mul_of_nonneg_right hlower hv)
  have hb : w ⬝ᵥ v ≤ v ⬝ᵥ v := by nlinarith
  calc
    v ⬝ᵥ A⁻¹ *ᵥ v = w ⬝ᵥ v := dotProduct_comm v w
    _ ≤ v ⬝ᵥ v := hb
    _ = ∑ i, (v i) ^ 2 := by simp only [dotProduct, pow_two]

end AffineFKProof
