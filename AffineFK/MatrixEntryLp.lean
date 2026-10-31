module

public import AffineFK.ConditionalMatrixHilbertSchmidt
public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Genuine matrix L2 membership from its finite entries

The operator-norm matrix is reconstructed as its finite sum of actual
matrix units. Scalar L2 membership and finite sums give actual matrix
L2 membership, without identifying the operator norm with a sum of
squares. Matrix units and Lp operations reuse Mathlib (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem matrix_memLp_two_of_entries
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ)
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j : Fin n, MemLp (fun ω => A ω i j) 2 μ) : MemLp A 2 μ := by
  classical
  have h : MemLp (fun ω => ∑ i : Fin n, ∑ j : Fin n,
      A ω i j • Matrix.single i j (1 : ℝ)) 2 μ := by
    apply memLp_finsetSum Finset.univ
    intro i _
    apply memLp_finsetSum Finset.univ
    intro j _
    simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply] using
      (ContinuousLinearMap.toSpanSingleton ℝ (Matrix.single i j (1 : ℝ))).comp_memLp' (hA i j)
  apply h.ae_eq
  exact Filter.Eventually.of_forall fun ω => by
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.sum_sum_single (A ω)

end AffineFKProof
