module

public import AffineFK.SteinSumLaw

/-!
# The Hilbert--Schmidt bound for the quadratic Gaussian tensor moment

The inequality uses 2ab <= a²+b² and permutation of the two contracted
indices. The tensor is arbitrary; no symmetry hypothesis is introduced.
The Hilbert--Schmidt norm identity is reused from SteinSumLaw.
-/

@[expose] public noncomputable section
namespace AffineFKProof

theorem tensor_quadratic_moment_le_two_norm_sq (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n × Fin n × Fin n)) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (A (i, j, k) ^ 2 + A (i, j, k) * A (i, k, j))) ≤ 2 * ‖A‖ ^ 2 := by
  classical
  have hswap : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, A (i, k, j) ^ 2) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, A (i, j, k) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  have hsum : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      2 * (A (i, j, k) * A (i, k, j))) ≤
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (A (i, j, k) ^ 2 + A (i, k, j) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    nlinarith [sq_nonneg (A (i, j, k) - A (i, k, j))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hswap] at hsum
  rw [third_order_tensor_norm_sq]
  simp only [Finset.sum_add_distrib]
  linarith

end AffineFKProof
