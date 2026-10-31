module

public import AffineFK.GaussianTensorContraction
public import AffineFK.TensorQuadraticBound

/-!
# The Gaussian tensor fourth-moment formula

This is the first display in the manuscript's Hermite-contraction step:
the exact actual Gaussian expectation and its coefficient-two bound.
The later conditional-score/Fisher-information step remains separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem stdGaussian_tensor_hermite_contraction (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n × Fin n × Fin n)) :
    MemLp (gaussianHermiteContraction n A) 2 (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ‖gaussianHermiteContraction n A x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (A (i, j, k) ^ 2 + A (i, j, k) * A (i, k, j))) ∧
    (∫ x, ‖gaussianHermiteContraction n A x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      2 * ‖A‖ ^ 2 := by
  have h := gaussianHermiteContraction_second_moment n A
  have hc : Continuous (gaussianHermiteContraction n A) := by
    unfold gaussianHermiteContraction
    fun_prop
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr h.1,
    h.2, ?_⟩
  rw [h.2]
  exact tensor_quadratic_moment_le_two_norm_sq n A

end AffineFKProof
