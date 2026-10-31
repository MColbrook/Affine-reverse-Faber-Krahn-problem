module

public import AffineFK.EuclideanGaussianCovariance
public import AffineFK.FiniteQuadraticIntegrals

/-!
# The exact Gaussian quadratic contraction of a third-order tensor

All coefficients are arbitrary real tensor entries; no permutation
symmetry is assumed. The covariance of the actual Gaussian coordinate
products supplies the two terms in the fourth-moment formula.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

def gaussianHermiteContraction (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => ∑ j : Fin n, ∑ k : Fin n,
    A (i, j, k) * (x j * x k - if j = k then 1 else 0)

theorem tensor_quadratic_covariance_sum (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n × Fin n × Fin n)) (i : Fin n) :
    (∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
      (A (i, a.1, a.2) * A (i, b.1, b.2)) *
        ((if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0) +
          (if a.1 = b.2 then 1 else 0) * (if a.2 = b.1 then 1 else 0))) =
      ∑ j : Fin n, ∑ k : Fin n, (A (i, j, k) ^ 2 + A (i, j, k) * A (i, k, j)) := by
  classical
  simp [Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib, mul_ite, ite_mul, pow_two]

theorem gaussianHermiteContraction_component_moment (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n × Fin n × Fin n)) (i : Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (∑ j : Fin n, ∑ k : Fin n, A (i, j, k) * (x j * x k - if j = k then 1 else 0)) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x : EuclideanSpace ℝ (Fin n),
      (∑ j : Fin n, ∑ k : Fin n, A (i, j, k) * (x j * x k - if j = k then 1 else 0)) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∑ j : Fin n, ∑ k : Fin n, (A (i, j, k) ^ 2 + A (i, j, k) * A (i, k, j)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let f : (Fin n × Fin n) → EuclideanSpace ℝ (Fin n) → ℝ := fun a x =>
    A (i, a.1, a.2) * (x a.1 * x a.2 - if a.1 = a.2 then 1 else 0)
  have hpair (a b : Fin n × Fin n) : Integrable (fun x => f a x * f b x) γ := by
    convert ((stdGaussian_quadratic_pair_covariance n a.1 a.2 b.1 b.2).1.const_mul
      (A (i, a.1, a.2) * A (i, b.1, b.2))) using 1
    funext x
    dsimp [f]
    ring
  have h := integral_sq_fintype_sum γ f hpair
  have hvalue (a b : Fin n × Fin n) : (∫ x, f a x * f b x ∂γ) =
      (A (i, a.1, a.2) * A (i, b.1, b.2)) *
        ((if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0) +
          (if a.1 = b.2 then 1 else 0) * (if a.2 = b.1 then 1 else 0)) := by
    calc
      _ = ∫ x : EuclideanSpace ℝ (Fin n), (A (i, a.1, a.2) * A (i, b.1, b.2)) *
          ((x a.1 * x a.2 - if a.1 = a.2 then 1 else 0) *
            (x b.1 * x b.2 - if b.1 = b.2 then 1 else 0)) ∂γ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp [f]
          ring
      _ = _ := by
        rw [integral_const_mul, (stdGaussian_quadratic_pair_covariance n a.1 a.2 b.1 b.2).2]
  refine ⟨?_, ?_⟩
  · simpa only [Fintype.sum_prod_type] using h.1
  · have heq := h.2
    simp_rw [hvalue] at heq
    calc
      _ = ∑ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
          (A (i, a.1, a.2) * A (i, b.1, b.2)) *
            ((if a.1 = b.1 then 1 else 0) * (if a.2 = b.2 then 1 else 0) +
              (if a.1 = b.2 then 1 else 0) * (if a.2 = b.1 then 1 else 0)) := by
        simpa only [Fintype.sum_prod_type] using heq
      _ = _ := tensor_quadratic_covariance_sum n A i

theorem gaussianHermiteContraction_second_moment (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n × Fin n × Fin n)) :
    Integrable (fun x => ‖gaussianHermiteContraction n A x‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ‖gaussianHermiteContraction n A x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (A (i, j, k) ^ 2 + A (i, j, k) * A (i, k, j)) := by
  have heq : (fun x => ‖gaussianHermiteContraction n A x‖ ^ 2) =
      (fun x : EuclideanSpace ℝ (Fin n) => ∑ i : Fin n,
        (∑ j : Fin n, ∑ k : Fin n, A (i, j, k) * (x j * x k - if j = k then 1 else 0)) ^ 2) := by
    funext x
    simp only [EuclideanSpace.real_norm_sq_eq, gaussianHermiteContraction, PiLp.toLp_apply]
  rw [heq]
  refine ⟨integrable_finsetSum _ fun i _ => (gaussianHermiteContraction_component_moment n A i).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (gaussianHermiteContraction_component_moment n A i).1]
  exact Finset.sum_congr rfl fun i _ => (gaussianHermiteContraction_component_moment n A i).2

end AffineFKProof
