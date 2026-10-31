module

public import AffineFK.EuclideanGaussianCovariance
public import AffineFK.GaussianKLCalculus

/-!
# The fourth norm moment of the actual standard Gaussian

The finite coordinate expansion uses the previously proved Hermite
covariance and actual coordinate second moments, not an assumed Wick
formula. Mathlib's genuine Gaussian Lp theorem supplies L4 membership.
The Gaussian, finite-product and integral developments retain their
Mathlib and earlier-source attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem stdGaussian_coordinate_squared_pair_moment (n : ℕ) (i j : Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2 * (x j) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x : EuclideanSpace ℝ (Fin n), (x i) ^ 2 * (x j) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = if i = j then 3 else 1 := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hG : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 γ :=
    IsGaussian.memLp_id _ 2 (by norm_num)
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2) γ :=
    (hG.eval_piLp i).integrable_sq
  have hj : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x j) ^ 2) γ :=
    (hG.eval_piLp j).integrable_sq
  have hcov := stdGaussian_quadratic_pair_covariance n i i j j
  have hC : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      ((x i) ^ 2 - 1) * ((x j) ^ 2 - 1)) γ := by
    simpa only [pow_two, ite_true, γ] using hcov.1
  have hCeq : (∫ x : EuclideanSpace ℝ (Fin n), ((x i) ^ 2 - 1) * ((x j) ^ 2 - 1) ∂γ) =
      if i = j then 2 else 0 := by
    by_cases hij : i = j <;> convert hcov.2 using 1 <;> norm_num [pow_two, hij, γ]
  have heq : (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2 * (x j) ^ 2) =
      (fun x => (((x i) ^ 2 - 1) * ((x j) ^ 2 - 1) + (x i) ^ 2) + (x j) ^ 2 - 1) := by
    funext x
    ring
  rw [heq]
  refine ⟨((hC.add hi).add hj).sub (integrable_const 1), ?_⟩
  rw [integral_sub
    (f := fun x : EuclideanSpace ℝ (Fin n) =>
      (((x i) ^ 2 - 1) * ((x j) ^ 2 - 1) + (x i) ^ 2) + (x j) ^ 2)
    (g := fun _ => (1 : ℝ)) ((hC.add hi).add hj) (integrable_const 1),
    integral_add (f := fun x : EuclideanSpace ℝ (Fin n) =>
      ((x i) ^ 2 - 1) * ((x j) ^ 2 - 1) + (x i) ^ 2)
      (g := fun x => (x j) ^ 2) (hC.add hi) hj,
    integral_add (f := fun x : EuclideanSpace ℝ (Fin n) => ((x i) ^ 2 - 1) * ((x j) ^ 2 - 1))
      (g := fun x => (x i) ^ 2) hC hi, hCeq]
  simp only [γ, gaussian_entropy_coordinate_second_moment, integral_const, probReal_univ, one_smul]
  split_ifs <;> norm_num

theorem stdGaussian_norm_fourth_moment (n : ℕ) :
    MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 4
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 4)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 4
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = (n : ℝ) * (n + 2) := by
  classical
  have hG : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 4
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := IsGaussian.memLp_id _ 4 (by norm_num)
  refine ⟨hG, hG.integrable_norm_pow (by norm_num), ?_⟩
  have hpoint (x : EuclideanSpace ℝ (Fin n)) : ‖x‖ ^ 4 =
      ∑ i : Fin n, ∑ j : Fin n, (x i) ^ 2 * (x j) ^ 2 := by
    rw [show ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 by ring, EuclideanSpace.real_norm_sq_eq, pow_two,
      Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (stdGaussian_coordinate_squared_pair_moment n i j).1))]
  simp_rw [integral_finsetSum _ (fun j _ => (stdGaussian_coordinate_squared_pair_moment n _ j).1),
    (stdGaussian_coordinate_squared_pair_moment n _ _).2]
  have hsum (i : Fin n) : (∑ j : Fin n, if i = j then (3 : ℝ) else 1) = n + 2 := by
    have heq (j : Fin n) : (if i = j then (3 : ℝ) else 1) = (if i = j then 2 else 0) + 1 := by
      split_ifs <;> norm_num
    simp_rw [heq]
    simp [Finset.sum_add_distrib, add_comm]
  simp_rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end AffineFKProof
