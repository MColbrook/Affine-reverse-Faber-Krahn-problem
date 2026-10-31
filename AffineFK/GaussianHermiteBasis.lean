module

public import AffineFK.RealGaussianMoments
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Low Hermite factors in Gaussian product spaces

The factors 1, x and x²-1 are actual polynomials under gaussianReal 0 1.
Their Gram matrix follows from the already proved Gaussian moments.
Finite-product integration is Mathlib's theorem of Xavier Roblot; the
polynomial evaluation results and contributors retain their source credits.
This develops the fourth-moment calculation without assuming Wick's formula.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Polynomial

theorem gaussianReal_standard_polynomial_integrable (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x) (gaussianReal 0 1) := by
  classical
  simp_rw [Polynomial.eval_eq_sum_range]
  exact integrable_finsetSum _ fun k _ => (gaussianReal_standard_pow_integrable k).const_mul (p.coeff k)

theorem gaussianReal_standard_polynomial_integral (p : ℝ[X]) (N : ℕ) (hN : p.natDegree < N) :
    (∫ x : ℝ, p.eval x ∂gaussianReal 0 1) =
      ∑ k ∈ Finset.range N, p.coeff k * ∫ x : ℝ, x ^ k ∂gaussianReal 0 1 := by
  classical
  simp_rw [Polynomial.eval_eq_sum_range' hN]
  rw [integral_finsetSum _ fun k _ => (gaussianReal_standard_pow_integrable k).const_mul (p.coeff k)]
  simp_rw [integral_const_mul]

def realHermitePolynomial (i : Fin 3) : ℝ[X] :=
  if i = 0 then 1 else if i = 1 then X else X ^ 2 - 1

def realHermiteFactor (i : Fin 3) (x : ℝ) : ℝ := (realHermitePolynomial i).eval x

theorem realHermitePolynomial_natDegree (i : Fin 3) : (realHermitePolynomial i).natDegree ≤ 2 := by
  fin_cases i
  · norm_num [realHermitePolynomial]
  · norm_num [realHermitePolynomial]
  · change (X ^ 2 - 1 : ℝ[X]).natDegree ≤ 2
    exact (Polynomial.natDegree_sub_le _ _).trans (by norm_num)

theorem gaussianReal_hermite_product_integrable (i j : Fin 3) :
    Integrable (fun x : ℝ => realHermiteFactor i x * realHermiteFactor j x) (gaussianReal 0 1) := by
  simpa only [realHermiteFactor, Polynomial.eval_mul] using
    gaussianReal_standard_polynomial_integrable (realHermitePolynomial i * realHermitePolynomial j)

theorem gaussianReal_hermite_gram (i j : Fin 3) :
    (∫ x : ℝ, realHermiteFactor i x * realHermiteFactor j x ∂gaussianReal 0 1) =
      if i = j then (if i = 2 then 2 else 1) else 0 := by
  have hd : (realHermitePolynomial i * realHermitePolynomial j).natDegree < 5 :=
    lt_of_le_of_lt (Polynomial.natDegree_mul_le.trans
      (Nat.add_le_add (realHermitePolynomial_natDegree i) (realHermitePolynomial_natDegree j))) (by decide)
  have heq : (fun x : ℝ => realHermiteFactor i x * realHermiteFactor j x) =
      (fun x : ℝ => (realHermitePolynomial i * realHermitePolynomial j).eval x) := by
    funext x
    exact Polynomial.eval_mul.symm
  rw [heq, gaussianReal_standard_polynomial_integral _ 5 hd]
  fin_cases i <;> fin_cases j <;>
    norm_num [realHermitePolynomial, mul_sub, sub_mul, ← pow_add, ← pow_two, ← pow_succ, ← pow_succ',
      Polynomial.coeff_one,
      Polynomial.coeff_X, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Finset.sum_range_succ,
      gaussianReal_standard_second_moment, gaussianReal_standard_third_moment,
      gaussianReal_standard_fourth_moment, integral_id_gaussianReal]
  all_goals
    have hsq : ((X : ℝ[X]) ^ 2 - 1) ^ 2 = X ^ 4 - (X ^ 2 + X ^ 2) + 1 := by ring
    rw [hsq]
    norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow]

theorem productGaussian_hermite_gram (n : ℕ) (α β : Fin n → Fin 3) :
    Integrable (fun x : Fin n → ℝ => ∏ i, realHermiteFactor (α i) (x i) * realHermiteFactor (β i) (x i))
      (Measure.pi fun _ => gaussianReal 0 1) ∧
    (∫ x : Fin n → ℝ, ∏ i, realHermiteFactor (α i) (x i) * realHermiteFactor (β i) (x i)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∏ i, if α i = β i then (if α i = 2 then 2 else 1) else 0 := by
  refine ⟨Integrable.fintype_prod (fun i => gaussianReal_hermite_product_integrable (α i) (β i)), ?_⟩
  calc
    _ = ∏ i, ∫ s : ℝ, realHermiteFactor (α i) s * realHermiteFactor (β i) s
        ∂gaussianReal 0 1 :=
      integral_fintype_prod_eq_prod (fun (i : Fin n) (s : ℝ) =>
        realHermiteFactor (α i) s * realHermiteFactor (β i) s)
    _ = _ := by simp_rw [gaussianReal_hermite_gram]

end AffineFKProof
