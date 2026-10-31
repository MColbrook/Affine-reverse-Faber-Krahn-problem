module

public import AffineFK.GaussianHermiteBasis

/-!
# Gaussian quadratic coordinate factors

The centred coordinate product x_j x_k - delta_jk is a product of the
first three real Hermite factors. Its integrability and covariance are
therefore genuine finite-product Gaussian integrals. The combinatorial
covariance calculation is kept separate from this representation.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem realHermiteFactor_zero (x : ℝ) : realHermiteFactor 0 x = 1 := by
  simp [realHermiteFactor, realHermitePolynomial]

theorem realHermiteFactor_one (x : ℝ) : realHermiteFactor 1 x = x := by
  simp [realHermiteFactor, realHermitePolynomial]

theorem realHermiteFactor_two (x : ℝ) : realHermiteFactor 2 x = x ^ 2 - 1 := by
  simp [realHermiteFactor, realHermitePolynomial]

def hermitePairDegree (n : ℕ) (j k i : Fin n) : Fin 3 :=
  if j = k then (if i = j then 2 else 0) else (if i = j ∨ i = k then 1 else 0)

theorem hermitePairDegree_swap (n : ℕ) (j k : Fin n) :
    hermitePairDegree n j k = hermitePairDegree n k j := by
  funext i
  by_cases h : j = k
  · subst k
    rfl
  · simp [hermitePairDegree, h, Ne.symm h, or_comm]

theorem hermitePair_factorization (n : ℕ) (j k : Fin n) (x : Fin n → ℝ) :
    (∏ i, realHermiteFactor (hermitePairDegree n j k i) (x i)) =
      x j * x k - if j = k then 1 else 0 := by
  classical
  by_cases h : j = k
  · subst k
    have hp (i : Fin n) : realHermiteFactor (hermitePairDegree n j j i) (x i) =
        if i = j then x j ^ 2 - 1 else 1 := by
      by_cases hi : i = j
      · subst i
        simp [hermitePairDegree, realHermiteFactor_two]
      · simp [hermitePairDegree, hi, realHermiteFactor_zero]
    simp_rw [hp]
    simp [pow_two]
  · have hp (i : Fin n) : realHermiteFactor (hermitePairDegree n j k i) (x i) =
        (if i = j then x j else 1) * (if i = k then x k else 1) := by
      by_cases hij : i = j
      · subst i
        simp [hermitePairDegree, h, realHermiteFactor_one]
      · by_cases hik : i = k
        · subst i
          simp [hermitePairDegree, h, Ne.symm h, realHermiteFactor_one]
        · simp [hermitePairDegree, h, hij, hik, realHermiteFactor_zero]
    simp_rw [hp]
    rw [Finset.prod_mul_distrib]
    simp [h]

theorem productGaussian_quadratic_pair_covariance_product (n : ℕ) (j k l p : Fin n) :
    Integrable (fun x : Fin n → ℝ =>
      (x j * x k - if j = k then 1 else 0) * (x l * x p - if l = p then 1 else 0))
      (Measure.pi fun _ => gaussianReal 0 1) ∧
    (∫ x : Fin n → ℝ,
      (x j * x k - if j = k then 1 else 0) * (x l * x p - if l = p then 1 else 0)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∏ i, if hermitePairDegree n j k i = hermitePairDegree n l p i then
        (if hermitePairDegree n j k i = 2 then 2 else 1) else 0 := by
  have heq : (fun x : Fin n → ℝ =>
      (x j * x k - if j = k then 1 else 0) * (x l * x p - if l = p then 1 else 0)) =
      (fun x : Fin n → ℝ => ∏ i,
        realHermiteFactor (hermitePairDegree n j k i) (x i) *
        realHermiteFactor (hermitePairDegree n l p i) (x i)) := by
    funext x
    rw [Finset.prod_mul_distrib, hermitePair_factorization, hermitePair_factorization]
  rw [heq]
  exact productGaussian_hermite_gram n (hermitePairDegree n j k) (hermitePairDegree n l p)

end AffineFKProof
