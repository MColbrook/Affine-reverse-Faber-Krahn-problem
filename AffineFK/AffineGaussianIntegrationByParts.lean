module

public import AffineFK.GaussianHermiteIdentity
public import AffineFK.AffineTestFunctions

/-!
# Gaussian integration by parts for affine compact tests

The actual test is x |-> phi(a x+b). Nonzero real a ensures compact
support of the pullback. Its exact first and ordered second derivative
factors are a and a². These are the Gaussian steps in the smoothed
relative-score argument, before integrating over the other random vector.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

def gaussianAffineTest (n : ℕ) (a : ℝ) (ha : a ≠ 0) (b : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  scaledTestFunction a⁻¹ (inv_ne_zero ha) (translatedTestFunction b φ)

theorem gaussianAffineTest_apply (n : ℕ) (a : ℝ) (ha : a ≠ 0) (b : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (x : EuclideanSpace ℝ (Fin n)) :
    gaussianAffineTest n a ha b φ x = φ (a • x + b) := by
  simp only [gaussianAffineTest, scaledTestFunction_apply, inv_inv, translatedTestFunction_apply]

theorem partialTest_gaussianAffineTest (n : ℕ) (j : Fin n)
    (a : ℝ) (ha : a ≠ 0) (b : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    partialTest n j (gaussianAffineTest n a ha b φ) =
      a • gaussianAffineTest n a ha b (partialTest n j φ) := by
  simp only [gaussianAffineTest, partialTest_scaled, inv_inv, partialTest_translated]

theorem second_partialTest_gaussianAffineTest (n : ℕ) (j k : Fin n)
    (a : ℝ) (ha : a ≠ 0) (b : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    partialTest n k (partialTest n j (gaussianAffineTest n a ha b φ)) =
      (a * a) • gaussianAffineTest n a ha b (partialTest n k (partialTest n j φ)) := by
  rw [partialTest_gaussianAffineTest, partialTest_smul, partialTest_gaussianAffineTest, smul_smul]

theorem stdGaussian_affine_integration_by_parts (n : ℕ) (j : Fin n)
    (a : ℝ) (ha : a ≠ 0) (b : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => x j * φ (a • x + b))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => partialTest n j φ (a • x + b))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, x j * φ (a • x + b) ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      a * ∫ x, partialTest n j φ (a • x + b) ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  have h := stdGaussian_coordinate_integration_by_parts n j (gaussianAffineTest n a ha b φ)
  have hd : Integrable (gaussianAffineTest n a ha b (partialTest n j φ))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    (gaussianAffineTest n a ha b (partialTest n j φ)).continuous.integrable_of_hasCompactSupport
      (gaussianAffineTest n a ha b (partialTest n j φ)).hasCompactSupport
  refine ⟨?_, ?_, ?_⟩
  · simpa only [gaussianAffineTest_apply] using h.1
  · convert hd using 1
    funext x
    exact (gaussianAffineTest_apply n a ha b (partialTest n j φ) x).symm
  · calc
      _ = ∫ x, partialTest n j (gaussianAffineTest n a ha b φ) x
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
        simpa only [gaussianAffineTest_apply] using h.2.2
      _ = _ := by
        rw [partialTest_gaussianAffineTest]
        change (∫ x, a * gaussianAffineTest n a ha b (partialTest n j φ) x
          ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = _
        simp_rw [gaussianAffineTest_apply]
        rw [integral_const_mul]

theorem stdGaussian_affine_second_integration_by_parts (n : ℕ) (j k : Fin n)
    (a : ℝ) (ha : a ≠ 0) (b : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (x j * x k - if j = k then 1 else 0) * φ (a • x + b))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => partialTest n k (partialTest n j φ) (a • x + b))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, (x j * x k - if j = k then 1 else 0) * φ (a • x + b)
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      a ^ 2 * ∫ x, partialTest n k (partialTest n j φ) (a • x + b)
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  have h := stdGaussian_second_integration_by_parts n j k (gaussianAffineTest n a ha b φ)
  have hd : Integrable (gaussianAffineTest n a ha b (partialTest n k (partialTest n j φ)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    (gaussianAffineTest n a ha b (partialTest n k (partialTest n j φ))).continuous.integrable_of_hasCompactSupport
      (gaussianAffineTest n a ha b (partialTest n k (partialTest n j φ))).hasCompactSupport
  refine ⟨?_, ?_, ?_⟩
  · simpa only [gaussianAffineTest_apply] using h.1
  · convert hd using 1
    funext x
    exact (gaussianAffineTest_apply n a ha b (partialTest n k (partialTest n j φ)) x).symm
  · calc
      _ = ∫ x, partialTest n k (partialTest n j (gaussianAffineTest n a ha b φ)) x
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
        simpa only [gaussianAffineTest_apply] using h.2.2
      _ = _ := by
        rw [second_partialTest_gaussianAffineTest]
        change (∫ x, (a * a) * gaussianAffineTest n a ha b (partialTest n k (partialTest n j φ)) x
          ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = _
        simp_rw [gaussianAffineTest_apply]
        rw [integral_const_mul, pow_two]

end AffineFKProof
