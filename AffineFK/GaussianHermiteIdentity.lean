module

public import AffineFK.EuclideanGaussianIntegrationByParts

/-!
# The mixed second Hermite identity for Euclidean Gaussian tests

Two actual coordinate integrations by parts give the ordered mixed
derivative. The Kronecker correction is present for equal indices, and
all polynomial-times-test products are integrable by compact support.
This is the Gaussian integration-by-parts step used in the manuscript's
second-order score argument, before its separate conditional-score step.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

def coordinateMulTest (n : ℕ) (k : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  ⟨fun x => x k * φ x, by
    have heq : (fun x : EuclideanSpace ℝ (Fin n) => x k * φ x) =
        (coordinateFunctional n k : EuclideanSpace ℝ (Fin n) → ℝ) * φ := by
      funext x
      simp only [Pi.mul_apply, coordinateFunctional_apply]
    rw [heq]
    exact (coordinateFunctional n k).contDiff.mul φ.contDiff,
    φ.hasCompactSupport.mul_left, Set.subset_univ _⟩

theorem partialTest_coordinateMulTest (n : ℕ) (j k : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    partialTest n j (coordinateMulTest n k φ) x =
      (if j = k then 1 else 0) * φ x + x k * partialTest n j φ x := by
  have hφ : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hd := ((coordinateFunctional n k).hasFDerivAt (x := x)).mul hφ
  have hfd := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
    L (EuclideanSpace.basisFun (Fin n) ℝ j)) hd.fderiv
  have hmul : ((coordinateFunctional n k : EuclideanSpace ℝ (Fin n) → ℝ) * φ) =
      (coordinateMulTest n k φ : EuclideanSpace ℝ (Fin n) → ℝ) := by
    funext y
    simp only [Pi.mul_apply, coordinateFunctional_apply]
    rfl
  have hb : coordinateFunctional n k (EuclideanSpace.basisFun (Fin n) ℝ j) =
      if j = k then 1 else 0 := by
    by_cases h : j = k
    · subst k
      simp [coordinateFunctional_apply, EuclideanSpace.basisFun_apply]
    · simp [coordinateFunctional_apply, EuclideanSpace.basisFun_apply, h, Ne.symm h]
  rw [hmul] at hfd
  simp only [add_apply, smul_apply, smul_eq_mul] at hfd
  rw [hb, coordinateFunctional_apply] at hfd
  simp_rw [← partialTest_fderiv] at hfd
  calc
    _ = x k * partialTest n j φ x + φ x * (if j = k then 1 else 0) := hfd
    _ = _ := by ring

theorem stdGaussian_second_integration_by_parts (n : ℕ) (j k : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (x j * x k - if j = k then 1 else 0) * φ x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (partialTest n k (partialTest n j φ))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, (x j * x k - if j = k then 1 else 0) * φ x
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        ∫ x, partialTest n k (partialTest n j φ) x
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let δ : ℝ := if j = k then 1 else 0
  have hfirst := stdGaussian_coordinate_integration_by_parts n j (coordinateMulTest n k φ)
  have hsecond := stdGaussian_coordinate_integration_by_parts n k (partialTest n j φ)
  have hφ : Integrable φ γ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hderiv : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x k * partialTest n j φ x) γ :=
    hsecond.1
  have hxxφ : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x j * x k * φ x) γ := by
    convert hfirst.1 using 1
    funext x
    change x j * x k * φ x = x j * (x k * φ x)
    ring
  have hδφ := hφ.const_mul δ
  refine ⟨?_, hsecond.2.1, ?_⟩
  · convert hxxφ.sub hδφ using 1
    funext x
    change (x j * x k - δ) * φ x = x j * x k * φ x - δ * φ x
    ring
  · have heq : (∫ x, x j * x k * φ x ∂γ) =
        δ * (∫ x, φ x ∂γ) + ∫ x, x k * partialTest n j φ x ∂γ := by
      calc
        _ = ∫ x, x j * coordinateMulTest n k φ x ∂γ := by
          congr 1
          funext x
          change x j * x k * φ x = x j * (x k * φ x)
          ring
        _ = ∫ x, δ * φ x + x k * partialTest n j φ x ∂γ := by
          rw [hfirst.2.2]
          simp_rw [partialTest_coordinateMulTest]
          rfl
        _ = _ := by rw [integral_add hδφ hderiv, integral_const_mul]
    calc
      _ = (∫ x, x j * x k * φ x ∂γ) - δ * ∫ x, φ x ∂γ := by
        rw [← integral_const_mul, ← integral_sub hxxφ hδφ]
        congr 1
        funext x
        ring
      _ = ∫ x, x k * partialTest n j φ x ∂γ := by rw [heq]; ring
      _ = _ := hsecond.2.2

end AffineFKProof
