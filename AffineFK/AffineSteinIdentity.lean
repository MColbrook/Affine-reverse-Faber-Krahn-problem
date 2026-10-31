module

public import AffineFK.AffineTestFunctions
public import AffineFK.SteinTensorAssembly

/-!
# The Stein identity with an affine test

For fixed other summands the test is phi((x+b)/r). Its first derivative has
factor r^{-1} and its second derivative has factor r^{-2}. This module proves
the resulting actual integral identity and every integrability assertion
before the later product-measure and conditional-expectation steps.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem tensorPartialContraction_affine
    (n : ℕ) (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (i : Fin n) (r : ℝ) (hr : r ≠ 0) (b : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (x : EuclideanSpace ℝ (Fin n)) :
    tensorPartialContraction n T i (affineTestFunction r hr b φ) x =
      (r⁻¹ * r⁻¹) * (∑ j : Fin n, ∑ k : Fin n,
        T x (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (x + b))) := by
  unfold tensorPartialContraction
  simp_rw [second_partialTest_affine]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  change T x (i, j, k) * ((r⁻¹ * r⁻¹) * partialTest n k (partialTest n j φ) (r⁻¹ • (x + b))) = _
  ring

theorem affine_tensor_contraction_integrable
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n) (r : ℝ) (hr : r ≠ 0) (b : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x => ∑ j : Fin n, ∑ k : Fin n,
      T x (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (x + b))) ν := by
  apply integrable_finsetSum Finset.univ
  intro j _hj
  apply integrable_finsetSum Finset.univ
  intro k _hk
  have hp : MemLp (fun x => partialTest n k (partialTest n j φ) (r⁻¹ • (x + b))) 2 ν := by
    change MemLp (affineTestFunction r hr b (partialTest n k (partialTest n j φ))) 2 ν
    exact (Lp.memLp (testFunctionToL2 ν (affineTestFunction r hr b (partialTest n k (partialTest n j φ))))).ae_eq
      (testFunctionToL2_coe ν (affineTestFunction r hr b (partialTest n k (partialTest n j φ))))
  exact (hT.eval_piLp (i, j, k)).integrable_mul hp

theorem affine_stein_component_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hidentity : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, x i * ψ x ∂ν) - (∫ x, partialTest n i ψ x ∂ν) =
        ∫ x, tensorPartialContraction n T i ψ x ∂ν)
    (r : ℝ) (hr : r ≠ 0) (b : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x => x i * φ (r⁻¹ • (x + b))) ν ∧
    Integrable (fun x => partialTest n i φ (r⁻¹ • (x + b))) ν ∧
    Integrable (fun x => ∑ j : Fin n, ∑ k : Fin n,
      T x (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (x + b))) ν ∧
    (∫ x, x i * φ (r⁻¹ • (x + b)) ∂ν) -
      r⁻¹ * (∫ x, partialTest n i φ (r⁻¹ • (x + b)) ∂ν) =
      (r⁻¹ * r⁻¹) * (∫ x, ∑ j : Fin n, ∑ k : Fin n,
        T x (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (x + b)) ∂ν) := by
  have hp : MemLp (fun x => φ (r⁻¹ • (x + b))) 2 ν := by
    change MemLp (affineTestFunction r hr b φ) 2 ν
    exact (Lp.memLp (testFunctionToL2 ν (affineTestFunction r hr b φ))).ae_eq
      (testFunctionToL2_coe ν (affineTestFunction r hr b φ))
  have hd : MemLp (fun x => partialTest n i φ (r⁻¹ • (x + b))) 2 ν := by
    change MemLp (affineTestFunction r hr b (partialTest n i φ)) 2 ν
    exact (Lp.memLp (testFunctionToL2 ν (affineTestFunction r hr b (partialTest n i φ)))).ae_eq
      (testFunctionToL2_coe ν (affineTestFunction r hr b (partialTest n i φ)))
  refine ⟨hxi.integrable_mul hp, hd.integrable (by norm_num),
    affine_tensor_contraction_integrable n ν T hT i r hr b φ, ?_⟩
  have h := hidentity (affineTestFunction r hr b φ)
  have hderiv : (∫ x, partialTest n i (affineTestFunction r hr b φ) x ∂ν) =
      r⁻¹ * ∫ x, partialTest n i φ (r⁻¹ • (x + b)) ∂ν := by
    simp_rw [partialTest_affine]
    change (∫ x, r⁻¹ * partialTest n i φ (r⁻¹ • (x + b)) ∂ν) = _
    exact integral_const_mul _ _
  rw [hderiv] at h
  simp_rw [tensorPartialContraction_affine] at h
  rw [integral_const_mul] at h
  simpa only [affineTestFunction_apply] using h

end AffineFKProof
