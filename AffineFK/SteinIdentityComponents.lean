module

public import AffineFK.VectorSteinIdentity

/-!
# Recovering the scalar components of the vector Stein identity

A scalar test is embedded into one actual vector coordinate. This proves the
reverse implication needed to apply the normalized-sum construction to any
tensor satisfying the manuscript's vector identity, not just the tensor
returned by the particular Poisson construction.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

def singleComponentTest
    (n : ℕ) (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)) :=
  TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)) φ

theorem singleComponentTest_apply
    (n : ℕ) (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    singleComponentTest n i φ x = φ x • EuclideanSpace.basisFun (Fin n) ℝ i := by rfl

theorem vectorComponentTest_single
    (n : ℕ) (i p : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    vectorComponentTest n p (singleComponentTest n i φ) = if p = i then φ else 0 := by
  ext x
  rw [vectorComponentTest_apply, singleComponentTest_apply]
  by_cases hp : p = i
  · subst p
    simp [PiLp.smul_apply, EuclideanSpace.basisFun_apply]
  · simp [PiLp.smul_apply, EuclideanSpace.basisFun_apply, hp]

theorem partialTest_zero (n : ℕ) (j : Fin n) :
    partialTest n j (0 : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) = 0 := by
  unfold partialTest
  rw [map_zero, map_zero]

theorem tensorPartialContraction_zero
    (n : ℕ) (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    tensorPartialContraction n T i (0 : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) x = 0 := by
  simp [tensorPartialContraction, partialTest_zero]

theorem vectorDivergence_singleComponentTest
    (n : ℕ) (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    vectorDivergence n (singleComponentTest n i φ) x = partialTest n i φ x := by
  unfold vectorDivergence
  rw [Finset.sum_eq_single i]
  · rw [vectorComponentTest_single, ite_eq_left rfl]
  · intro p _hp hpi
    rw [vectorComponentTest_single, ite_eq_right hpi, partialTest_zero]
    rfl
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem vectorHessianContraction_singleComponentTest
    (n : ℕ) (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    vectorHessianContraction n T (singleComponentTest n i φ) x = tensorPartialContraction n T i φ x := by
  rw [vector_hessian_contraction_sum, Finset.sum_eq_single i]
  · rw [vectorComponentTest_single, ite_eq_left rfl]
  · intro p _hp hpi
    rw [vectorComponentTest_single, ite_eq_right hpi, tensorPartialContraction_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem singleComponentTest_inner
    (n : ℕ) (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, singleComponentTest n i φ x⟫ = x i * φ x := by
  rw [singleComponentTest_apply, inner_smul_right, real_inner_comm, EuclideanSpace.basisFun_inner]
  exact mul_comm _ _

theorem vector_identity_implies_component_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) = ∫ x, vectorHessianContraction n T F x ∂ν) :
    ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν) =
        ∫ x, tensorPartialContraction n T i φ x ∂ν := by
  intro i φ
  have hfirst : Integrable (fun x => x i * φ x) ν :=
    (hxi i).integrable_mul (testFunction_memLp_two n ν φ)
  have hderiv : Integrable (partialTest n i φ) ν :=
    (testFunction_memLp_two n ν (partialTest n i φ)).integrable (by norm_num)
  have h := hidentity (singleComponentTest n i φ)
  simp_rw [singleComponentTest_inner, vectorDivergence_singleComponentTest,
    vectorHessianContraction_singleComponentTest] at h
  rw [integral_sub hfirst hderiv] at h
  exact h

end AffineFKProof
