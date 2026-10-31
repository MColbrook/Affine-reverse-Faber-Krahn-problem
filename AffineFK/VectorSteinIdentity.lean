module

public import AffineFK.OddSteinTensor
public import AffineFK.SmoothPartials

/-!
# The vector-field second-order Stein identity

The divergence is the sum of genuine diagonal partials of the vector field.
The tensor contraction uses partial_j(partial_k F_i), exactly the manuscript's
index order. Schwarz symmetry relates it to the order supplied by the Poisson
equations. Every finite sum/integral exchange is justified by L2 integrability.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

def vectorComponentTest
    (n : ℕ) (i : Fin n)
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n))) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  TestFunction.postcompCLM (coordinateFunctional n i) F

theorem vectorComponentTest_apply
    (n : ℕ) (i : Fin n)
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : vectorComponentTest n i F x = F x i := by
  exact coordinateFunctional_apply n i (F x)

def vectorDivergence
    (n : ℕ)
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, partialTest n i (vectorComponentTest n i F) x

def vectorHessianContraction
    (n : ℕ) (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    T x (i, j, k) * partialTest n j (partialTest n k (vectorComponentTest n i F)) x

theorem vector_stein_left_sum
    (n : ℕ)
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, F x⟫ - vectorDivergence n F x =
      ∑ i : Fin n, (x i * vectorComponentTest n i F x -
        partialTest n i (vectorComponentTest n i F) x) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    vectorDivergence, vectorComponentTest_apply, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  exact mul_comm _ _

theorem vector_hessian_contraction_sum
    (n : ℕ) (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    vectorHessianContraction n T F x =
      ∑ i : Fin n, tensorPartialContraction n T i (vectorComponentTest n i F) x := by
  unfold vectorHessianContraction tensorPartialContraction
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  rw [partialTest_commute n j k]

theorem testFunction_memLp_two
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) : MemLp φ 2 ν :=
  (Lp.memLp (testFunctionToL2 ν φ)).ae_eq (testFunctionToL2_coe ν φ)

/-- The component identity yields the actual vector-field identity, with
the manuscript's Hessian index order and genuine integrability of both sides. -/
theorem component_identity_implies_vector_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν)
    (hidentity : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν) =
        ∫ x, tensorPartialContraction n T i φ x ∂ν)
    (F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n))) :
    Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x) ν ∧
      Integrable (vectorHessianContraction n T F) ν ∧
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) =
        ∫ x, vectorHessianContraction n T F x ∂ν := by
  have hm (i : Fin n) : Integrable (fun x => x i * vectorComponentTest n i F x) ν :=
    (hxi i).integrable_mul (testFunction_memLp_two n ν (vectorComponentTest n i F))
  have hd (i : Fin n) : Integrable (fun x => partialTest n i (vectorComponentTest n i F) x) ν :=
    (testFunction_memLp_two n ν (partialTest n i (vectorComponentTest n i F))).integrable (by norm_num)
  have hl (i : Fin n) : Integrable (fun x => x i * vectorComponentTest n i F x -
      partialTest n i (vectorComponentTest n i F) x) ν := (hm i).sub (hd i)
  have hr (i : Fin n) := tensorPartialContraction_integrable n ν T hT i (vectorComponentTest n i F)
  have hleft : Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x) ν := by
    simp_rw [vector_stein_left_sum]
    exact integrable_finsetSum Finset.univ fun i _hi => hl i
  have hright : Integrable (vectorHessianContraction n T F) ν := by
    have heq : vectorHessianContraction n T F =
        (fun x => ∑ i : Fin n, tensorPartialContraction n T i (vectorComponentTest n i F) x) :=
      funext (vector_hessian_contraction_sum n T F)
    rw [heq]
    exact integrable_finsetSum Finset.univ fun i _hi => hr i
  refine ⟨hleft, hright, ?_⟩
  simp_rw [vector_stein_left_sum, vector_hessian_contraction_sum]
  rw [integral_finsetSum Finset.univ (fun i _hi => hl i),
    integral_finsetSum Finset.univ (fun i _hi => hr i)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [integral_sub (hm i) (hd i)]
  exact hidentity i (vectorComponentTest n i F)

/-- The full odd, centred second-order Stein tensor for smooth compactly
supported vector fields, with exact P(P-1)n and no assumed Stein equations. -/
theorem second_stein_exists_odd_tensor
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    [Measure.IsNegInvariant ν]
    (P : ℝ) (hPnonneg : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (hmean : ∀ i : Fin n, ∫ x, x i ∂ν = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0) :
    ∃ T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n),
      MemLp T 2 ν ∧ Integrable T ν ∧ (∫ x, T x ∂ν) = 0 ∧
      (∀ x, T (-x) = -T x) ∧ ((∫ x, ‖T x‖ ^ 2 ∂ν) ≤ P * (P - 1) * n) ∧
      (∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
        Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x) ν ∧
        Integrable (vectorHessianContraction n T F) ν ∧
        (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) =
          ∫ x, vectorHessianContraction n T F x ∂ν) := by
  obtain ⟨T, hT, hTint, hTmean, hTodd, henergy, hidentity⟩ :=
    second_stein_exists_odd_tensor_components n ν P hPnonneg hP hmean hcov
  exact ⟨T, hT, hTint, hTmean, hTodd, henergy, fun F =>
    component_identity_implies_vector_identity n ν (isotropic_coordinate_memLp n ν hcov) T hT hidentity F⟩

end AffineFKProof
