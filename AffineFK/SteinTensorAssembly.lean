module

public import AffineFK.SteinTestIdentities
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The actual third-order coefficient field

The gradients of the second Poisson solutions define a genuine Euclidean
three-index tensor field. Its L2 membership is obtained coordinatewise and
its Hilbert--Schmidt energy is exactly the sum of the row energies.
The finite-product Lp equivalence is reused from Etienne Marion's Mathlib
SpecificCodomains.WithLp development.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped RealInnerProductSpace Distributions

def secondSteinTensor
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (v : Fin n → Fin n → weightedSobolevGraph ν)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n × Fin n × Fin n) :=
  WithLp.toLp 2 (fun p => (sobolevGradient ν (v p.1 p.2.1) x) p.2.2)

theorem secondSteinTensor_apply
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (v : Fin n → Fin n → weightedSobolevGraph ν)
    (x : EuclideanSpace ℝ (Fin n)) (i j k : Fin n) :
    secondSteinTensor n ν v x (i, j, k) = (sobolevGradient ν (v i j) x) k := by rfl

theorem secondSteinTensor_memLp
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (v : Fin n → Fin n → weightedSobolevGraph ν) :
    MemLp (secondSteinTensor n ν v) 2 ν := by
  apply memLp_piLp_iff.mpr
  rintro ⟨i, j, k⟩
  exact (Lp.memLp (sobolevGradient ν (v i j))).eval_piLp k

theorem secondSteinTensor_norm_sq
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (v : Fin n → Fin n → weightedSobolevGraph ν)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖secondSteinTensor n ν v x‖ ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, ‖sobolevGradient ν (v i j) x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type,
    secondSteinTensor_apply]

theorem secondSteinTensor_energy
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (v : Fin n → Fin n → weightedSobolevGraph ν) :
    (∫ x, ‖secondSteinTensor n ν v x‖ ^ 2 ∂ν) =
      ∑ i : Fin n, ∑ j : Fin n, ‖sobolevGradient ν (v i j)‖ ^ 2 := by
  have hint (i j : Fin n) : Integrable (fun x => ‖sobolevGradient ν (v i j) x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp (sobolevGradient ν (v i j))).aestronglyMeasurable).mp
      (Lp.memLp (sobolevGradient ν (v i j)))
  have hisum (i : Fin n) : Integrable (fun x => ∑ j : Fin n,
      ‖sobolevGradient ν (v i j) x‖ ^ 2) ν :=
    integrable_finsetSum Finset.univ fun j _hj => hint i j
  simp_rw [secondSteinTensor_norm_sq]
  rw [integral_finsetSum Finset.univ (fun i _hi => hisum i)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [integral_finsetSum Finset.univ (fun j _hj => hint i j)]
  simp_rw [← l2_norm_sq_integral]

/-- The contraction with the iterated partials in the order supplied by
testing the second equation: partial_k(partial_j phi). Commutation with
the manuscript's Hessian ordering is a separate smoothness identity. -/
def tensorPartialContraction
    (n : ℕ) (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (i : Fin n) (φ : 𝓓((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j : Fin n, ∑ k : Fin n, T x (i, j, k) * partialTest n k (partialTest n j φ) x

theorem tensorPartialContraction_integrable
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n)
    (φ : 𝓓((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (tensorPartialContraction n T i φ) ν := by
  apply integrable_finsetSum Finset.univ
  intro j _hj
  apply integrable_finsetSum Finset.univ
  intro k _hk
  have hpartial : MemLp (partialTest n k (partialTest n j φ)) 2 ν :=
    (Lp.memLp (testFunctionToL2 ν (partialTest n k (partialTest n j φ)))).ae_eq
      (testFunctionToL2_coe ν (partialTest n k (partialTest n j φ)))
  exact (hT.eval_piLp (i, j, k)).integrable_mul hpartial

theorem secondSteinTensor_contraction
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (v : Fin n → Fin n → weightedSobolevGraph ν)
    (i : Fin n) (φ : 𝓓((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    tensorPartialContraction n (secondSteinTensor n ν v) i φ x =
      ∑ j : Fin n, ⟪sobolevGradient ν (v i j) x, gradient (partialTest n j φ) x⟫ := by
  simp only [tensorPartialContraction, secondSteinTensor_apply, partialTest_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  exact mul_comm _ _

theorem secondSteinTensor_contraction_integral
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (v : Fin n → Fin n → weightedSobolevGraph ν)
    (i : Fin n) (φ : 𝓓((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, tensorPartialContraction n (secondSteinTensor n ν v) i φ x ∂ν) =
      ∑ j : Fin n, ∫ x,
        ⟪sobolevGradient ν (v i j) x, gradient (partialTest n j φ) x⟫ ∂ν := by
  simp_rw [secondSteinTensor_contraction]
  apply integral_finsetSum
  intro j _hj
  have hint := L2.integrable_inner (𝕜 := ℝ) (sobolevGradient ν (v i j))
    (testFunctionToL2 ν (testFunctionGradient (partialTest n j φ)))
  apply hint.congr
  filter_upwards [testFunctionToL2_coe ν (testFunctionGradient (partialTest n j φ))] with x hx
  rw [hx, testFunctionGradient_apply]

/-- A genuine L2 third-order field with exact energy and the second-order
component identity, constructed from the original moment/Poincare premises.
Oddness and mean zero of this field are not yet asserted. -/
theorem second_stein_exists_tensor_components
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ) (hPnonneg : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (hmean : ∀ i : Fin n, ∫ x, x i ∂ν = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0) :
    ∃ T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n),
      MemLp T 2 ν ∧ ((∫ x, ‖T x‖ ^ 2 ∂ν) ≤ P * (P - 1) * n) ∧
      (∀ (i : Fin n) (φ : 𝓓((⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
        (∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν) =
          ∫ x, tensorPartialContraction n T i φ x ∂ν) := by
  obtain ⟨v, _hvmean, hvenergy, hidentity⟩ :=
    second_stein_exists_components n ν P hPnonneg hP hmean hcov
  refine ⟨secondSteinTensor n ν v, secondSteinTensor_memLp n ν v, ?_, ?_⟩
  · rw [secondSteinTensor_energy]
    exact hvenergy
  · intro i φ
    rw [secondSteinTensor_contraction_integral]
    exact hidentity i φ

end AffineFKProof
