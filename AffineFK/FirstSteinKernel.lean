module

public import AffineFK.SobolevCoordinates

/-!
# The first Poisson solutions and the centred Stein-kernel bound

Coordinate membership supplies the actual tests which determine the means
of the kernel rows. The squared-distance identity then gives the exact P-1
bound, with no assumed Stein identity or assumed Poisson solution.

The construction follows the spectral-gap argument attributed to Courtade,
Fathi and Pananjady in the manuscript. The Hilbert and measure-theoretic
steps reuse Mathlib's Lax--Milgram, L2 and real inner-product results.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

theorem l2_vector_const_norm
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (ν : Measure X) [IsProbabilityMeasure ν] (e : E) :
    ‖Lp.const 2 ν e‖ = ‖e‖ := by
  rw [Lp.norm_const 2 ν e (by norm_num : (2 : ENNReal) ≠ 0)]
  simp [measureReal_def]

theorem coordinateL2_mean
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν) :
    l2Mean ν (hxi.toLp (fun x : EuclideanSpace ℝ (Fin n) => x i)) = ∫ x, x i ∂ν := by
  rw [l2Mean_apply]
  exact integral_congr_ae hxi.coeFn_toLp

theorem coordinateL2_inner
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i j : Fin n)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hxj : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x j) 2 ν) :
    ⟪hxi.toLp (fun x : EuclideanSpace ℝ (Fin n) => x i),
      hxj.toLp (fun x : EuclideanSpace ℝ (Fin n) => x j)⟫ = ∫ x, x i * x j ∂ν := by
  rw [l2_real_inner_integral]
  apply integral_congr_ae
  filter_upwards [hxi.coeFn_toLp, hxj.coeFn_toLp] with x hi hj
  rw [hi, hj]

theorem coordinateL2_norm_sq
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν) :
    ‖hxi.toLp (fun x : EuclideanSpace ℝ (Fin n) => x i)‖ ^ 2 = ∫ x, (x i) ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, coordinateL2_inner]
  simp only [pow_two]

/-- The original test-integral Poincare assumption and an actual centred
unit-variance coordinate imply P ≥ 1. -/
theorem poincare_one_le_of_coordinate
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hmean : ∫ x, x i ∂ν = 0) (hvar : ∫ x, (x i) ^ 2 ∂ν = 1) : 1 ≤ P := by
  have h := weighted_poincare_extension ν P (test_poincare_graph_bound ν P hP)
    (sobolevCoordinate n ν i hxi)
  rw [sobolevCoordinate_value, sobolevCoordinate_gradient, coordinateL2_norm_sq,
    coordinateL2_mean, hmean, hvar, l2_vector_const_norm,
    (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one] at h
  simpa using h

/-- Solving the first Poisson equation for every coordinate gives the exact
mean inner products and the rowwise P-1 discrepancy bound. -/
theorem first_poisson_solutions
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ) (hPnonneg : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hmean : ∀ i : Fin n, ∫ x, x i ∂ν = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0) :
    ∃ u : Fin n → weightedSobolevGraph ν,
      (∀ i, l2Mean ν (sobolevValue ν (u i)) = 0) ∧
      (∀ i f, ⟪sobolevGradient ν (u i), sobolevGradient ν f⟫ =
        ⟪(hxi i).toLp (fun x : EuclideanSpace ℝ (Fin n) => x i), sobolevValue ν f⟫) ∧
      (∀ i, ‖sobolevGradient ν (u i)‖ ^ 2 ≤ P) ∧
      (∀ i j, ⟪sobolevGradient ν (u i),
        Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ = if i = j then 1 else 0) ∧
      (∀ i, ‖sobolevGradient ν (u i) -
        Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 ≤ P - 1) := by
  have hex (i : Fin n) := weighted_poisson_all_tests n ν P hPnonneg hP
    ((hxi i).toLp (fun x : EuclideanSpace ℝ (Fin n) => x i))
    ((coordinateL2_mean n ν i (hxi i)).trans (hmean i))
  choose u hu using fun i => (hex i).exists
  have hnorm (i : Fin n) :
      ‖(hxi i).toLp (fun x : EuclideanSpace ℝ (Fin n) => x i)‖ ^ 2 = 1 := by
    rw [coordinateL2_norm_sq]
    simpa [pow_two] using hcov i i
  have henergy (i : Fin n) : ‖sobolevGradient ν (u i)‖ ^ 2 ≤ P := by
    simpa only [hnorm, mul_one] using (hu i).2.2
  have hpair (i j : Fin n) : ⟪sobolevGradient ν (u i),
      Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ = if i = j then 1 else 0 := by
    have h := (hu i).2.1 (sobolevCoordinate n ν j (hxi j))
    rw [sobolevCoordinate_gradient, sobolevCoordinate_value, coordinateL2_inner, hcov] at h
    exact h
  refine ⟨u, fun i => (hu i).1, fun i => (hu i).2.1, henergy, hpair, ?_⟩
  intro i
  have hii := hpair i i
  simp only [ite_true] at hii
  rw [norm_sub_sq_real, hii, l2_vector_const_norm,
    (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one]
  linarith [henergy i]

/-- Summing the genuine L2 row discrepancies yields the manuscript's exact
first Stein-kernel size bound. -/
theorem first_stein_size
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ) (u : Fin n → weightedSobolevGraph ν)
    (hrow : ∀ i, ‖sobolevGradient ν (u i) -
      Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 ≤ P - 1) :
    (∑ i : Fin n, ‖sobolevGradient ν (u i) -
      Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2) ≤ (P - 1) * n := by
  calc
    _ ≤ ∑ _i : Fin n, (P - 1) := Finset.sum_le_sum fun i _hi => hrow i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end AffineFKProof
