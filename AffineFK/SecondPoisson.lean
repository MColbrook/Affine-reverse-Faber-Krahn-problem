module

public import AffineFK.FirstSteinKernel
public import AffineFK.L2Coordinates

/-!
# The second Poisson equations and their summed energy

The scalar sources are actual coordinates of the centred first-kernel rows.
Their means follow from the first Poisson equations tested on coordinates.
Solving the second equations and summing Parseval's identity preserves the
exact P(P-1)n bound. Reflection and the differential second-order Stein
identity are separate assertions.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

def firstSteinSource
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (u : Fin n → weightedSobolevGraph ν) (i j : Fin n) : Lp ℝ 2 ν :=
  l2Coordinate n ν j (sobolevGradient ν (u i) -
    Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i))

theorem firstSteinSource_coe
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (u : Fin n → weightedSobolevGraph ν) (i j : Fin n) :
    firstSteinSource n ν u i j =ᵐ[ν] fun x =>
      (sobolevGradient ν (u i) x) j - (if i = j then 1 else 0) := by
  filter_upwards [l2Coordinate_coe n ν j (sobolevGradient ν (u i) -
    Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)),
    Lp.coeFn_sub (sobolevGradient ν (u i)) (Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)),
    Lp.coeFn_const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)] with x hc hd he
  rw [show firstSteinSource n ν u i j x = _ from hc, hd]
  simp only [Pi.sub_apply, he]
  simp [EuclideanSpace.basisFun_apply, eq_comm]

theorem firstSteinSource_mean_zero
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (u : Fin n → weightedSobolevGraph ν)
    (hpair : ∀ i j, ⟪sobolevGradient ν (u i),
      Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ = if i = j then 1 else 0)
    (i j : Fin n) : l2Mean ν (firstSteinSource n ν u i j) = 0 := by
  unfold firstSteinSource
  rw [l2Coordinate_mean, inner_sub_left, hpair, l2_const_inner,
    (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite]
  simp

theorem firstSteinSource_norm_sum
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (u : Fin n → weightedSobolevGraph ν) :
    (∑ i : Fin n, ∑ j : Fin n, ‖firstSteinSource n ν u i j‖ ^ 2) =
      ∑ i : Fin n, ‖sobolevGradient ν (u i) -
        Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _hi
  exact l2Coordinate_norm_sq_sum n ν _

/-- The actual second Poisson solutions exist, their sources are centred,
and summing their energies gives exactly P(P-1)n. -/
theorem second_poisson_solutions
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ) (hPnonneg : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (u : Fin n → weightedSobolevGraph ν)
    (hpair : ∀ i j, ⟪sobolevGradient ν (u i),
      Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ = if i = j then 1 else 0)
    (hrow : ∀ i, ‖sobolevGradient ν (u i) -
      Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 ≤ P - 1) :
    ∃ v : Fin n → Fin n → weightedSobolevGraph ν,
      (∀ i j, l2Mean ν (sobolevValue ν (v i j)) = 0) ∧
      (∀ i j f, ⟪sobolevGradient ν (v i j), sobolevGradient ν f⟫ =
        ⟪firstSteinSource n ν u i j, sobolevValue ν f⟫) ∧
      (∀ i j, ‖sobolevGradient ν (v i j)‖ ^ 2 ≤ P * ‖firstSteinSource n ν u i j‖ ^ 2) ∧
      (∑ i : Fin n, ∑ j : Fin n, ‖sobolevGradient ν (v i j)‖ ^ 2) ≤ P * (P - 1) * n := by
  have hex (i j : Fin n) := weighted_poisson_all_tests n ν P hPnonneg hP
    (firstSteinSource n ν u i j) (firstSteinSource_mean_zero n ν u hpair i j)
  choose v hv using fun i j => (hex i j).exists
  refine ⟨v, fun i j => (hv i j).1, fun i j => (hv i j).2.1,
    fun i j => (hv i j).2.2, ?_⟩
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, P * ‖firstSteinSource n ν u i j‖ ^ 2 :=
      Finset.sum_le_sum fun i _hi => Finset.sum_le_sum fun j _hj => (hv i j).2.2
    _ = P * (∑ i : Fin n, ∑ j : Fin n, ‖firstSteinSource n ν u i j‖ ^ 2) := by
      simp only [Finset.mul_sum]
    _ = P * (∑ i : Fin n, ‖sobolevGradient ν (u i) -
        Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2) := by
      rw [firstSteinSource_norm_sum]
    _ ≤ P * ((P - 1) * n) :=
      mul_le_mul_of_nonneg_left (first_stein_size n ν P u hrow) hPnonneg
    _ = _ := by ring

end AffineFKProof
