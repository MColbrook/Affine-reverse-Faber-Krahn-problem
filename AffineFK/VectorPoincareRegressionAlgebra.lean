module

public import AffineFK.SobolevCoordinates
public import AffineFK.MatrixHilbertSchmidt

/-!
# Actual coordinate linear forms and their regression moments

The linear forms use the original Euclidean coordinates. Isotropy and
score-coordinate orthogonality below are literal actual integrals, with
all products proved integrable by L2 Holder. The matrix energy is the
explicit sum of squared entries from the frozen Hilbert--Schmidt module.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace ENNReal

def vectorPoincareLinearForm (n : ℕ) (a : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := ∑ j, a j • coordinateFunctional n j

theorem vectorPoincareLinearForm_apply (n : ℕ) (a : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    vectorPoincareLinearForm n a x = ∑ j, a j * x j := by
  simp [vectorPoincareLinearForm, coordinateFunctional_apply, smul_eq_mul]

theorem vectorPoincareLinearForm_gradient_coordinate (n : ℕ) (a : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    gradient (vectorPoincareLinearForm n a) x j = a j := by
  rw [gradient, (vectorPoincareLinearForm n a).fderiv]
  simp [vectorPoincareLinearForm, coordinateFunctional,
    EuclideanSpace.basisFun_apply, smul_eq_mul, Pi.single_apply]

theorem vectorPoincareLinearForm_memLp (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (a : Fin n → ℝ) : MemLp (vectorPoincareLinearForm n a) 2 ν := by
  have h := memLp_finsetSum Finset.univ (fun j _ => (hxi j).const_mul (a j))
  have heq : (vectorPoincareLinearForm n a : EuclideanSpace ℝ (Fin n) → ℝ) =
      fun x => ∑ j, a j * x j := funext (vectorPoincareLinearForm_apply n a)
  rw [heq]
  exact h

theorem vectorPoincareLinearForm_mean (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (a : Fin n → ℝ) : (∫ x, vectorPoincareLinearForm n a x ∂ν) = 0 := by
  simp_rw [vectorPoincareLinearForm_apply]
  rw [integral_finsetSum Finset.univ (fun j _ =>
    ((hxi j).integrable (by norm_num)).const_mul (a j))]
  simp_rw [integral_const_mul, hmean, mul_zero]
  exact Finset.sum_const_zero

theorem vectorPoincareLinearForm_cross (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (r : EuclideanSpace ℝ (Fin n) → ℝ) (hr : MemLp r 2 ν)
    (hcross : ∀ j : Fin n, (∫ x, r x * x j ∂ν) = 0)
    (a : Fin n → ℝ) : (∫ x, r x * vectorPoincareLinearForm n a x ∂ν) = 0 := by
  have heq (x : EuclideanSpace ℝ (Fin n)) :
      r x * vectorPoincareLinearForm n a x = ∑ j, a j * (r x * x j) := by
    rw [vectorPoincareLinearForm_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [heq]
  have hi (j : Fin n) : Integrable (fun x => a j * (r x * x j)) ν := by
    simpa only [Pi.mul_apply] using (hr.integrable_mul (hxi j)).const_mul (a j)
  rw [integral_finsetSum Finset.univ (fun j _ => hi j)]
  simp_rw [integral_const_mul, hcross, mul_zero]
  exact Finset.sum_const_zero

theorem vectorPoincareLinearForm_second_moment (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (a : Fin n → ℝ) :
    (∫ x, (vectorPoincareLinearForm n a x) ^ 2 ∂ν) = ∑ j, (a j) ^ 2 := by
  have hi (j k : Fin n) : Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (a j * a k) * (x j * x k)) ν :=
    ((hxi j).integrable_mul (hxi k)).const_mul _
  have heq (x : EuclideanSpace ℝ (Fin n)) :
      (vectorPoincareLinearForm n a x) ^ 2 = ∑ j, ∑ k, (a j * a k) * (x j * x k) := by
    rw [vectorPoincareLinearForm_apply, pow_two]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ = ∑ j, ∑ k, (a j * a k) * (∫ x : EuclideanSpace ℝ (Fin n), x j * x k ∂ν) := by
      simp_rw [heq]
      rw [integral_finsetSum Finset.univ (fun j _ =>
        integrable_finsetSum Finset.univ (fun k _ => hi j k))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum Finset.univ (fun k _ => hi j k)]
      apply Finset.sum_congr rfl
      intro k _
      exact integral_const_mul _ _
    _ = _ := by simp [hsecond, pow_two]

theorem vectorPoincareRegression_row_moments (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (r : EuclideanSpace ℝ (Fin n) → ℝ) (hr : MemLp r 2 ν)
    (hrmean : (∫ x, r x ∂ν) = 0)
    (hcross : ∀ j : Fin n, (∫ x, r x * x j ∂ν) = 0)
    (a : Fin n → ℝ) :
    (∫ x, r x + vectorPoincareLinearForm n a x ∂ν) = 0 ∧
    (∫ x, ((r x + vectorPoincareLinearForm n a x) -
      ∫ y, r y + vectorPoincareLinearForm n a y ∂ν) ^ 2 ∂ν) =
        (∫ x, (r x) ^ 2 ∂ν) + ∑ j, (a j) ^ 2 := by
  have hL2 := vectorPoincareLinearForm_memLp n ν hxi a
  have hmean' : (∫ x, r x + vectorPoincareLinearForm n a x ∂ν) = 0 := by
    rw [integral_add (hr.integrable (by norm_num)) (hL2.integrable (by norm_num)),
      hrmean, vectorPoincareLinearForm_mean n ν hxi hmean, zero_add]
  refine ⟨hmean', ?_⟩
  rw [hmean']
  simp only [sub_zero]
  have hr2 : Integrable (fun x => (r x) ^ 2) ν := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).mp hr
  have hL2' : Integrable (fun x => (vectorPoincareLinearForm n a x) ^ 2) ν := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2
  have hcrossL1 : Integrable (fun x => r x * vectorPoincareLinearForm n a x) ν := by
    apply (hr.integrable_mul hL2).congr
    exact Filter.Eventually.of_forall fun _ => rfl
  calc
    _ = ∫ x, (r x) ^ 2 + 2 * (r x * vectorPoincareLinearForm n a x) +
        (vectorPoincareLinearForm n a x) ^ 2 ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    _ = (∫ x, (r x) ^ 2 ∂ν) + 2 * (∫ x, r x * vectorPoincareLinearForm n a x ∂ν) +
        (∫ x, (vectorPoincareLinearForm n a x) ^ 2 ∂ν) := by
      rw [integral_add (f := fun x => (r x) ^ 2 + 2 * (r x * vectorPoincareLinearForm n a x))
          (g := fun x => (vectorPoincareLinearForm n a x) ^ 2)
          (hr2.add (hcrossL1.const_mul 2)) hL2',
        integral_add (f := fun x => (r x) ^ 2)
          (g := fun x => 2 * (r x * vectorPoincareLinearForm n a x)) hr2 (hcrossL1.const_mul 2),
        integral_const_mul]
    _ = _ := by
      rw [vectorPoincareLinearForm_cross n ν hxi r hr hcross,
        vectorPoincareLinearForm_second_moment n ν hxi hsecond]
      ring

end AffineFKProof
