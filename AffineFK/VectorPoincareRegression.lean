module

public import AffineFK.PoincareConstantAttainment
public import AffineFK.VectorPoincareRegressionAlgebra

/-!
# Componentwise Poincare regression with the actual least constant

The field and all of its actual component gradients are L2. A fixed real
matrix contributes a genuine linear coordinate form to each component.
The proved coordinate moments determine its exact variance. Summing the
actual smooth-L2 Poincare inequalities gives the explicit squared
Hilbert--Schmidt regression estimate. No Hessian membership or global
score equation is hidden in the premises.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace ENNReal NNReal ContDiff

def vectorPoincareDerivativeMatrix (n : ℕ)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => gradient (fun y => r y i) x j

theorem vectorPoincareRegression_gradient (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (a : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => f y + vectorPoincareLinearForm n a y) x =
      gradient f x + gradient (vectorPoincareLinearForm n a) 0 := by
  have hd := ((hf.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt.add
    (vectorPoincareLinearForm n a).hasFDerivAt
  change (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ (fun y => f y + vectorPoincareLinearForm n a y) x) =
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x) +
      (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
        (fderiv ℝ (vectorPoincareLinearForm n a) 0)
  have heq : (fun y => f y + vectorPoincareLinearForm n a y) =
      f + (vectorPoincareLinearForm n a : EuclideanSpace ℝ (Fin n) → ℝ) := rfl
  rw [heq, hd.fderiv, (vectorPoincareLinearForm n a).fderiv, map_add]

theorem vectorPoincareRegression_gradient_memLp (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hg : MemLp (gradient f) 2 ν) (a : Fin n → ℝ) :
    MemLp (gradient (fun y => f y + vectorPoincareLinearForm n a y)) 2 ν := by
  have heq : gradient (fun y => f y + vectorPoincareLinearForm n a y) =
      fun x => gradient f x + gradient (vectorPoincareLinearForm n a) 0 :=
    funext (vectorPoincareRegression_gradient n f hf a)
  rw [heq]
  exact hg.add (memLp_const _)

theorem vectorPoincareRegression_row (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ≥0) (hP : poincareConstant n ν ≤ (P : ℝ≥0∞))
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (r : EuclideanSpace ℝ (Fin n) → ℝ) (hr : MemLp r 2 ν)
    (hrmean : (∫ x, r x ∂ν) = 0)
    (hcross : ∀ j : Fin n, (∫ x, r x * x j ∂ν) = 0)
    (hsm : ContDiff ℝ ∞ r) (hg : MemLp (gradient r) 2 ν) (a : Fin n → ℝ) :
    (∫ x, (r x) ^ 2 ∂ν) + ∑ j, (a j) ^ 2 ≤
      (P : ℝ) * (∫ x, ‖gradient (fun y => r y + vectorPoincareLinearForm n a y) x‖ ^ 2 ∂ν) := by
  have h := poincareConstant_le_smooth_L2 n ν P hP
    (fun y => r y + vectorPoincareLinearForm n a y)
    (hsm.add (vectorPoincareLinearForm n a).contDiff)
    (hr.add (vectorPoincareLinearForm_memLp n ν hxi a))
    (vectorPoincareRegression_gradient_memLp n ν r hsm hg a)
  rw [(vectorPoincareRegression_row_moments n ν hxi hmean hsecond r hr hrmean hcross a).2] at h
  exact h

theorem vectorPoincareRegression (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ≥0) (hP0 : 0 < P) (hP : poincareConstant n ν ≤ (P : ℝ≥0∞))
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hr : MemLp r 2 ν)
    (hrmean : ∀ i : Fin n, (∫ x, r x i ∂ν) = 0)
    (hcross : ∀ i j : Fin n, (∫ x, r x i * x j ∂ν) = 0)
    (hsm : ContDiff ℝ ∞ r)
    (hg : ∀ i : Fin n, MemLp (gradient (fun y => r y i)) 2 ν)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n r x + A)) ν ∧
    ((∫ x, ‖r x‖ ^ 2 ∂ν) + matrixHilbertSchmidtSq A) / (P : ℝ) ≤
      ∫ x, matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n r x + A) ∂ν := by
  have hri (i : Fin n) : ContDiff ℝ ∞ (fun x => r x i) := by
    simpa only [Function.comp_def, coordinateFunctional_apply] using
      (coordinateFunctional n i).contDiff.comp hsm
  let F (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    r x i + vectorPoincareLinearForm n (A i) x
  have hgF (i : Fin n) : MemLp (gradient (F i)) 2 ν :=
    vectorPoincareRegression_gradient_memLp n ν (fun x => r x i) (hri i) (hg i) (A i)
  have hi (i : Fin n) : Integrable (fun x => ‖gradient (F i) x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (hgF i).aestronglyMeasurable).mp (hgF i)
  have hcomp (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
      gradient (F i) x j = gradient (fun y => r y i) x j + A i j := by
    change gradient (fun y => r y i + vectorPoincareLinearForm n (A i) y) x j = _
    rw [vectorPoincareRegression_gradient n _ (hri i)]
    simp only [PiLp.add_apply, vectorPoincareLinearForm_gradient_coordinate]
  have hHSfun : (fun x => matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n r x + A)) =
      fun x => ∑ i, ‖gradient (F i) x‖ ^ 2 := by
    funext x
    simp only [matrixHilbertSchmidtSq, vectorPoincareDerivativeMatrix, Matrix.add_apply,
      EuclideanSpace.real_norm_sq_eq, hcomp]
  have hHSint : Integrable
      (fun x => matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n r x + A)) ν := by
    rw [hHSfun]
    exact integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hHS : (∫ x, matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n r x + A) ∂ν) =
      ∑ i, ∫ x, ‖gradient (F i) x‖ ^ 2 ∂ν := by
    rw [hHSfun, integral_finsetSum Finset.univ (fun i _ => hi i)]
  have hri2 (i : Fin n) : Integrable (fun x => (r x i) ^ 2) ν := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (hr.eval_piLp i).aestronglyMeasurable).mp (hr.eval_piLp i)
  have hR : (∫ x, ‖r x‖ ^ 2 ∂ν) = ∑ i, ∫ x, (r x i) ^ 2 ∂ν := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    exact integral_finsetSum Finset.univ (fun i _ => hri2 i)
  have hrow (i : Fin n) := vectorPoincareRegression_row n ν P hP hxi hmean hsecond
    (fun x => r x i) (hr.eval_piLp i) (hrmean i) (hcross i) (hri i) (hg i) (A i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hrow i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  change (∑ i, ∫ x, (r x i) ^ 2 ∂ν) + matrixHilbertSchmidtSq A ≤
    (P : ℝ) * (∑ i, ∫ x, ‖gradient (F i) x‖ ^ 2 ∂ν) at hsum
  rw [← hR, ← hHS] at hsum
  refine ⟨hHSint, (div_le_iff₀ (show (0 : ℝ) < (P : ℝ) by exact_mod_cast hP0)).mpr ?_⟩
  simpa only [mul_comm] using hsum

end AffineFKProof
