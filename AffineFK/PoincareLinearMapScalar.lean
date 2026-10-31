module

public import AffineFK.PoincareLinearMap

/-! Scalar images have the exact admissible Poincare constant `a² P`. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

theorem poincareLinearMap_scalar (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (a : ℝ) (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (f x - ∫ y, f y ∂ν.map (fun z => a • z)) ^ 2 ∂ν.map (fun z => a • z)) ≤
      (a ^ 2 * P) * (∫ x, ‖gradient f x‖ ^ 2 ∂ν.map (fun z => a • z)) := by
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    a • ContinuousLinearMap.id ℝ _
  have hA : ‖A‖ ≤ |a| := by
    change ‖a • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))) (abs_nonneg a)
  have hA2 : ‖A‖ ^ 2 ≤ a ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (norm_nonneg A) (abs_nonneg a)).mpr hA
  have h := poincareLinearMap n n ν P hP0 hP A f
  apply h.trans
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA2 hP0)
  exact integral_nonneg fun x => sq_nonneg ‖gradient f x‖

end AffineFKProof
