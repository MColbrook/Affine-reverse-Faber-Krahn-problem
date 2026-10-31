module

public import AffineFK.PoincareConstantAttainment
public import AffineFK.PoincareSmoothExtension

/-!
# Covariance and second moments from the actual Poincare constant

The compact-test inequality extends to genuine linear functionals through
the proved smooth cutoff approximation. Mathlib's Riesz representation,
L2 composition and Bochner integral results retain their attribution.
No compact-support property is asserted for a linear functional.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem poincare_linear_variance_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) ν)
    (P : ℝ≥0) (hP : poincareConstant n ν ≤ (P : ℝ≥0∞))
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, (⟪v, x⟫ - ∫ y, ⟪v, y⟫ ∂ν) ^ 2 ∂ν) ≤ (P : ℝ) * ‖v‖ ^ 2 := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := toDual ℝ _ v
  have hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr hsecond
  have hL : MemLp L 2 ν := L.comp_memLp' hX
  have hgrad : gradient L = fun _ : EuclideanSpace ℝ (Fin n) => v := by
    funext x
    change (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ L x) = v
    rw [L.hasFDerivAt.fderiv]
    exact (toDual ℝ _).symm_apply_apply v
  have hG : MemLp (gradient L) 2 ν := by rw [hgrad]; exact memLp_const v
  have h := poincareSmoothExtension n ν (P : ℝ)
    (admissiblePoincareConstant_of_poincareConstant_le n ν P hP)
    L L.contDiff hL hG
  rw [hgrad] at h
  simpa only [L, toDual_apply_apply, integral_const, probReal_univ, one_smul] using h

theorem poincare_centered_second_moment_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) ν)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (P : ℝ≥0) (hP : poincareConstant n ν ≤ (P : ℝ≥0∞)) :
    (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 ∂ν) ≤ (P : ℝ) * n := by
  have hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr hsecond
  have hi (i : Fin n) : (∫ x : EuclideanSpace ℝ (Fin n), (x i) ^ 2 ∂ν) ≤ (P : ℝ) := by
    have h := poincare_linear_variance_bound n ν hsecond P hP
      (EuclideanSpace.basisFun (Fin n) ℝ i)
    simpa only [EuclideanSpace.basisFun_inner, hmean i, sub_zero,
      (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one, one_pow, mul_one] using h
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  have hsqi (i : Fin n) : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2) ν := by
    simpa only [id_eq] using (hX.eval_piLp i).integrable_sq
  rw [integral_finsetSum Finset.univ (fun i _ => hsqi i)]
  calc
    _ ≤ ∑ _i : Fin n, (P : ℝ) := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp [mul_comm]

end AffineFKProof
