module

public import AffineFK.PoincareSmoothExtension

/-!
# Poincare inequalities under arbitrary linear maps

The linear map need not be injective, so its pullback of a compact test
function need not have compact support. The actual smooth L2 extension
justifies that test; the ordinary derivative chain rule gives the exact
squared operator-norm factor.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace ContDiff

theorem poincareLinearMap_gradient_bound (n m : ℕ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (f ∘ A) x‖ ≤ ‖A‖ * ‖gradient f (A x)‖ := by
  rw [norm_gradient_eq_fderiv, norm_gradient_eq_fderiv]
  have hd := ((hf.differentiable (by simp)).differentiableAt (x := A x)).hasFDerivAt.comp x A.hasFDerivAt
  rw [hd.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

theorem poincareLinearMap (n m : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin m))), ℝ)) :
    (∫ x, (f x - ∫ y, f y ∂ν.map A) ^ 2 ∂ν.map A) ≤
      (‖A‖ ^ 2 * P) * (∫ x, ‖gradient f x‖ ^ 2 ∂ν.map A) := by
  let Bf := TestFunction.toBoundedContinuousFunctionCLM ℝ f
  let Bg := TestFunction.toBoundedContinuousFunctionCLM ℝ (testFunctionGradient f)
  have hfb (x) : ‖f x‖ ≤ ‖Bf‖ := Bf.norm_coe_le_norm x
  have hgb (x) : ‖gradient f x‖ ≤ ‖Bg‖ := by
    rw [← testFunctionGradient_apply]
    exact Bg.norm_coe_le_norm x
  have hc : ContDiff ℝ ∞ (f ∘ A) := f.contDiff.comp A.contDiff
  have hgcont : Continuous (gradient (f ∘ A)) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp (hc.continuous_fderiv (by simp))
  have hfv : MemLp (f ∘ A) 2 ν :=
    MemLp.of_bound hc.continuous.aestronglyMeasurable ‖Bf‖ (Eventually.of_forall fun x => hfb (A x))
  have hgv : MemLp (gradient (f ∘ A)) 2 ν :=
    MemLp.of_bound hgcont.aestronglyMeasurable (‖A‖ * ‖Bg‖) (Eventually.of_forall fun x =>
      (poincareLinearMap_gradient_bound n m A f f.contDiff x).trans
        (mul_le_mul_of_nonneg_left (hgb _) (norm_nonneg A)))
  have hgsq : Integrable (fun x => ‖gradient (f ∘ A) x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hgv.aestronglyMeasurable).mp hgv
  have hgoalL2 : MemLp (fun x => gradient f (A x)) 2 ν := by
    apply MemLp.of_bound
      (((toDual ℝ (EuclideanSpace ℝ (Fin m))).symm.continuous.comp
        (f.contDiff.continuous_fderiv (by simp))).comp A.continuous).aestronglyMeasurable ‖Bg‖
    exact Eventually.of_forall fun x => hgb _
  have hgoalsq : Integrable (fun x => ‖gradient f (A x)‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hgoalL2.aestronglyMeasurable).mp hgoalL2
  have hgradle : (∫ x, ‖gradient (f ∘ A) x‖ ^ 2 ∂ν) ≤
      ‖A‖ ^ 2 * (∫ x, ‖gradient f (A x)‖ ^ 2 ∂ν) := by
    rw [← integral_const_mul]
    apply integral_mono hgsq (hgoalsq.const_mul _)
    intro x
    have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg A) (norm_nonneg _))).mpr
      (poincareLinearMap_gradient_bound n m A f f.contDiff x)
    simpa only [mul_pow] using hh
  have hp := (poincareSmoothExtension n ν P hP (f ∘ A) hc hfv hgv).trans
    (mul_le_mul_of_nonneg_left hgradle hP0)
  have hm : (∫ x, f x ∂ν.map A) = ∫ x, f (A x) ∂ν :=
    integral_map A.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable
  have hs : (∫ x, (f x - ∫ y, f y ∂ν.map A) ^ 2 ∂ν.map A) =
      ∫ x, (f (A x) - ∫ y, f (A y) ∂ν) ^ 2 ∂ν := by
    rw [hm]
    exact integral_map A.continuous.measurable.aemeasurable
      (f := fun x => (f x - ∫ y, f (A y) ∂ν) ^ 2)
      ((f.continuous.sub continuous_const).pow 2).aestronglyMeasurable
  have hg : (∫ x, ‖gradient f x‖ ^ 2 ∂ν.map A) = ∫ x, ‖gradient f (A x)‖ ^ 2 ∂ν := by
    apply integral_map A.continuous.measurable.aemeasurable
    exact (((toDual ℝ (EuclideanSpace ℝ (Fin m))).symm.continuous.comp
      (f.contDiff.continuous_fderiv (by simp))).norm.pow 2).aestronglyMeasurable
  rw [hs, hg]
  simpa only [Function.comp_apply, mul_left_comm, mul_assoc] using hp

end AffineFKProof
