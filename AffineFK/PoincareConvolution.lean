module

public import AffineFK.PoincareConvolutionAverage
public import AffineFK.PoincareLinearMap

/-!
# The exact sum of Poincare constants under convolution

The proof integrates the genuine input inequality in the first variable,
then applies the smooth L2 extension in the second variable to the actual
average. Fubini and the variance identity preserve the exact constant.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter ProbabilityTheory
open scoped Distributions RealInnerProductSpace ContDiff ENNReal

theorem poincareConvolution (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (P Q : ℝ) (_hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (hQ : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂η) ^ 2 ∂η) ≤ Q * (∫ x, ‖gradient f x‖ ^ 2 ∂η))
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (f x - ∫ y, f y ∂(ν.prod η).map (fun p => p.1 + p.2)) ^ 2
      ∂(ν.prod η).map (fun p => p.1 + p.2)) ≤
      (P + Q) * (∫ x, ‖gradient f x‖ ^ 2 ∂(ν.prod η).map (fun p => p.1 + p.2)) := by
  obtain ⟨C, D, _, _, hC, hD⟩ := poincareConvolution_test_bounds n f
  let g := poincareConvolutionAverage n ν f
  have hgj := poincareConvolutionAverage_memLp n ν η f
  have hg2 : Integrable (fun y => (g y) ^ 2) η := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hgj.1.aestronglyMeasurable).mp hgj.1
  have hgg2 : Integrable (fun y => ‖gradient g y‖ ^ 2) η :=
    (memLp_two_iff_integrable_sq_norm hgj.2.aestronglyMeasurable).mp hgj.2
  have hfL2 : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      f (p.1 + p.2)) 2 (ν.prod η) :=
    MemLp.of_bound (f.continuous.comp (by fun_prop)).aestronglyMeasurable C
      (Eventually.of_forall fun p => hC _)
  have hfgL2 : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      gradient f (p.1 + p.2)) 2 (ν.prod η) :=
    MemLp.of_bound (((toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (f.contDiff.continuous_fderiv (by simp))).comp (by fun_prop)).aestronglyMeasurable D
      (Eventually.of_forall fun p => hD _)
  have hf2 : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (f (p.1 + p.2)) ^ 2) (ν.prod η) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hfL2.aestronglyMeasurable).mp hfL2
  have hfg2 : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖gradient f (p.1 + p.2)‖ ^ 2) (ν.prod η) :=
    (memLp_two_iff_integrable_sq_norm hfgL2.aestronglyMeasurable).mp hfgL2
  have hfiber (y : EuclideanSpace ℝ (Fin n)) :
      (∫ x, (f (x + y)) ^ 2 ∂ν) - (g y) ^ 2 ≤ P * (∫ x, ‖gradient f (x + y)‖ ^ 2 ∂ν) := by
    have ht := hP (translatedTestFunction y f)
    simp only [translatedTestFunction_apply, gradient_translatedTestFunction] at ht
    have htL2 : MemLp (fun x => f (x + y)) 2 ν :=
      MemLp.of_bound (f.continuous.comp (by fun_prop)).aestronglyMeasurable C
        (Eventually.of_forall fun x => hC _)
    have hv : (∫ x, (f (x + y) - ∫ z, f (z + y) ∂ν) ^ 2 ∂ν) =
        (∫ x, (f (x + y)) ^ 2 ∂ν) - (∫ z, f (z + y) ∂ν) ^ 2 :=
      (variance_eq_integral htL2.aemeasurable).symm.trans (variance_eq_sub htL2)
    rw [hv] at ht
    exact ht
  have hfirst : (∫ y, ∫ x, (f (x + y)) ^ 2 ∂ν ∂η) - (∫ y, (g y) ^ 2 ∂η) ≤
      P * (∫ y, ∫ x, ‖gradient f (x + y)‖ ^ 2 ∂ν ∂η) := by
    have hh := integral_mono (hf2.integral_prod_right.sub hg2)
      (hfg2.integral_prod_right.const_mul P) hfiber
    change (∫ y, ((∫ x, (f (x + y)) ^ 2 ∂ν) - (g y) ^ 2) ∂η) ≤
      ∫ y, P * (∫ x, ‖gradient f (x + y)‖ ^ 2 ∂ν) ∂η at hh
    rwa [integral_sub hf2.integral_prod_right hg2, integral_const_mul] at hh
  have hsecond := poincareSmoothExtension n η Q hQ g
    (poincareConvolutionAverage_smooth n ν f) hgj.1 hgj.2
  have hgvar : (∫ y, (g y - ∫ z, g z ∂η) ^ 2 ∂η) =
      (∫ y, (g y) ^ 2 ∂η) - (∫ y, g y ∂η) ^ 2 :=
    (variance_eq_integral hgj.1.aemeasurable).symm.trans (variance_eq_sub hgj.1)
  rw [hgvar] at hsecond
  have hJ : (∫ y, ‖gradient g y‖ ^ 2 ∂η) ≤
      ∫ y, ∫ x, ‖gradient f (x + y)‖ ^ 2 ∂ν ∂η :=
    integral_mono hgg2 hfg2.integral_prod_right (poincareConvolutionAverage_jensen n ν f)
  have hsecond' := hsecond.trans (mul_le_mul_of_nonneg_left hJ hQ0)
  have hflaw : MemLp (f : EuclideanSpace ℝ (Fin n) → ℝ) 2
      ((ν.prod η).map (fun p => p.1 + p.2)) :=
    MemLp.of_bound f.continuous.aestronglyMeasurable C (Eventually.of_forall hC)
  have hvar : (∫ x, (f x - ∫ y, f y ∂(ν.prod η).map (fun p => p.1 + p.2)) ^ 2
      ∂(ν.prod η).map (fun p => p.1 + p.2)) =
      (∫ p, (f (p.1 + p.2)) ^ 2 ∂ν.prod η) - (∫ p, f (p.1 + p.2) ∂ν.prod η) ^ 2 := by
    rw [← variance_eq_integral hflaw.aemeasurable,
      variance_map f.continuous.measurable.aemeasurable (by fun_prop)]
    exact variance_eq_sub hfL2
  have hgradmap : (∫ x, ‖gradient f x‖ ^ 2 ∂(ν.prod η).map (fun p => p.1 + p.2)) =
      ∫ p, ‖gradient f (p.1 + p.2)‖ ^ 2 ∂ν.prod η := by
    apply integral_map (by fun_prop)
    exact (((toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (f.contDiff.continuous_fderiv (by simp))).norm.pow 2).aestronglyMeasurable
  have hmean := integral_prod_symm _ (hfL2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  rw [hvar, hgradmap, integral_prod_symm _ hf2, integral_prod_symm _ hfg2, hmean]
  change (∫ y, ∫ x, (f (x + y)) ^ 2 ∂ν ∂η) - (∫ y, g y ∂η) ^ 2 ≤
    (P + Q) * (∫ y, ∫ x, ‖gradient f (x + y)‖ ^ 2 ∂ν ∂η)
  nlinarith [hfirst, hsecond']

end AffineFKProof
