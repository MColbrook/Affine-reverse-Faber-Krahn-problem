module

public import AffineFK.StandardGaussianDensity
public import AffineFK.GaussianSmoothingDensity
public import AffineFK.GaussianKernelDerivativeBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Smooth finite-measure averages of translations

This general dominated-differentiation argument is independent of the
Gaussian derivative estimates. Its final Gaussian application uses proved,
global bounds for every derivative, rather than assuming regularity of the
smoothed density. The parametric integration theorem is due to Patrick
Massot; the higher-derivative development is due to Sébastien Gouëzel.
These primary Mathlib modules retain their Apache-2.0 attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ContDiff

theorem gaussianSmoothingRegularity_integrable_translation (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν] (a : ℝ)
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin n) → F) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun u => f (x - a • u)) ν := by
  apply (integrable_const C).mono'
    (hf.comp (by fun_prop)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => hC _

theorem gaussianSmoothingRegularity_continuous_translation_integral (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν] (a : ℝ)
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin n) → F) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) :
    Continuous (fun x => ∫ u, f (x - a • u) ∂ν) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro x
    exact (gaussianSmoothingRegularity_integrable_translation n ν a f hf C hC x).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun u => hC _
  · exact integrable_const C
  · exact Filter.Eventually.of_forall fun u => hf.comp (by fun_prop)

theorem gaussianSmoothingRegularity_hasFDerivAt_translation_integral (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν] (a : ℝ)
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : EuclideanSpace ℝ (Fin n) → F) (hf : ContDiff ℝ ∞ f)
    (C D : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (hD : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z => ∫ u, f (z - a • u) ∂ν)
      (∫ u, fderiv ℝ f (x - a • u) ∂ν) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun z u => fderiv ℝ f (z - a • u))
    (s := Set.univ) (bound := fun _ => D) (Filter.univ_mem)
  · exact Filter.Eventually.of_forall fun z =>
      (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact gaussianSmoothingRegularity_integrable_translation n ν a f hf.continuous C hC x
  · exact ((hf.continuous_fderiv (by simp)).comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u z _ => hD _
  · exact integrable_const D
  · exact Filter.Eventually.of_forall fun u z _ => by
      simpa [Function.comp_def] using ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp z
        ((hasFDerivAt_id z).sub_const (a • u)))

theorem gaussianSmoothingRegularity_contDiff_nat_translation_integral
    (n m : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν] (a : ℝ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : EuclideanSpace ℝ (Fin n) → F), ContDiff ℝ ∞ f →
      (∀ r : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ r f y‖ ≤ C) →
      ContDiff ℝ m (fun x => ∫ u, f (x - a • u) ∂ν) := by
  induction m with
  | zero =>
      intro F _ _ _ f hf hb
      obtain ⟨C, hC⟩ := hb 0
      apply contDiff_zero.mpr
      apply gaussianSmoothingRegularity_continuous_translation_integral n ν a f hf.continuous C
      intro y
      simpa only [norm_iteratedFDeriv_zero] using hC y
  | succ m ih =>
      intro F _ _ _ f hf hb
      obtain ⟨C, hC⟩ := hb 0
      obtain ⟨D, hD⟩ := hb 1
      have hC' (y) : ‖f y‖ ≤ C := by
        simpa only [norm_iteratedFDeriv_zero] using hC y
      have hD' (y) : ‖fderiv ℝ f y‖ ≤ D := by
        simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] using hD y
      have hd (x) := gaussianSmoothingRegularity_hasFDerivAt_translation_integral n ν a f hf C D hC' hD' x
      change ContDiff ℝ ((m : ℕ∞ω) + 1) _
      apply contDiff_succ_iff_fderiv.mpr
      refine ⟨fun x => (hd x).differentiableAt, by simp, ?_⟩
      have heq : fderiv ℝ (fun x => ∫ u, f (x - a • u) ∂ν) =
          fun x => ∫ u, fderiv ℝ f (x - a • u) ∂ν :=
        funext fun x => (hd x).fderiv
      rw [heq]
      apply ih (EuclideanSpace ℝ (Fin n) →L[ℝ] F) (fderiv ℝ f) (hf.fderiv_right (by simp))
      intro r
      obtain ⟨B, hB⟩ := hb (r + 1)
      exact ⟨B, fun y => by rw [norm_iteratedFDeriv_fderiv]; exact hB y⟩

theorem gaussianSmoothingRegularity_contDiff_translation_integral (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν] (a : ℝ)
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : EuclideanSpace ℝ (Fin n) → F) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ r : ℕ, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ r f y‖ ≤ C) :
    ContDiff ℝ ∞ (fun x => ∫ u, f (x - a • u) ∂ν) := by
  exact contDiff_infty.mpr fun m =>
    gaussianSmoothingRegularity_contDiff_nat_translation_integral n m ν a F f hf hb

theorem gaussianSmoothingDensity_smooth (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν]
    (a b : ℝ) : ContDiff ℝ ∞ (gaussianSmoothingDensity n ν a b) := by
  have hI : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) =>
      ∫ u, standardGaussianDensity n (z - (b⁻¹ * a) • u) ∂ν) :=
    gaussianSmoothingRegularity_contDiff_translation_integral n ν (b⁻¹ * a)
      (standardGaussianDensity n) (standardGaussianDensity_smooth n)
      (fun r => by
        obtain ⟨C, _, hC⟩ := standardGaussianDensity_iteratedFDeriv_bound n r
        exact ⟨C, hC⟩)
  have heq : gaussianSmoothingDensity n ν a b = fun x =>
      (b ^ n)⁻¹ * ∫ u, standardGaussianDensity n (b⁻¹ • x - (b⁻¹ * a) • u) ∂ν := by
    funext x
    simp only [gaussianSmoothingDensity, smul_sub, smul_smul]
  rw [heq]
  have hlin : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => b⁻¹ • x) := by fun_prop
  exact contDiff_const.mul (hI.comp hlin)

theorem gaussianSmoothingDensity_exists_positive_smooth (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    ∃ ρ : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ x, ρ x = (b ^ n)⁻¹ *
        ∫ u, standardGaussianDensity n (b⁻¹ • (x - a • u)) ∂ν) ∧
      (ν.prod (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2) = densityMeasure n ρ ∧
      (∀ x, 0 < ρ x) ∧ ContDiff ℝ ∞ ρ := by
  refine ⟨gaussianSmoothingDensity n ν a b, fun x => rfl,
    gaussianSmoothingDensity_law n ν a b hb,
    gaussianSmoothingDensity_pos n ν a b hb, gaussianSmoothingDensity_smooth n ν a b⟩

end AffineFKProof
