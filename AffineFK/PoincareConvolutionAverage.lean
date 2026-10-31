module

public import AffineFK.PoincareSmoothExtension
public import AffineFK.GaussianSmoothingRegularity
public import AffineFK.AffineTestFunctions
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul

/-!
# Smooth averages and the Jensen estimate for Poincare convolution

The averaged test function generally has no compact support. Its actual
smoothness follows from dominated differentiation, and its actual gradient
is the average gradient. All L2 hypotheses used below follow from the
bounded compact test and its bounded gradient. Jensen's inequality is
reused from Mathlib's convex integral development.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace ContDiff ENNReal

theorem poincareConvolution_integral_norm_sq_le
    {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (g : X → F) (hg : MemLp g 2 ν) :
    ‖∫ x, g x ∂ν‖ ^ 2 ≤ ∫ x, ‖g x‖ ^ 2 ∂ν := by
  have hi : Integrable g ν := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hs : Integrable (fun x => ‖g x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hc : ConvexOn ℝ Set.univ (fun r : ℝ => r ^ 2) :=
    (by norm_num : Even (2 : ℕ)).convexOn_pow
  have hJ := hc.map_integral_le (continuous_pow 2).continuousOn isClosed_univ
    (Eventually.of_forall fun _ => Set.mem_univ _) hi.norm hs
  have hNonneg : 0 ≤ ∫ x, ‖g x‖ ∂ν := integral_nonneg fun x => norm_nonneg (g x)
  have hN : ‖∫ x, g x ∂ν‖ ^ 2 ≤ (∫ x, ‖g x‖ ∂ν) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hNonneg).mpr (norm_integral_le_integral_norm g)
  exact hN.trans hJ

def poincareConvolutionAverage (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (y : EuclideanSpace ℝ (Fin n)) : ℝ := ∫ x, f (x + y) ∂ν

theorem poincareConvolution_test_bounds (n : ℕ)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (∀ x, ‖f x‖ ≤ C) ∧ (∀ x, ‖gradient f x‖ ≤ D) := by
  let F := TestFunction.toBoundedContinuousFunctionCLM ℝ f
  let G := TestFunction.toBoundedContinuousFunctionCLM ℝ (testFunctionGradient f)
  refine ⟨‖F‖, ‖G‖, norm_nonneg _, norm_nonneg _, fun x => F.norm_coe_le_norm x, ?_⟩
  intro x
  rw [← testFunctionGradient_apply]
  exact G.norm_coe_le_norm x

theorem poincareConvolutionAverage_smooth (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν]
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ContDiff ℝ ∞ (poincareConvolutionAverage n ν f) := by
  have h := gaussianSmoothingRegularity_contDiff_translation_integral n ν (-1) f f.contDiff
    (fun r => by
      obtain ⟨C, _, hC⟩ := f.hasCompactSupport.exists_bound_iteratedFDeriv f.contDiff r
      exact ⟨C, hC r le_rfl⟩)
  have heq : (fun z : EuclideanSpace ℝ (Fin n) => ∫ x, f (z - (-1 : ℝ) • x) ∂ν) =
      poincareConvolutionAverage n ν f := by
    funext z
    simp only [poincareConvolutionAverage, neg_one_smul, sub_neg_eq_add, add_comm]
  rwa [heq] at h

theorem poincareConvolutionAverage_gradient (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν]
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (y : EuclideanSpace ℝ (Fin n)) :
    gradient (poincareConvolutionAverage n ν f) y = ∫ x, gradient f (x + y) ∂ν := by
  obtain ⟨C, D, _, _, hC, hD⟩ := poincareConvolution_test_bounds n f
  have hD' (x) : ‖fderiv ℝ f x‖ ≤ D := by
    rw [← norm_gradient_eq_fderiv]
    exact hD x
  have hd := gaussianSmoothingRegularity_hasFDerivAt_translation_integral n ν (-1)
    f f.contDiff C D hC hD' y
  have heq : (fun z : EuclideanSpace ℝ (Fin n) => ∫ x, f (z - (-1 : ℝ) • x) ∂ν) =
      poincareConvolutionAverage n ν f := by
    funext z
    simp only [poincareConvolutionAverage, neg_one_smul, sub_neg_eq_add, add_comm]
  rw [heq] at hd
  rw [gradient, hd.fderiv]
  calc
    _ = ∫ x, (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
        (fderiv ℝ f (y - (-1 : ℝ) • x)) ∂ν :=
      ((toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [neg_one_smul, sub_neg_eq_add, add_comm]
        rfl

theorem poincareConvolutionAverage_bounds (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (C D : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖gradient f x‖ ≤ D)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖poincareConvolutionAverage n ν f y‖ ≤ C ∧
      ‖gradient (poincareConvolutionAverage n ν f) y‖ ≤ D := by
  constructor
  · simpa only [poincareConvolutionAverage, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall fun x => hC (x + y)))
  · rw [poincareConvolutionAverage_gradient]
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall fun x => hD (x + y)))

theorem poincareConvolutionAverage_memLp (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsFiniteMeasure η]
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    MemLp (poincareConvolutionAverage n ν f) 2 η ∧
      MemLp (gradient (poincareConvolutionAverage n ν f)) 2 η := by
  obtain ⟨C, D, _, _, hC, hD⟩ := poincareConvolution_test_bounds n f
  have hc := poincareConvolutionAverage_smooth n ν f
  constructor
  · exact MemLp.of_bound hc.continuous.aestronglyMeasurable C
      (Eventually.of_forall fun y => (poincareConvolutionAverage_bounds n ν f C D hC hD y).1)
  · apply MemLp.of_bound
      ((toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
        (hc.continuous_fderiv (by simp))).aestronglyMeasurable D
    exact Eventually.of_forall fun y => (poincareConvolutionAverage_bounds n ν f C D hC hD y).2

theorem poincareConvolutionAverage_jensen (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (poincareConvolutionAverage n ν f) y‖ ^ 2 ≤
      ∫ x, ‖gradient f (x + y)‖ ^ 2 ∂ν := by
  obtain ⟨_, D, _, _, _, hD⟩ := poincareConvolution_test_bounds n f
  rw [poincareConvolutionAverage_gradient]
  apply poincareConvolution_integral_norm_sq_le ν
  apply MemLp.of_bound
    (((toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (f.contDiff.continuous_fderiv (by simp))).comp (by fun_prop)).aestronglyMeasurable D
  exact Eventually.of_forall fun x => hD _

end AffineFKProof
