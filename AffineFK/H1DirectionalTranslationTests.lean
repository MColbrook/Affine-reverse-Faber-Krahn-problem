module

public import AffineFK.H1DirectionalTranslationCalculus
public import AffineFK.BridgeGaussianL2Average
public import Mathlib.Probability.HasLaw

/-!
# The genuine Lebesgue L2 directional bound for compact smooth tests

Fubini is applied only after constructing the joint integrability from
translation invariance of the actual square directional derivative.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set InnerProductSpace TopologicalSpace
open scoped RealInnerProductSpace Distributions

theorem test_directional_translation_integral_sq_le (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (z : EuclideanSpace ℝ (Fin n)) :
    (∫ x, (φ (x + z) - φ x)^2) ≤
      ∫ x, (⟪z, gradient φ x⟫)^2 := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let d : E → ℝ := fun x => ⟪z, gradient φ x⟫
  have hgrad : MemLp (gradient φ) 2 (volume : Measure E) := by
    simpa only [testFunctionGradient_apply] using!
      ((testFunctionGradient φ).continuous.memLp_of_hasCompactSupport
        (testFunctionGradient φ).hasCompactSupport)
  have hd : MemLp d 2 volume := (toDual ℝ E z).comp_memLp' hgrad
  have hdi : Integrable (fun x => (d x)^2) volume :=
    (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mp hd
  have hgc : Continuous (gradient φ) :=
    (toDual ℝ E).symm.continuous.comp (φ.contDiff.continuous_fderiv (by simp))
  have hdc : Continuous d := continuous_const.inner hgc
  have hshift (t : ℝ) : Integrable (fun x => (d (x + t • z))^2) volume :=
    (measurePreserving_add_right volume (t • z)).integrable_comp_of_integrable hdi
  have heq (t : ℝ) : (∫ x, (d (x + t • z))^2) = ∫ x, (d x)^2 :=
    (measurePreserving_add_right volume (t • z)).hasLaw.integral_comp hdi.aestronglyMeasurable
  let F : E × ℝ → ℝ := fun p => (d (p.1 + p.2 • z))^2
  have hFm : AEStronglyMeasurable F (volume.prod μ) := by
    exact ((hdc.comp (by fun_prop)).pow 2).aestronglyMeasurable
  have hFn (t : ℝ) : (∫ x, ‖F (x,t)‖) = ∫ x, (d x)^2 := by
    calc
      _ = ∫ x, (d (x + t • z))^2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          exact Real.norm_of_nonneg (sq_nonneg _)
      _ = _ := heq t
  have hF : Integrable F (volume.prod μ) := by
    apply (integrable_prod_iff' hFm).mpr
    refine ⟨Filter.Eventually.of_forall hshift, ?_⟩
    exact (integrable_const (∫ x, (d x)^2)).congr
      (Filter.Eventually.of_forall fun t => (hFn t).symm)
  have hφ : MemLp (φ : E → ℝ) 2 volume :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hdiff : MemLp (fun x => φ (x+z) - φ x) 2 volume :=
    (hφ.comp_measurePreserving (measurePreserving_add_right volume z)).sub hφ
  have hdiffi : Integrable (fun x => (φ (x+z) - φ x)^2) volume :=
    (memLp_two_iff_integrable_sq hdiff.aestronglyMeasurable).mp hdiff
  calc
    _ ≤ ∫ x, ∫ t, F (x,t) ∂μ := by
      apply integral_mono hdiffi hF.integral_prod_left
      intro x
      simpa only [F, d, real_inner_comm] using!
        smooth_directional_translation_sq_le φ (φ.contDiff.of_le (by simp)) x z
    _ = ∫ t, ∫ x, F (x,t) ∂volume ∂μ := integral_integral_swap hF
    _ = ∫ x, (d x)^2 := by
      simp_rw [show ∀ t, (∫ x, F (x,t)) = ∫ x, (d x)^2 from heq]
      simp [μ, Real.volume_Icc]

end AffineFKProof
