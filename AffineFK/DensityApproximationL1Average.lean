module

public import AffineFK.DensityApproximationL1Translation
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic.Linarith

/-!
# L1 control of actual translated averages

Haar translation preserves the L1 norm. Averaging the actual translation
error against any probability therefore has dominator twice that norm,
and tends to zero without any moment assumption on the averaging law.
The primary Bochner/Fubini/DCT results retain their Mathlib attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter
open scoped Topology

theorem densityApproximation_translation_L1_bound (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Integrable f (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (y : EuclideanSpace ℝ (Fin n)) :
    (∫ x, ‖f (x - y) - f x‖) ≤ 2 * ∫ x, ‖f x‖ := by
  have hs : Integrable (fun x => f (x - y)) volume :=
    (densityApproximationTranslation_measurePreserving n y).integrable_comp_of_integrable hf
  have h := integral_mono_ae (hs.sub hf).norm (hs.norm.add hf.norm)
    (Eventually.of_forall fun x => norm_sub_le (f (x - y)) (f x))
  simp only [Pi.sub_apply, Pi.add_apply] at h
  rw [integral_add hs.norm hf.norm, integral_sub_right_eq_self (fun x => ‖f x‖) y] at h
  linarith

theorem densityApproximation_average_kernel_integrable (n : ℕ)
    (η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure η]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable f)
    (hf : Integrable f (volume : Measure (EuclideanSpace ℝ (Fin n)))) (b : ℝ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      f (p.2 - b • p.1)) (η.prod volume) := by
  have harg : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      p.2 - b • p.1) := by fun_prop
  have hF : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => f (p.2 - b • p.1))
      (η.prod volume) := (hm.comp harg).aestronglyMeasurable
  apply (integrable_prod_iff hF).mpr
  refine ⟨Eventually.of_forall fun g =>
    (densityApproximationTranslation_measurePreserving n (b • g)).integrable_comp_of_integrable hf, ?_⟩
  have heq : (fun g : EuclideanSpace ℝ (Fin n) => ∫ x, ‖f (x - b • g)‖) =
      fun _ => ∫ x, ‖f x‖ := by
    funext g
    exact integral_sub_right_eq_self (fun x => ‖f x‖) (b • g)
  rw [heq]
  exact integrable_const _

theorem densityApproximation_averaged_translation_L1_tendsto (n : ℕ)
    (η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure η]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable f)
    (hf : Integrable f (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Tendsto (fun b : ℝ => ∫ g, (∫ x, ‖f (x - b • g) - f x‖) ∂η) (𝓝 0) (𝓝 0) := by
  have hmeas (b : ℝ) : StronglyMeasurable
      (fun g : EuclideanSpace ℝ (Fin n) => ∫ x, ‖f (x - b • g) - f x‖) := by
    have harg : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        p.2 - b • p.1) := by fun_prop
    have hF : StronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ‖f (p.2 - b • p.1) - f p.2‖) :=
      (((hm.comp harg).sub (hm.comp measurable_snd)).norm).stronglyMeasurable
    exact hF.integral_prod_right'
  have hbound (b : ℝ) : ∀ᵐ g ∂η,
      ‖∫ x, ‖f (x - b • g) - f x‖‖ ≤ 2 * ∫ x, ‖f x‖ := by
    exact Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
      exact densityApproximation_translation_L1_bound n f hf (b • g)
  have hpoint : ∀ᵐ g ∂η, Tendsto
      (fun b : ℝ => ∫ x, ‖f (x - b • g) - f x‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
    exact Eventually.of_forall fun g => by
      have hg : Tendsto (fun b : ℝ => b • g) (𝓝 0) (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
        simpa only [zero_smul] using
          (show Continuous (fun b : ℝ => b • g) from by fun_prop).tendsto (0 : ℝ)
      exact (densityApproximation_translation_L1_tendsto n f hf).comp hg
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := η) (l := 𝓝 (0 : ℝ))
    (F := fun b g => ∫ x, ‖f (x - b • g) - f x‖) (f := fun _ => (0 : ℝ))
    (fun _ : EuclideanSpace ℝ (Fin n) => 2 * ∫ x, ‖f x‖)
    (Eventually.of_forall fun b => (hmeas b).aestronglyMeasurable)
    (Eventually.of_forall hbound) (integrable_const _) hpoint
  simpa only [integral_zero] using h

end AffineFKProof
