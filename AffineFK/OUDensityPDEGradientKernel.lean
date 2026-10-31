module

public import AffineFK.OUDensityTimeKernel

/-!
# Differentiating bounded smooth kernels along the actual OU scales

This extends the genuine dominated-differentiation proof of
ou_gaussian_kernel_integral_hasDerivAt from OUDensityTimeKernel to a
Banach-valued smooth kernel. That earlier project proof is reused with
attribution to its OU-entropy branch author. Patrick Massot's Mathlib
parametric-integral theorem performs the actual interchange. The bound
uses only the original first moment, not higher moments.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff

theorem ouDensityPDE_smooth_kernel_integral_hasDerivAt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (f : EuclideanSpace ℝ (Fin n) → H) (hf : ContDiff ℝ ∞ f)
    (C₀ C₁ : ℝ) (hC₀ : ∀ y, ‖f y‖ ≤ C₀) (hC₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ C₁)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : 0 < t) :
    let a := Real.exp (-t)
    let b := Real.sqrt (1 - Real.exp (-2 * t))
    let r := b⁻¹
    let dr := -(Real.exp (-2 * t) / b) / b ^ 2
    Integrable (fun u => fderiv ℝ f (r • (x - a • u))
      (r • (a • u) + dr • (x - a • u))) ν ∧
    HasDerivAt (fun s : ℝ => ∫ u, f
      ((Real.sqrt (1 - Real.exp (-2 * s)))⁻¹ • (x - Real.exp (-s) • u)) ∂ν)
      (∫ u, fderiv ℝ f (r • (x - a • u))
        (r • (a • u) + dr • (x - a • u)) ∂ν) t := by
  let E := EuclideanSpace ℝ (Fin n)
  let a : ℝ → ℝ := fun s => Real.exp (-s)
  let b : ℝ → ℝ := fun s => Real.sqrt (1 - Real.exp (-2 * s))
  let r : ℝ → ℝ := fun s => (b s)⁻¹
  let dr : ℝ → ℝ := fun s => -(Real.exp (-2 * s) / b s) / (b s) ^ 2
  let z : ℝ → E → E := fun s u => r s • (x - a s • u)
  let dz : ℝ → E → E := fun s u => r s • (a s • u) + dr s • (x - a s • u)
  let F : ℝ → E → H := fun s u => f (z s u)
  let F' : ℝ → E → H := fun s u => fderiv ℝ f (z s u) (dz s u)
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hb : Continuous b := by dsimp [b]; fun_prop
  have hr : ContinuousAt r t := hb.continuousAt.inv₀ (ou_smoothing_scale_domain t ht).2.1.ne'
  have hdr : ContinuousAt dr t := by
    dsimp [dr]
    exact ((by fun_prop : Continuous (fun s : ℝ => Real.exp (-2 * s))).continuousAt.div
      hb.continuousAt (ou_smoothing_scale_domain t ht).2.1.ne').neg.div
        (hb.continuousAt.pow 2) (pow_ne_zero _ (ou_smoothing_scale_domain t ht).2.1.ne')
  let A := ‖a t‖ + 1
  let R := ‖r t‖ + 1
  let D := ‖dr t‖ + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hAn : ∀ᶠ s in 𝓝 t, ‖a s‖ < A := ha.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖a t‖))
  have hRn : ∀ᶠ s in 𝓝 t, ‖r s‖ < R := hr.norm.eventually (gt_mem_nhds (lt_add_one ‖r t‖))
  have hDn : ∀ᶠ s in 𝓝 t, ‖dr s‖ < D := hdr.norm.eventually (gt_mem_nhds (lt_add_one ‖dr t‖))
  let S : Set ℝ := {s | 0 < s ∧ ‖a s‖ ≤ A ∧ ‖r s‖ ≤ R ∧ ‖dr s‖ ≤ D}
  have hS : S ∈ 𝓝 t := by
    filter_upwards [lt_mem_nhds ht, hAn, hRn, hDn] with s hs has hrs hds
    exact ⟨hs, has.le, hrs.le, hds.le⟩
  have hC : 0 ≤ C₁ := (norm_nonneg (fderiv ℝ f 0)).trans (hC₁ 0)
  let bound : E → ℝ := fun u => C₁ * (R * A * ‖u‖ + D * (‖x‖ + A * ‖u‖))
  have hbint : Integrable bound ν :=
    ((hU.norm.const_mul (R * A)).add
      (((integrable_const ‖x‖).add (hU.norm.const_mul A)).const_mul D)).const_mul C₁
  have hz (s : ℝ) : Continuous (z s) := by dsimp [z]; fun_prop
  have hdz (s : ℝ) : Continuous (dz s) := by dsimp [dz]; fun_prop
  have hkD : Continuous (fderiv ℝ f) := ((hf.fderiv_right (m := 0) (by simp))).continuous
  have hFm (s : ℝ) : AEStronglyMeasurable (F s) ν := (hf.continuous.comp (hz s)).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable (F' t) ν := ((hkD.comp (hz t)).clm_apply (hdz t)).aestronglyMeasurable
  have hFt : Integrable (F t) ν := by
    apply (integrable_const C₀).mono' (hFm t)
    exact Filter.Eventually.of_forall fun u => hC₀ _
  have hbound : ∀ᵐ u ∂ν, ∀ s ∈ S, ‖F' s u‖ ≤ bound u := by
    exact Filter.Eventually.of_forall fun u s hs => by
      have hau : ‖a s • u‖ ≤ A * ‖u‖ := by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right hs.2.1 (norm_nonneg _)
      have hdiff : ‖x - a s • u‖ ≤ ‖x‖ + A * ‖u‖ := (norm_sub_le _ _).trans (add_le_add le_rfl hau)
      have hv : ‖dz s u‖ ≤ R * A * ‖u‖ + D * (‖x‖ + A * ‖u‖) := by
        calc
          ‖dz s u‖ ≤ ‖r s • (a s • u)‖ + ‖dr s • (x - a s • u)‖ := norm_add_le _ _
          _ = ‖r s‖ * ‖a s • u‖ + ‖dr s‖ * ‖x - a s • u‖ := by simp only [norm_smul]
          _ ≤ R * (A * ‖u‖) + D * (‖x‖ + A * ‖u‖) :=
            add_le_add (mul_le_mul hs.2.2.1 hau (norm_nonneg _) hR)
              (mul_le_mul hs.2.2.2 hdiff (norm_nonneg _) hD)
          _ = _ := by ring
      exact ((fderiv ℝ f (z s u)).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (hC₁ _) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hv hC))
  have hdiff : ∀ᵐ u ∂ν, ∀ s ∈ S, HasDerivAt (F · u) (F' s u) s := by
    exact Filter.Eventually.of_forall fun u s hs => by
      have hk := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z s u)
      simpa only [Function.comp_def, F, F', z, dz, a, b, r, dr] using
        hk.comp_hasDerivAt s (ou_standardized_curve_hasDerivAt n x u s hs.1)
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Filter.Eventually.of_forall hFm) hFt hF'm hbound hbint hdiff

end AffineFKProof
