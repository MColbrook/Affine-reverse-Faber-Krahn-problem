module

public import AffineFK.OUDensityPDEGradient
public import AffineFK.GaussianSmoothedScoreHessianSymmetry
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Joint continuity of the actual positive-time OU density derivatives

Uniform bounds for the genuine Gaussian derivatives give dominated
continuity with arbitrary continuous parameters. The time-derivative
integrals have a local majorant proportional to 1+norm(u), so only the
original first moment is needed. The Bochner dominated-continuity and
parametric derivative-measurability results are reused from Mathlib,
with the attribution in their primary modules retained.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

theorem ouDensityPDE_bounded_kernel_parameter_integral_continuous
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν]
    {P H : Type*} [TopologicalSpace P] [FirstCountableTopology P] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : EuclideanSpace ℝ (Fin n) → H) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C)
    (a r : P → ℝ) (x : P → EuclideanSpace ℝ (Fin n))
    (ha : Continuous a) (hr : Continuous r) (hx : Continuous x) :
    Continuous (fun p => ∫ u, f (r p • (x p - a p • u)) ∂ν) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro p
    exact (hf.comp (by fun_prop)).aestronglyMeasurable
  · intro p
    exact Filter.Eventually.of_forall fun u => hC _
  · exact integrable_const C
  · exact Filter.Eventually.of_forall fun u => hf.comp (by fun_prop)

theorem ouDensityPDE_linear_kernel_parameter_integral_continuous
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    {P H : Type*} [TopologicalSpace P] [FirstCountableTopology P] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] H)
    (hG : Continuous G) (C : ℝ) (hC : 0 ≤ C) (hGb : ∀ y, ‖G y‖ ≤ C)
    (a r d : P → ℝ) (x : P → EuclideanSpace ℝ (Fin n))
    (ha : Continuous a) (hr : Continuous r) (hd : Continuous d) (hx : Continuous x) :
    Continuous (fun p => ∫ u, G (r p • (x p - a p • u))
      (r p • (a p • u) + d p • (x p - a p • u)) ∂ν) := by
  let E := EuclideanSpace ℝ (Fin n)
  let F : P → E → H := fun p u => G (r p • (x p - a p • u))
    (r p • (a p • u) + d p • (x p - a p • u))
  have hFp (p : P) : Continuous (F p) := (hG.comp (by fun_prop)).clm_apply (by fun_prop)
  have hFu (u : E) : Continuous (fun p => F p u) := (hG.comp (by fun_prop)).clm_apply (by fun_prop)
  apply continuous_iff_continuousAt.mpr
  intro p₀
  let A := ‖a p₀‖ + 1
  let R := ‖r p₀‖ + 1
  let D := ‖d p₀‖ + 1
  let M := ‖x p₀‖ + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hAn : ∀ᶠ p in 𝓝 p₀, ‖a p‖ ≤ A :=
    (ha.norm.continuousAt.eventually (gt_mem_nhds (lt_add_one ‖a p₀‖))).mono fun _ h => h.le
  have hRn : ∀ᶠ p in 𝓝 p₀, ‖r p‖ ≤ R :=
    (hr.norm.continuousAt.eventually (gt_mem_nhds (lt_add_one ‖r p₀‖))).mono fun _ h => h.le
  have hDn : ∀ᶠ p in 𝓝 p₀, ‖d p‖ ≤ D :=
    (hd.norm.continuousAt.eventually (gt_mem_nhds (lt_add_one ‖d p₀‖))).mono fun _ h => h.le
  have hMn : ∀ᶠ p in 𝓝 p₀, ‖x p‖ ≤ M :=
    (hx.norm.continuousAt.eventually (gt_mem_nhds (lt_add_one ‖x p₀‖))).mono fun _ h => h.le
  let bound : E → ℝ := fun u => C * (R * (A * ‖u‖) + D * (M + A * ‖u‖))
  have hbint : Integrable bound ν :=
    (((hU.norm.const_mul A).const_mul R).add
      (((integrable_const M).add (hU.norm.const_mul A)).const_mul D)).const_mul C
  have hb : ∀ᶠ p in 𝓝 p₀, ∀ᵐ u ∂ν, ‖F p u‖ ≤ bound u := by
    filter_upwards [hAn, hRn, hDn, hMn] with p hap hrp hdp hxp
    exact Filter.Eventually.of_forall fun u => by
      have hau : ‖a p • u‖ ≤ A * ‖u‖ := by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right hap (norm_nonneg _)
      have hxu : ‖x p - a p • u‖ ≤ M + A * ‖u‖ :=
        (norm_sub_le _ _).trans (add_le_add hxp hau)
      have hv : ‖r p • (a p • u) + d p • (x p - a p • u)‖ ≤
          R * (A * ‖u‖) + D * (M + A * ‖u‖) := by
        calc
          _ ≤ ‖r p • (a p • u)‖ + ‖d p • (x p - a p • u)‖ := norm_add_le _ _
          _ = ‖r p‖ * ‖a p • u‖ + ‖d p‖ * ‖x p - a p • u‖ := by simp only [norm_smul]
          _ ≤ _ := add_le_add (mul_le_mul hrp hau (norm_nonneg _) hR)
            (mul_le_mul hdp hxu (norm_nonneg _) hD)
      exact ((G _).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (hGb _) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hv hC))
  exact continuousAt_of_dominated
    (Filter.Eventually.of_forall fun p => (hFp p).aestronglyMeasurable) hb hbint
    (Filter.Eventually.of_forall fun u => (hFu u).continuousAt)

theorem ou_density_joint_continuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] :
    Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) =>
      gaussianSmoothingDensity n ν (Real.exp (-p.1.val))
        (Real.sqrt (1 - Real.exp (-2 * p.1.val))) p.2) := by
  let P := {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n)
  let a : P → ℝ := fun p => Real.exp (-p.1.val)
  let b : P → ℝ := fun p => Real.sqrt (1 - Real.exp (-2 * p.1.val))
  let r : P → ℝ := fun p => (b p)⁻¹
  have ha : Continuous a := by dsimp [P, a]; fun_prop
  have hb : Continuous b := by dsimp [P, b]; fun_prop
  have hr : Continuous r := hb.inv₀ fun p => (ou_smoothing_scale_domain p.1.val p.1.property).2.1.ne'
  have hI := ouDensityPDE_bounded_kernel_parameter_integral_continuous n ν
    (standardGaussianDensity n) (standardGaussianDensity_smooth n).continuous
    (standardGaussianDensity n 0) (fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (standardGaussianDensity_pos n y)]
      exact gaussianSmoothingDensity_standard_le n y)
    a r (fun p : P => p.2) ha hr continuous_snd
  exact ((hb.pow n).inv₀
    (fun p => pow_ne_zero _ (ou_smoothing_scale_domain p.1.val p.1.property).2.1.ne')).mul hI

theorem ou_density_fderiv_joint_continuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] :
    Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ (gaussianSmoothingDensity n ν (Real.exp (-p.1.val))
        (Real.sqrt (1 - Real.exp (-2 * p.1.val)))) p.2) := by
  let P := {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n)
  let a : P → ℝ := fun p => Real.exp (-p.1.val)
  let b : P → ℝ := fun p => Real.sqrt (1 - Real.exp (-2 * p.1.val))
  let r : P → ℝ := fun p => (b p)⁻¹
  have ha : Continuous a := by dsimp [P, a]; fun_prop
  have hb : Continuous b := by dsimp [P, b]; fun_prop
  have hr : Continuous r := hb.inv₀ fun p => (ou_smoothing_scale_domain p.1.val p.1.property).2.1.ne'
  obtain ⟨C, _, hC⟩ := standardGaussianDensity_iteratedFDeriv_bound n 1
  have hI := ouDensityPDE_bounded_kernel_parameter_integral_continuous n ν
    (fderiv ℝ (standardGaussianDensity n))
    ((standardGaussianDensity_smooth n).fderiv_right (m := 0) (by simp)).continuous
    C (fun y => by simpa only [norm_iteratedFDeriv_one] using hC y)
    a r (fun p : P => p.2) ha hr continuous_snd
  have heq : (fun p : P => fderiv ℝ (gaussianSmoothingDensity n ν (a p) (b p)) p.2) =
      fun p => (r p) ^ (n + 1) •
        ∫ u, fderiv ℝ (standardGaussianDensity n) (r p • (p.2 - a p • u)) ∂ν := by
    funext p
    exact gaussianSmoothingDensity_fderiv_eq_integral n ν (a p) (b p) p.2
  change Continuous (fun p : P => fderiv ℝ (gaussianSmoothingDensity n ν (a p) (b p)) p.2)
  rw [heq]
  exact (hr.pow _).smul hI

end AffineFKProof
