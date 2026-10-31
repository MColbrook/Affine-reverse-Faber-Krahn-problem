module

public import AffineFK.OUDensityPDEJointContinuity
public import AffineFK.OUDensityPDEScore
public import AffineFK.GaussianHessianL2Calculus

/-!
# Joint continuity of the positive-time score and its actual time derivative

Every integral below is the actual Gaussian kernel derivative. Dominated
continuity uses the proved Gaussian derivative bounds and only the
initial first moment. These statements supply compact parameter bounds;
they do not assume or conclude a global Fisher dissipation identity.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff

theorem ou_density_time_derivative_joint_continuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν) :
    Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) =>
      ouDensityTimeDerivative n ν p.1.val p.2) := by
  let P := {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n)
  let a : P → ℝ := fun p => Real.exp (-p.1.val)
  let b : P → ℝ := fun p => Real.sqrt (1 - Real.exp (-2 * p.1.val))
  let r : P → ℝ := fun p => (b p)⁻¹
  let d : P → ℝ := fun p => -(Real.exp (-2 * p.1.val) / b p) / (b p) ^ 2
  have ha : Continuous a := by dsimp [P, a]; fun_prop
  have hb : Continuous b := by dsimp [P, b]; fun_prop
  have hne (p : P) : b p ≠ 0 := (ou_smoothing_scale_domain p.1.val p.1.property).2.1.ne'
  have hr : Continuous r := hb.inv₀ hne
  have he : Continuous (fun p : P => Real.exp (-2 * p.1.val)) := by dsimp [P]; fun_prop
  have hd : Continuous d := (he.div hb hne).neg.div (hb.pow 2) (fun p => pow_ne_zero _ (hne p))
  have hI₀ := ouDensityPDE_bounded_kernel_parameter_integral_continuous n ν
    (standardGaussianDensity n) (standardGaussianDensity_smooth n).continuous
    (standardGaussianDensity n 0) (fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (standardGaussianDensity_pos n y)]
      exact gaussianSmoothingDensity_standard_le n y)
    a r (fun p : P => p.2) ha hr continuous_snd
  obtain ⟨C, hC, hCb⟩ := standardGaussianDensity_iteratedFDeriv_bound n 1
  have hI₁ := ouDensityPDE_linear_kernel_parameter_integral_continuous n ν hU
    (fderiv ℝ (standardGaussianDensity n))
    ((standardGaussianDensity_smooth n).fderiv_right (m := 0) (by simp)).continuous
    C hC (fun y => by simpa only [norm_iteratedFDeriv_one] using hCb y)
    a r d (fun p : P => p.2) ha hr hd continuous_snd
  exact (((continuous_const.mul (hr.pow (n - 1))).mul hd).mul hI₀).add ((hr.pow n).mul hI₁)

theorem ou_density_gradient_time_derivative_joint_continuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν) :
    Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) =>
      ouDensityGradientTimeDerivative n ν p.1.val p.2) := by
  let P := {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n)
  let a : P → ℝ := fun p => Real.exp (-p.1.val)
  let b : P → ℝ := fun p => Real.sqrt (1 - Real.exp (-2 * p.1.val))
  let r : P → ℝ := fun p => (b p)⁻¹
  let d : P → ℝ := fun p => -(Real.exp (-2 * p.1.val) / b p) / (b p) ^ 2
  have ha : Continuous a := by dsimp [P, a]; fun_prop
  have hb : Continuous b := by dsimp [P, b]; fun_prop
  have hne (p : P) : b p ≠ 0 := (ou_smoothing_scale_domain p.1.val p.1.property).2.1.ne'
  have hr : Continuous r := hb.inv₀ hne
  have he : Continuous (fun p : P => Real.exp (-2 * p.1.val)) := by dsimp [P]; fun_prop
  have hd : Continuous d := (he.div hb hne).neg.div (hb.pow 2) (fun p => pow_ne_zero _ (hne p))
  obtain ⟨C₁, _, hC₁⟩ := standardGaussianDensity_iteratedFDeriv_bound n 1
  obtain ⟨C₂, hC₂, hC₂b⟩ := standardGaussianDensity_iteratedFDeriv_bound n 2
  have hk₁ : ContDiff ℝ ∞ (fderiv ℝ (standardGaussianDensity n)) :=
    (standardGaussianDensity_smooth n).fderiv_right (by simp)
  have hk₂ : Continuous (fderiv ℝ (fderiv ℝ (standardGaussianDensity n))) :=
    (hk₁.fderiv_right (m := 0) (by simp)).continuous
  have hI₀ := ouDensityPDE_bounded_kernel_parameter_integral_continuous n ν
    (fderiv ℝ (standardGaussianDensity n)) hk₁.continuous C₁
    (fun y => by simpa only [norm_iteratedFDeriv_one] using hC₁ y)
    a r (fun p : P => p.2) ha hr continuous_snd
  have hI₁ := ouDensityPDE_linear_kernel_parameter_integral_continuous n ν hU
    (fderiv ℝ (fderiv ℝ (standardGaussianDensity n))) hk₂ C₂ hC₂
    (fun y => by
      have h := hC₂b y
      rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h
      exact h)
    a r d (fun p : P => p.2) ha hr hd continuous_snd
  exact (((continuous_const.mul (hr.pow n)).mul hd).smul hI₀).add ((hr.pow (n + 1)).smul hI₁)

theorem ou_ordinary_score_coordinate_joint_continuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] (i : Fin n) :
    Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) =>
      gradient (fun x => Real.log (gaussianSmoothingDensity n ν (Real.exp (-p.1.val))
        (Real.sqrt (1 - Real.exp (-2 * p.1.val))) x)) p.2 i) := by
  have hρ := ou_density_joint_continuous n ν
  have hD := (ou_density_fderiv_joint_continuous n ν).clm_apply
    (g := fun _ => EuclideanSpace.basisFun (Fin n) ℝ i) continuous_const
  have hpos (p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n)) :=
    gaussianSmoothingDensity_pos n ν (Real.exp (-p.1.val))
      (Real.sqrt (1 - Real.exp (-2 * p.1.val)))
      (ou_smoothing_scale_domain p.1.val p.1.property).2.1 p.2
  have h := (hρ.inv₀ fun p => (hpos p).ne').mul hD
  convert! h using 1
  funext p
  exact log_density_gradient_coordinate n _ (gaussianSmoothingDensity_smooth n ν _ _)
    (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain p.1.val p.1.property).2.1) p.2 i

theorem ou_ordinary_fisher_density_joint_continuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] :
    Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) =>
      ‖gradient (fun x => Real.log (gaussianSmoothingDensity n ν (Real.exp (-p.1.val))
        (Real.sqrt (1 - Real.exp (-2 * p.1.val))) x)) p.2‖ ^ 2 *
      gaussianSmoothingDensity n ν (Real.exp (-p.1.val))
        (Real.sqrt (1 - Real.exp (-2 * p.1.val))) p.2) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact (continuous_finsetSum Finset.univ fun i _ =>
    (ou_ordinary_score_coordinate_joint_continuous n ν i).pow 2).mul (ou_density_joint_continuous n ν)

theorem ou_ordinary_score_time_derivative_joint_continuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν) (i : Fin n) :
    Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) =>
      ouOrdinaryScoreTimeDerivative n ν p.1.val p.2 i) := by
  have hρ := ou_density_joint_continuous n ν
  have hD := (ou_density_fderiv_joint_continuous n ν).clm_apply
    (g := fun _ => EuclideanSpace.basisFun (Fin n) ℝ i) continuous_const
  have hDt := ou_density_time_derivative_joint_continuous n ν hU
  have hDDt := (ou_density_gradient_time_derivative_joint_continuous n ν hU).clm_apply
    (g := fun _ => EuclideanSpace.basisFun (Fin n) ℝ i) continuous_const
  exact ((hDDt.mul hρ).sub (hD.mul hDt)).div (hρ.pow 2) fun p =>
    pow_ne_zero _ (gaussianSmoothingDensity_pos n ν _ _
      (ou_smoothing_scale_domain p.1.val p.1.property).2.1 p.2).ne'

theorem ou_ordinary_fisher_density_time_derivative_joint_continuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν) :
    Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) =>
      let ρ := gaussianSmoothingDensity n ν (Real.exp (-p.1.val))
        (Real.sqrt (1 - Real.exp (-2 * p.1.val)))
      let s := gradient (fun x => Real.log (ρ x)) p.2
      2 * (∑ i : Fin n, s i * ouOrdinaryScoreTimeDerivative n ν p.1.val p.2 i) * ρ p.2 +
        ‖s‖ ^ 2 * ouDensityTimeDerivative n ν p.1.val p.2) := by
  dsimp only
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  exact ((continuous_const.mul (continuous_finsetSum Finset.univ fun i _ =>
    (ou_ordinary_score_coordinate_joint_continuous n ν i).mul
      (ou_ordinary_score_time_derivative_joint_continuous n ν hU i))).mul
        (ou_density_joint_continuous n ν)).add
    ((continuous_finsetSum Finset.univ fun i _ =>
      (ou_ordinary_score_coordinate_joint_continuous n ν i).pow 2).mul
        (ou_density_time_derivative_joint_continuous n ν hU))

theorem ou_logHessian_entry_joint_measurable (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] (i j : Fin n) :
    Measurable (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) =>
      densityLogHessian n (gaussianSmoothingDensity n ν (Real.exp (-p.1.val))
        (Real.sqrt (1 - Real.exp (-2 * p.1.val)))) p.2 i j) := by
  let f : {t : ℝ // 0 < t} → EuclideanSpace ℝ (Fin n) → ℝ := fun t x =>
    gradient (fun y => Real.log (gaussianSmoothingDensity n ν (Real.exp (-t.val))
      (Real.sqrt (1 - Real.exp (-2 * t.val))) y)) x i
  have hf : Continuous f.uncurry := ou_ordinary_score_coordinate_joint_continuous n ν i
  have h := measurable_fderiv_apply_const_with_param (f := f) ℝ hf
    (EuclideanSpace.basisFun (Fin n) ℝ j)
  convert! h using 1
  funext p
  exact gradient_coordinate_eq_fderiv n _ p.2 j

end AffineFKProof
