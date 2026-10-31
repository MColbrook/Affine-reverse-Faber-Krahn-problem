module

public import AffineFK.OUDensityTimeDerivativeBounds
public import AffineFK.GaussianSmoothingRegularity

/-!
# Spatial continuity of the genuine OU time derivative

The derivative integral is dominated locally in the spatial parameter by
a constant times 1+norm(u). Only the original first moment is used.
The dominating derivative bound is the previously proved bound for the
actual Gaussian kernel, not an extra Gaussian assumption. Dominated
continuity reuses Mathlib's Bochner integral interface.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem ouDensityPDE_kernel_derivative_integral_continuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν) (a r d : ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ u, fderiv ℝ (standardGaussianDensity n) (r • (x - a • u))
        (r • (a • u) + d • (x - a • u)) ∂ν) := by
  let E := EuclideanSpace ℝ (Fin n)
  let F : E → E → ℝ := fun x u => fderiv ℝ (standardGaussianDensity n)
    (r • (x - a • u)) (r • (a • u) + d • (x - a • u))
  have hkD : Continuous (fderiv ℝ (standardGaussianDensity n)) :=
    ((standardGaussianDensity_smooth n).fderiv_right (m := 0) (by simp)).continuous
  have hFx (x : E) : Continuous (F x) := (hkD.comp (by fun_prop)).clm_apply (by fun_prop)
  have hFu (u : E) : Continuous (fun x => F x u) := (hkD.comp (by fun_prop)).clm_apply (by fun_prop)
  obtain ⟨K, hK, hKb⟩ := standardGaussianDensity_iteratedFDeriv_bound n 1
  have hKD (z : E) : ‖fderiv ℝ (standardGaussianDensity n) z‖ ≤ K := by
    simpa only [norm_iteratedFDeriv_one] using hKb z
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let M : ℝ := ‖x₀‖ + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hx₀ : ∀ᶠ x in 𝓝 x₀, ‖x‖ ≤ M := by
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds (lt_add_one ‖x₀‖))] with x hx
    exact hx.le
  let bound : E → ℝ := fun u => K * (‖r‖ * (‖a‖ * ‖u‖) + ‖d‖ * (M + ‖a‖ * ‖u‖))
  have hbint : Integrable bound ν :=
    (((hU.norm.const_mul ‖a‖).const_mul ‖r‖).add
      (((integrable_const M).add (hU.norm.const_mul ‖a‖)).const_mul ‖d‖)).const_mul K
  have hb : ∀ᶠ x in 𝓝 x₀, ∀ᵐ u ∂ν, ‖F x u‖ ≤ bound u := by
    filter_upwards [hx₀] with x hx
    exact Filter.Eventually.of_forall fun u => by
      have hxu : ‖x - a • u‖ ≤ M + ‖a‖ * ‖u‖ := by
        exact (norm_sub_le x (a • u)).trans (add_le_add hx (by rw [norm_smul]))
      have hv : ‖r • (a • u) + d • (x - a • u)‖ ≤
          ‖r‖ * (‖a‖ * ‖u‖) + ‖d‖ * (M + ‖a‖ * ‖u‖) := by
        calc
          _ ≤ ‖r • (a • u)‖ + ‖d • (x - a • u)‖ := norm_add_le _ _
          _ = ‖r‖ * (‖a‖ * ‖u‖) + ‖d‖ * ‖x - a • u‖ := by simp only [norm_smul]
          _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hxu (norm_nonneg _))
      exact ((fderiv ℝ (standardGaussianDensity n) (r • (x - a • u))).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (hKD _) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hv hK))
  exact continuousAt_of_dominated (Filter.Eventually.of_forall fun x => (hFx x).aestronglyMeasurable)
    hb hbint (Filter.Eventually.of_forall fun u => (hFu u).continuousAt)

theorem ou_density_time_derivative_continuous (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν) (t : ℝ) :
    Continuous (ouDensityTimeDerivative n ν t) := by
  let E := EuclideanSpace ℝ (Fin n)
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-2 * t))
  let r := b⁻¹
  let d := -(Real.exp (-2 * t) / b) / b ^ 2
  have hI0 : Continuous (fun x : E => ∫ u, standardGaussianDensity n (r • (x - a • u)) ∂ν) := by
    apply continuous_of_dominated (bound := fun _ : E => standardGaussianDensity n 0)
    · intro x
      exact ((standardGaussianDensity_smooth n).continuous.comp (by fun_prop)).aestronglyMeasurable
    · intro x
      exact Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_pos (standardGaussianDensity_pos n _)]
        exact gaussianSmoothingDensity_standard_le n _
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun u => (standardGaussianDensity_smooth n).continuous.comp (by fun_prop)
  exact (hI0.const_mul ((n : ℝ) * r ^ (n - 1) * d)).add
    ((ouDensityPDE_kernel_derivative_integral_continuous n ν hU a r d).const_mul (r ^ n))

end AffineFKProof
