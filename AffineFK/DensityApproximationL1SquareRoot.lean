module

public import AffineFK.WeightedSobolev
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith

/-!
# Actual L1 density convergence gives L2 square-root convergence

The elementary nonnegative square-root inequality is proved over the
real numbers, then integrated with genuine L1 and L2 witnesses. No
assumed density-approximation or Sobolev conclusion is used.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter
open scoped Topology

theorem densityApproximation_sqrt_difference_sq_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  by_cases hab : a ≤ b
  · have hroot := Real.sqrt_le_sqrt hab
    have hprod := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg a)
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    have hroot := Real.sqrt_le_sqrt hba
    have hprod := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg b)
    rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    nlinarith

theorem densityApproximation_sqrt_memLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ρ : X → ℝ) (hm : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂μ, 0 ≤ ρ x) (hρ : Integrable ρ μ) :
    MemLp (fun x => Real.sqrt (ρ x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hm.sqrt.aestronglyMeasurable).mpr
  apply hρ.congr
  filter_upwards [hρ0] with x hx
  simp only [Real.norm_eq_abs, sq_abs, Real.sq_sqrt hx]

theorem densityApproximation_sqrt_L2_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ρk : ℕ → X → ℝ) (ρ : X → ℝ)
    (hρk0 : ∀ k, ∀ᵐ x ∂μ, 0 ≤ ρk k x) (hρ0 : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hρk : ∀ k, Integrable (ρk k) μ) (hρ : Integrable ρ μ)
    (v : ℕ → Lp ℝ 2 μ) (w : Lp ℝ 2 μ)
    (hv : ∀ k, v k =ᵐ[μ] fun x => Real.sqrt (ρk k x))
    (hw : w =ᵐ[μ] fun x => Real.sqrt (ρ x))
    (hL1 : Tendsto (fun k => ∫ x, ‖ρk k x - ρ x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 w) := by
  have hbound (k : ℕ) : ‖v k - w‖ ^ 2 ≤ ∫ x, ‖ρk k x - ρ x‖ ∂μ := by
    rw [l2_norm_sq_integral]
    have hsub := Lp.memLp (v k - w)
    apply integral_mono_ae
      ((memLp_two_iff_integrable_sq_norm hsub.aestronglyMeasurable).mp hsub)
      ((hρk k).sub hρ).norm
    filter_upwards [Lp.coeFn_sub (v k) w, hv k, hw, hρk0 k, hρ0]
      with x hsubx hvx hwx hk0 h0
    rw [hsubx]
    simp only [Pi.sub_apply, hvx, hwx, Real.norm_eq_abs, sq_abs]
    exact densityApproximation_sqrt_difference_sq_le _ _ hk0 h0
  have hsquare : Tendsto (fun k => ‖v k - w‖ ^ 2) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun k => sq_nonneg _) hbound hL1
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

end AffineFKProof
