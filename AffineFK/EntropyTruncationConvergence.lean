module

public import AffineFK.EntropyTruncationLimits
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Actual scalar limits of entropy truncations and their Fisher coefficients. -/

@[expose] public noncomputable section
namespace AffineFKProof
open Filter Set InformationTheory
open scoped Topology

theorem entropyShift_expanded (z r : ℝ) (hz : 1 + z ≠ 0) :
    entropyShift z r = (r + z) * Real.log (r + z) -
      (r + z) * Real.log (1 + z) - r + 1 := by
  by_cases h : r + z = 0
  · simp [entropyShift, h]
  · rw [entropyShift, Real.log_div h hz]
    ring

theorem entropyShift_tendsto_zero_parameter (r : ℝ) :
    Tendsto (fun z : ℝ => entropyShift z r) (𝓝 0) (𝓝 (klFun r)) := by
  have hc1 : Continuous (fun z : ℝ => (r + z) * Real.log (r + z)) :=
    Real.continuous_mul_log.comp (continuous_const.add continuous_id)
  have hc2 : ContinuousAt (fun z : ℝ => (r + z) * Real.log (1 + z)) 0 := by
    fun_prop (disch := norm_num)
  have h : ContinuousAt (fun z : ℝ => (r + z) * Real.log (r + z) -
      (r + z) * Real.log (1 + z) - r + 1) 0 :=
    ((hc1.continuousAt.sub hc2).sub (continuousAt_const (y := r))).add (continuousAt_const (y := (1 : ℝ)))
  have hlim : Tendsto (fun z : ℝ => (r + z) * Real.log (r + z) -
      (r + z) * Real.log (1 + z) - r + 1) (𝓝 0) (𝓝 (klFun r)) := by
    convert h.tendsto using 1 <;> simp [klFun] <;> ring
  apply hlim.congr'
  filter_upwards [eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)] with z hz
  exact (entropyShift_expanded z r (by linarith)).symm

theorem entropyShift_tendsto_atTop (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun z : ℝ => entropyShift z r) atTop (𝓝 0) := by
  have hden : Tendsto (fun z : ℝ => 1 + z) atTop atTop := by
    simpa only [id_eq, add_comm] using tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hu : Tendsto (fun z : ℝ => (r - 1) ^ 2 / (1 + z)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hden).const_mul ((r - 1) ^ 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0) from tendsto_const_nhds) hu
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    exact entropyShift_nonneg z r hz hr
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    exact entropyShift_quadratic_bound z r hz hr

/-- The actual entropy truncation with epsilon=1/(k+1) and L=k+1. -/
def entropyTruncationSequence (k : ℕ) (r : ℝ) : ℝ :=
  entropyTruncation (((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1) r

theorem entropyTruncationSequence_tendsto (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun k : ℕ => entropyTruncationSequence k r) atTop (𝓝 (klFun r)) := by
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun k : ℕ => entropyShift (((k : ℝ) + 1)⁻¹) r) atTop (𝓝 (klFun r)) :=
    (entropyShift_tendsto_zero_parameter r).comp (tendsto_inv_atTop_zero.comp hden)
  have hlarge : Tendsto (fun k : ℕ => entropyShift ((k : ℝ) + 1) r) atTop (𝓝 0) :=
    (entropyShift_tendsto_atTop r hr).comp hden
  change Tendsto (fun k : ℕ => entropyShift (((k : ℝ) + 1)⁻¹) r - entropyShift ((k : ℝ) + 1) r)
    atTop (𝓝 (klFun r))
  simpa only [sub_zero] using hsmall.sub hlarge

theorem entropyTruncationSequence_fisher_tendsto (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun k : ℕ => r ^ 2 *
      ((r + ((k : ℝ) + 1)⁻¹)⁻¹ - (r + ((k : ℝ) + 1))⁻¹)) atTop (𝓝 r) := by
  by_cases h0 : r = 0
  · simp [h0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm h0)
    have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hinv := tendsto_inv_atTop_zero.comp hden
    have hnear : Tendsto (fun k : ℕ => (r + ((k : ℝ) + 1)⁻¹)⁻¹) atTop (𝓝 r⁻¹) := by
      have hh : Tendsto (fun k : ℕ => r + ((k : ℝ) + 1)⁻¹) atTop (𝓝 r) := by
        simpa only [add_zero, Function.comp_def] using tendsto_const_nhds.add hinv
      exact hh.inv₀ h0
    have hfar : Tendsto (fun k : ℕ => (r + ((k : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (by
        simpa only [add_comm] using tendsto_atTop_add_const_right atTop r hden)
    have hlimit := (hnear.sub hfar).const_mul (r ^ 2)
    have heq : r ^ 2 * (r⁻¹ - 0) = r := by
      field_simp
      ring
    simpa only [heq] using hlimit

theorem entropyTruncationSequence_domain (k : ℕ) :
    0 < ((k : ℝ) + 1)⁻¹ ∧ ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 := by
  have hk : 1 ≤ (k : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  refine ⟨inv_pos.mpr hkpos, ?_⟩
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hkpos).mpr (by nlinarith)

theorem entropyTruncationSequence_fisher_weight_tendsto (r : ℝ) (hr : 0 < r) :
    Tendsto (fun k : ℕ => r *
      ((r + ((k : ℝ) + 1)⁻¹)⁻¹ - (r + ((k : ℝ) + 1))⁻¹)) atTop (𝓝 1) := by
  have h := (entropyTruncationSequence_fisher_tendsto r hr.le).const_mul r⁻¹
  have heq : (fun k : ℕ => r⁻¹ * (r ^ 2 *
      ((r + ((k : ℝ) + 1)⁻¹)⁻¹ - (r + ((k : ℝ) + 1))⁻¹))) =
      (fun k : ℕ => r * ((r + ((k : ℝ) + 1)⁻¹)⁻¹ - (r + ((k : ℝ) + 1))⁻¹)) := by
    funext k
    field_simp [hr.ne']
  rw [heq] at h
  simpa only [inv_mul_cancel₀ hr.ne'] using h

theorem entropyTruncationSequence_fisher_weight_bounds (k : ℕ) (r : ℝ) (hr : 0 < r) :
    0 ≤ r * ((r + ((k : ℝ) + 1)⁻¹)⁻¹ - (r + ((k : ℝ) + 1))⁻¹) ∧
      r * ((r + ((k : ℝ) + 1)⁻¹)⁻¹ - (r + ((k : ℝ) + 1))⁻¹) ≤ 1 := by
  have hd := entropyTruncationSequence_domain k
  have hb := entropyTruncation_fisher_coefficient (((k : ℝ) + 1)⁻¹) ((k : ℝ) + 1) r hd.1 hd.2 hr.le
  have heq : r⁻¹ * (r ^ 2 * ((r + ((k : ℝ) + 1)⁻¹)⁻¹ - (r + ((k : ℝ) + 1))⁻¹)) =
      r * ((r + ((k : ℝ) + 1)⁻¹)⁻¹ - (r + ((k : ℝ) + 1))⁻¹) := by
    field_simp [hr.ne']
  rw [← heq]
  exact ⟨mul_nonneg (inv_nonneg.mpr hr.le) hb.1, by
    simpa only [inv_mul_cancel₀ hr.ne'] using mul_le_mul_of_nonneg_left hb.2 (inv_nonneg.mpr hr.le)⟩

end AffineFKProof
