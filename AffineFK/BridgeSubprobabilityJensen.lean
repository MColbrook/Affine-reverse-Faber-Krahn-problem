module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Quadratic Jensen inequality for an actual subprobability measure

An elementary expansion of the nonnegative square avoids normalization by
the mass, so the zero measure is included without any separate convention.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory

theorem bridge_subprobability_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : μ Set.univ ≤ 1)
    (f : Ω → ℝ) (hf : MemLp f 2 μ) : (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  let c := ∫ x, f x ∂μ
  have hfi : Integrable f μ := hf.integrable (by norm_num)
  have hfs : Integrable (fun x => (f x)^2) μ := hf.integrable_sq
  have hm : μ.real Set.univ ≤ 1 := by
    exact (ENNReal.toReal_mono (by simp) hμ).trans_eq (by simp)
  have he : (∫ x, (f x-c)^2 ∂μ) = (∫ x, (f x)^2 ∂μ) - 2*c*c + c^2*μ.real Set.univ := by
    calc
      _ = ∫ x, ((f x)^2-(2*c)*f x)+c^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = _ := by
        have hsub : Integrable (fun x => (f x)^2-(2*c)*f x) μ := hfs.sub (hfi.const_mul (2*c))
        rw [integral_add hsub (integrable_const (c^2)),
          integral_sub hfs (hfi.const_mul (2*c)), integral_const_mul, integral_const]
        change (∫ x, (f x)^2 ∂μ) - 2*c*c + μ.real Set.univ * c^2 = _
        ring
  have hn : 0 ≤ (∫ x, (f x-c)^2 ∂μ) := integral_nonneg (fun x => sq_nonneg _)
  rw [he] at hn
  change c^2 ≤ _
  nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hm)]

end AffineFKProof
