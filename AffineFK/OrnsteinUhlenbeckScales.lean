module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The exact Ornstein--Uhlenbeck smoothing scales

For positive time, the actual exponential and square-root scales satisfy
the domain assumptions of the smoothing identities. These are scalar
identities, without a claim about logarithmic scores or entropy.

The proof uses Mathlib's real exponential power identities and square-root
theorems, with kernel-checked ordered-field and ring calculations.
-/

@[expose] public noncomputable section
namespace AffineFKProof

theorem ou_exponential_power (t : ℝ) (k : ℕ) :
    Real.exp (-t) ^ k = Real.exp (-(k : ℝ) * t) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem ou_smoothing_scale_domain (t : ℝ) (ht : 0 < t) :
    0 < Real.exp (-t) ∧
    0 < Real.sqrt (1 - Real.exp (-2 * t)) ∧
    Real.exp (-t) ^ 2 + Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 = 1 := by
  have hden : 0 < 1 - Real.exp (-2 * t) := by
    have he : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  refine ⟨Real.exp_pos _, Real.sqrt_pos.mpr hden, ?_⟩
  rw [ou_exponential_power, Real.sq_sqrt hden.le]
  simp

theorem ou_smoothing_scale_coefficients (t : ℝ) (ht : 0 < t) :
    Real.exp (-t) ^ 3 / Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 =
      Real.exp (-3 * t) / (1 - Real.exp (-2 * t)) ∧
    2 * Real.exp (-t) ^ 6 / Real.sqrt (1 - Real.exp (-2 * t)) ^ 4 =
      2 * Real.exp (-6 * t) / (1 - Real.exp (-2 * t)) ^ 2 := by
  have hden : 0 ≤ 1 - Real.exp (-2 * t) := by
    have he : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hs := Real.sq_sqrt hden
  have hfour : Real.sqrt (1 - Real.exp (-2 * t)) ^ 4 = (1 - Real.exp (-2 * t)) ^ 2 := by
    calc
      _ = (Real.sqrt (1 - Real.exp (-2 * t)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hs]
  constructor
  · rw [ou_exponential_power, hs]
    norm_num
  · rw [ou_exponential_power, hfour]
    norm_num

end AffineFKProof
