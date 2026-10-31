module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Finite logarithmic slope estimates

The telescope uses only the explicitly stated finite second differences,
so an application to a killed diagonal needs positivity only on its finite
time grid. The elementary logarithm estimate is Mathlib's proved log bound.
-/

@[expose] public noncomputable section
namespace AffineFKProof

theorem bridge_sequence_slope_telescope (ℓ : ℕ → ℝ) : ∀ m : ℕ,
    (∀ k < m, 0 ≤ ℓ k - 2*ℓ (k+1) + ℓ (k+2)) →
      (m : ℝ) * (ℓ m - ℓ (m+1)) ≤ ℓ 0 - ℓ m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hconv
    have hp := ih (fun k hk => hconv k (Nat.lt_trans hk (Nat.lt_succ_self m)))
    have hs := hconv m (Nat.lt_succ_self m)
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have hs' : ℓ (m+1) - ℓ (m+1+1) ≤ ℓ m - ℓ (m+1) := by
      simpa only [Nat.add_assoc] using (by linarith : ℓ (m+1)-ℓ (m+2) ≤ ℓ m-ℓ (m+1))
    have hmul := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ (m : ℝ)+1)
    norm_num only [Nat.cast_add, Nat.cast_one] at *
    nlinarith

theorem bridge_positive_sub_le_log (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a-b ≤ a * (Real.log a - Real.log b) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h ha.le
  have he : a * (b/a-1) = b-a := by field_simp
  rw [he] at hm
  nlinarith

end AffineFKProof
