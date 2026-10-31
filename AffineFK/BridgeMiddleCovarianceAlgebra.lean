module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Exact covariance arithmetic for two short bridges and a Gaussian middle

This is a real scalar identity only. The actual probabilistic means,
independence and covariance are proved separately from their product law.
-/

@[expose] public noncomputable section
namespace AffineFKProof

theorem bridge_middle_covariance_algebra (s t r u : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ((if r ≤ s then Real.sqrt s else 0)*(if u ≤ s then Real.sqrt s else 0)) *
      (min (if r ≤ s then r/s else 0) (if u ≤ s then u/s else 0) -
        (if r ≤ s then r/s else 0)*(if u ≤ s then u/s else 0)) +
    ((if r ≤ s then 0 else Real.sqrt t)*(if u ≤ s then 0 else Real.sqrt t)) *
      (min (if r ≤ s then 0 else (r-s)/t) (if u ≤ s then 0 else (u-s)/t) -
        (if r ≤ s then 0 else (r-s)/t)*(if u ≤ s then 0 else (u-s)/t)) +
    (if r ≤ s then r/s else 1-(r-s)/t)*(if u ≤ s then u/s else 1-(u-s)/t)*(s*t/(s+t)) =
      min r u-r*u/(s+t) := by
  by_cases hr : r ≤ s
  · by_cases hu : u ≤ s
    · simp only [if_pos hr, if_pos hu, zero_mul, mul_zero, min_self, sub_zero, zero_add, add_zero]
      rw [Real.mul_self_sqrt hs.le, min_div_div_right hs.le]
      field_simp [hs.ne', ht.ne', (add_pos hs ht).ne']
      ring
    · simp only [if_pos hr, if_neg hu, zero_mul, mul_zero, zero_add, add_zero]
      rw [min_eq_left (hr.trans (le_of_not_ge hu))]
      field_simp [hs.ne', ht.ne', (add_pos hs ht).ne']
      ring
  · by_cases hu : u ≤ s
    · simp only [if_neg hr, if_pos hu, zero_mul, mul_zero, zero_add, add_zero]
      rw [min_eq_right (hu.trans (le_of_not_ge hr))]
      field_simp [hs.ne', ht.ne', (add_pos hs ht).ne']
      ring
    · simp only [if_neg hr, if_neg hu, zero_mul, mul_zero, min_self, sub_zero, zero_add, add_zero]
      rw [Real.mul_self_sqrt ht.le, min_div_div_right ht.le, min_sub_sub_right]
      field_simp [hs.ne', ht.ne', (add_pos hs ht).ne']
      ring

end AffineFKProof
