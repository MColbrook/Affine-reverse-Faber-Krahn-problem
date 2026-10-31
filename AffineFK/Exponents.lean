module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp

/-!
# Scalar exponents in the affine reverse Faber--Krahn argument

These results verify the real arithmetic and geometric-series steps of
Sections 4--5 of `affine_reverse_faber_krahn.tex`. They do not assert any
information inequality, Gaussian-measure estimate, Brownian representation,
or spectral theorem. In particular, the analytic hypotheses leading to the
scalar exponents remain separate formalisation obligations.

The logarithm, real powers, and geometric-series facts are reused from Mathlib:
`Real.log_neg`, `Real.log_pos`, `Real.rpow_pos_of_pos`,
`Real.rpow_lt_one_of_one_lt_of_neg`, `Real.rpow_mul_natCast`, and
`hasSum_geometric_of_lt_one`. The contributing Mathlib authors retain their
authorship and Apache-2.0 licence.
-/

public section

namespace AffineFKProof

/-- The information-jump ratio lies in `[15/16,1)` when `P ≥ 2`. -/
theorem information_jump_ratio_bounds (P : ℝ) (hP : 2 ≤ P) :
    (15 / 16 : ℝ) ≤ 1 - 1 / (8 * P) ∧ 1 - 1 / (8 * P) < 1 := by
  have hden : (16 : ℝ) ≤ 8 * P := by linarith
  have hdenpos : 0 < 8 * P := by linarith
  have hinv : 1 / (8 * P) ≤ (1 / 16 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hden
  have hinvpos : 0 < 1 / (8 * P) := one_div_pos.mpr hdenpos
  constructor <;> linarith

/-- The logarithmic information-decay exponent is strictly positive. -/
theorem information_decay_exponent_pos (P : ℝ) (hP : 2 ≤ P) :
    0 < -Real.log (1 - 1 / (8 * P)) / Real.log 2 := by
  obtain ⟨hqLower, hqUpper⟩ := information_jump_ratio_bounds P hP
  have hqPos : 0 < 1 - 1 / (8 * P) := by linarith
  exact div_pos (neg_pos.mpr (Real.log_neg hqPos hqUpper))
    (Real.log_pos (by norm_num))

/-- The logarithmic definition has exactly the dyadic contraction ratio in the paper. -/
theorem information_decay_ratio_identity (P : ℝ) (hP : 2 ≤ P) :
    (2 : ℝ) ^ (-(-Real.log (1 - 1 / (8 * P)) / Real.log 2)) =
      1 - 1 / (8 * P) := by
  obtain ⟨hqLower, _hqUpper⟩ := information_jump_ratio_bounds P hP
  have hqPos : 0 < 1 - 1 / (8 * P) := by linarith
  have hlogTwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
  have heq : Real.log 2 * (-(-Real.log (1 - 1 / (8 * P)) / Real.log 2)) =
      Real.log (1 - 1 / (8 * P)) := by
    field_simp [hlogTwo]
  rw [heq, Real.exp_log hqPos]

/-- Iterated dyadic contraction equals the real power with exponent `-δ`. -/
theorem information_decay_dyadic_identity (P : ℝ) (hP : 2 ≤ P) (r : ℕ) :
    (1 - 1 / (8 * P)) ^ r =
      ((2 : ℝ) ^ r) ^ (-(-Real.log (1 - 1 / (8 * P)) / Real.log 2)) := by
  calc
    (1 - 1 / (8 * P)) ^ r =
        ((2 : ℝ) ^ (-(-Real.log (1 - 1 / (8 * P)) / Real.log 2))) ^ r := by
      rw [information_decay_ratio_identity P hP]
    _ = (2 : ℝ) ^
        ((-(-Real.log (1 - 1 / (8 * P)) / Real.log 2)) * (r : ℝ)) :=
      (Real.rpow_mul_natCast (by norm_num) _ r).symm
    _ = (2 : ℝ) ^
        ((r : ℝ) * (-(-Real.log (1 - 1 / (8 * P)) / Real.log 2))) := by
      rw [mul_comm]
    _ = ((2 : ℝ) ^ r) ^ (-(-Real.log (1 - 1 / (8 * P)) / Real.log 2)) :=
      Real.rpow_natCast_mul (by norm_num) r _

/-- The Gaussian dilation exponent obtained from the information gain exceeds two. -/
theorem gaussian_dilation_exponent_gt_two (P : ℝ) (hP : 2 ≤ P) :
    2 < 2 + (-Real.log (1 - 1 / (8 * P)) / Real.log 2) := by
  have h := information_decay_exponent_pos P hP
  linarith

/-- The midpoint of `1/p` and `1/2` is an admissible bridge coefficient exponent. -/
theorem bridge_midpoint_choice (p : ℝ) (hp : 2 < p) :
    1 / p < (1 / p + 1 / 2) / 2 ∧ (1 / p + 1 / 2) / 2 < 1 / 2 := by
  have hinv : 1 / p < (1 / 2 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) hp
  constructor <;> linarith

/-- The interval required by the two bridge series is nonempty exactly for `p > 2`. -/
theorem bridge_choice_iff (p : ℝ) (hp : 0 < p) :
    (∃ a : ℝ, 1 / p < a ∧ a < 1 / 2) ↔ 2 < p := by
  constructor
  · rintro ⟨a, haLower, haUpper⟩
    have hinv : 1 / p < (1 / 2 : ℝ) := lt_trans haLower haUpper
    have hmul : (1 : ℝ) < (1 / 2) * p := (div_lt_iff₀ hp).mp hinv
    linarith
  · intro hpTwo
    exact ⟨(1 / p + 1 / 2) / 2, bridge_midpoint_choice p hpTwo⟩

/-- Both geometric ratios in the bridge proof are positive and strictly less than one. -/
theorem bridge_geometric_ratios (p a : ℝ) (hp : 2 < p)
    (haLower : 1 / p < a) (haUpper : a < 1 / 2) :
    (0 < (2 : ℝ) ^ (1 - a * p) ∧ (2 : ℝ) ^ (1 - a * p) < 1) ∧
    (0 < (2 : ℝ) ^ (a - 1 / 2) ∧ (2 : ℝ) ^ (a - 1 / 2) < 1) := by
  have hpPos : 0 < p := by linarith
  have hap : (1 : ℝ) < a * p := (div_lt_iff₀ hpPos).mp haLower
  have hprob : 1 - a * p < 0 := by linarith
  have hsize : a - 1 / 2 < 0 := by linarith
  exact ⟨⟨Real.rpow_pos_of_pos (by norm_num) _,
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hprob⟩,
    ⟨Real.rpow_pos_of_pos (by norm_num) _,
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hsize⟩⟩

/-- A negative real exponent gives a geometric series with its exact reciprocal sum. -/
theorem two_rpow_multiple_hasSum (c : ℝ) (hc : c < 0) :
    HasSum (fun j : ℕ ↦ (2 : ℝ) ^ (c * (j : ℝ)))
      (1 - (2 : ℝ) ^ c)⁻¹ := by
  have hrPos : 0 ≤ (2 : ℝ) ^ c := (Real.rpow_pos_of_pos (by norm_num) c).le
  have hrLt : (2 : ℝ) ^ c < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hc
  simpa only [Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))] using
    (hasSum_geometric_of_lt_one hrPos hrLt)

/-- Both scalar series in the bridge proof converge. -/
theorem bridge_series_summable (p a : ℝ) (hp : 2 < p)
    (haLower : 1 / p < a) (haUpper : a < 1 / 2) :
    Summable (fun j : ℕ ↦ (2 : ℝ) ^ ((1 - a * p) * (j : ℝ))) ∧
      Summable (fun j : ℕ ↦ (2 : ℝ) ^ ((a - 1 / 2) * (j : ℝ))) := by
  have hpPos : 0 < p := by linarith
  have hap : (1 : ℝ) < a * p := (div_lt_iff₀ hpPos).mp haLower
  exact ⟨(two_rpow_multiple_hasSum (1 - a * p) (by linarith)).summable,
    (two_rpow_multiple_hasSum (a - 1 / 2) (by linarith)).summable⟩

/-- The exact sums used for the probability cost and the uniform bridge bound. -/
theorem bridge_series_values (p a : ℝ) (hp : 2 < p)
    (haLower : 1 / p < a) (haUpper : a < 1 / 2) :
    (∑' j : ℕ, (2 : ℝ) ^ ((1 - a * p) * (j : ℝ))) =
        (1 - (2 : ℝ) ^ (1 - a * p))⁻¹ ∧
      (∑' j : ℕ, (2 : ℝ) ^ ((a - 1 / 2) * (j : ℝ))) =
        (1 - (2 : ℝ) ^ (a - 1 / 2))⁻¹ := by
  have hpPos : 0 < p := by linarith
  have hap : (1 : ℝ) < a * p := (div_lt_iff₀ hpPos).mp haLower
  exact ⟨(two_rpow_multiple_hasSum (1 - a * p) (by linarith)).tsum_eq,
    (two_rpow_multiple_hasSum (a - 1 / 2) (by linarith)).tsum_eq⟩

/-- The volume loss `L ≥ 2⁻ⁿ V` costs at most four after the `2/n` power.
This is only the scalar implication; existence of a symmetric intersection
with this volume is not assumed to have been formalised. -/
theorem symmetric_intersection_volume_factor (n : ℕ) (hn : 0 < n)
    (V L : ℝ) (hV : 0 < V) (hL : 0 < L)
    (hvolume : V ≤ (2 : ℝ) ^ n * L) :
    (V / L) ^ ((2 : ℝ) / (n : ℝ)) ≤ 4 := by
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnNe : (n : ℝ) ≠ 0 := ne_of_gt hnPos
  have hquot : V / L ≤ (2 : ℝ) ^ n := (div_le_iff₀ hL).mpr hvolume
  have hexp : 0 ≤ (2 : ℝ) / (n : ℝ) := div_nonneg (by norm_num) hnPos.le
  calc
    (V / L) ^ ((2 : ℝ) / (n : ℝ)) ≤
        ((2 : ℝ) ^ n) ^ ((2 : ℝ) / (n : ℝ)) :=
      Real.rpow_le_rpow (div_nonneg hV.le hL.le) hquot hexp
    _ = (2 : ℝ) ^ ((n : ℝ) * ((2 : ℝ) / (n : ℝ))) :=
      (Real.rpow_natCast_mul (by norm_num) n _).symm
    _ = (2 : ℝ) ^ (2 : ℝ) := by
      congr 1
      field_simp [hnNe]
    _ = 4 := by norm_num [Real.rpow_two]

end AffineFKProof
