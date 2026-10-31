module

public import AffineFK.EntropyTruncationBounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Growth and entropy comparison for the smooth truncations

The comparison uses Mathlib's genuine convex klFun (Remy Degenne and
Lorenzo Luccioli), with the exact perspective identity for shifted entropy.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open Set Filter InformationTheory
open scoped Topology

theorem entropyTruncation_linear_growth (ε L : ℝ) (hε : 0 < ε) (hεL : ε ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r → |entropyTruncation ε L r| ≤ B * (r + 1) := by
  have hL : 0 < L := hε.trans_le hεL
  obtain ⟨B, hB, hbound⟩ := entropyTruncationDeriv_uniform_bound ε L hε hεL
  refine ⟨B, hB, ?_⟩
  intro r hr
  have h := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (entropyTruncation_hasDerivAt ε L u hε hL hu).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using hbound u hu)
    (by norm_num : (1 : ℝ) ∈ Ici 0) hr
  have hmain : |entropyTruncation ε L r| ≤ B * |r - 1| := by
    simpa only [(entropyTruncation_at_one ε L hε hL).1, sub_zero, Real.norm_eq_abs] using h
  exact hmain.trans (mul_le_mul_of_nonneg_left
    (abs_le.mpr ⟨by linarith, by linarith⟩ : |r - 1| ≤ r + 1) hB)

theorem entropyShift_eq_perspective (z r : ℝ) (hz : 0 < z) :
    entropyShift z r = (1 + z) * klFun ((r + z) / (1 + z)) := by
  have h1z : 1 + z ≠ 0 := by positivity
  unfold entropyShift klFun
  field_simp
  ring

theorem entropyShift_nonneg (z r : ℝ) (hz : 0 < z) (hr : 0 ≤ r) :
    0 ≤ entropyShift z r := by
  rw [entropyShift_eq_perspective z r hz]
  exact mul_nonneg (by linarith) (klFun_nonneg (by positivity))

theorem entropyShift_le_klFun (z r : ℝ) (hz : 0 < z) (hr : 0 ≤ r) :
    entropyShift z r ≤ klFun r := by
  have h1z : 0 < 1 + z := by linarith
  have hab : (1 : ℝ) / (1 + z) + z / (1 + z) = 1 := by field_simp
  have hj := convexOn_klFun.2 hr (by norm_num : (1 : ℝ) ∈ Ici 0)
    (div_nonneg zero_le_one h1z.le) (div_nonneg hz.le h1z.le) hab
  have hmix : (1 / (1 + z)) • r + (z / (1 + z)) • (1 : ℝ) = (r + z) / (1 + z) := by
    simp only [smul_eq_mul]
    ring
  rw [hmix, klFun_one, smul_zero, add_zero, smul_eq_mul] at hj
  rw [entropyShift_eq_perspective z r hz]
  have hh := mul_le_mul_of_nonneg_left hj h1z.le
  simpa only [← mul_assoc, mul_one_div_cancel h1z.ne', one_mul] using hh

theorem entropyTruncation_le_klFun (ε L r : ℝ)
    (hε : 0 < ε) (hεL : ε ≤ L) (hr : 0 ≤ r) :
    entropyTruncation ε L r ≤ klFun r := by
  exact (sub_le_self _ (entropyShift_nonneg L r (hε.trans_le hεL) hr)).trans
    (entropyShift_le_klFun ε r hε hr)

theorem klFun_le_square (r : ℝ) (hr : 0 ≤ r) : klFun r ≤ (r - 1) ^ 2 := by
  by_cases h0 : r = 0
  · simp [h0, klFun_zero]
  · have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (lt_of_le_of_ne hr (Ne.symm h0))) hr
    unfold klFun
    nlinarith

theorem entropyShift_quadratic_bound (z r : ℝ) (hz : 0 < z) (hr : 0 ≤ r) :
    entropyShift z r ≤ (r - 1) ^ 2 / (1 + z) := by
  have h1z : 0 < 1 + z := by linarith
  rw [entropyShift_eq_perspective z r hz]
  apply (mul_le_mul_of_nonneg_left (klFun_le_square _ (by positivity)) h1z.le).trans_eq
  field_simp
  ring

end AffineFKProof
