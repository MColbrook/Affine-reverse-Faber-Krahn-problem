module

public import AffineFK.PrekopaLeindler
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The standard weighted-mixture Prékopa--Leindler inequality

This rescaling wrapper reuses Jonathan Ho's complete scaled-addition proof
at its attributed pinned source in PrekopaLeindler. Mathlib's genuine
Haar determinant change of variables gives the exact scaling factors;
strictly positive finite factors are cancelled in ENNReal. No integral
is assumed finite and zero functions remain included.
The Haar change-of-variables proofs are due to Floris van Doorn,
Sebastien Gouezel and Mathlib contributors (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem prekopa_lintegral_pos_inv_smul (n : ℕ) (c : ℝ) (hc : 0 < c)
    (f : (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (c⁻¹ • x)) = ENNReal.ofReal (c ^ n) * ∫⁻ x, f x := by
  have hg : Measurable (fun x : Fin n → ℝ => c⁻¹ • x) := by fun_prop
  change (∫⁻ x, (f ∘ (fun x : Fin n → ℝ => c⁻¹ • x)) x) = _
  rw [lintegral_comp hf hg,
    Measure.map_addHaar_smul (volume : Measure (Fin n → ℝ)) (inv_ne_zero hc.ne'),
    lintegral_smul_measure]
  congr 1
  simp only [Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hc.le _)]

theorem prekopa_scaling_factor (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ENNReal.ofReal (a ^ ((n : ℝ) * a) * b ^ ((n : ℝ) * b)) =
      ENNReal.ofReal (a ^ n) ^ a * ENNReal.ofReal (b ^ n) ^ b := by
  rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg ha.le _) ha.le,
    ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hb.le _) hb.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg _ _),
    Real.rpow_natCast_mul ha.le, Real.rpow_natCast_mul hb.le]
  all_goals positivity

theorem prekopa_leindler_weighted_pos (d : ℕ) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (f g h : (Fin (d + 1) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfg : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x := by
  let a : ℝ := 1 - t
  let b : ℝ := t
  let F : (Fin (d + 1) → ℝ) → ℝ≥0∞ := fun x => f (a⁻¹ • x)
  let G : (Fin (d + 1) → ℝ) → ℝ≥0∞ := fun x => g (b⁻¹ • x)
  let C : ℝ := a ^ (((d + 1 : ℕ) : ℝ) * a) * b ^ (((d + 1 : ℕ) : ℝ) * b)
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := ht
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hG : Measurable G := by dsimp [G]; fun_prop
  have hscaled : PLConditions (d + 1) t F G h := by
    refine ⟨ht, ht1, hF, hG, hh, ?_⟩
    intro x y
    have heq : (1 - t) • (a⁻¹ • x) + t • (b⁻¹ • y) = x + y := by
      change a • (a⁻¹ • x) + b • (b⁻¹ • y) = x + y
      rw [smul_smul, smul_smul, mul_inv_cancel₀ ha.ne', mul_inv_cancel₀ hb.ne', one_smul, one_smul]
    simpa only [F, G, heq] using hfg (a⁻¹ • x) (b⁻¹ • y)
  have hbase : (ENNReal.ofReal C)⁻¹ * (∫⁻ x, F x) ^ a * (∫⁻ x, G x) ^ b ≤ ∫⁻ x, h x := by
    have hraw : ENNReal.ofReal (C⁻¹) * (∫⁻ x, F x) ^ a * (∫⁻ x, G x) ^ b ≤ ∫⁻ x, h x := by
      simpa only [C, a, b, Nat.cast_add, Nat.cast_one] using prekopa_leindler hscaled
    simpa only [ENNReal.ofReal_inv_of_pos hC] using hraw
  have hFint := prekopa_lintegral_pos_inv_smul (d + 1) a ha f hf
  have hGint := prekopa_lintegral_pos_inv_smul (d + 1) b hb g hg
  change (∫⁻ x, F x) = _ at hFint
  change (∫⁻ x, G x) = _ at hGint
  rw [hFint, hGint, ENNReal.mul_rpow_of_nonneg _ _ ha.le,
    ENNReal.mul_rpow_of_nonneg _ _ hb.le] at hbase
  have hcoef : ENNReal.ofReal C =
      ENNReal.ofReal (a ^ (d + 1)) ^ a * ENNReal.ofReal (b ^ (d + 1)) ^ b :=
    prekopa_scaling_factor (d + 1) a b ha hb
  have hcancel : (ENNReal.ofReal C)⁻¹ *
      (ENNReal.ofReal (a ^ (d + 1)) ^ a * (∫⁻ x, f x) ^ a) *
      (ENNReal.ofReal (b ^ (d + 1)) ^ b * (∫⁻ x, g x) ^ b) =
      (∫⁻ x, f x) ^ a * (∫⁻ x, g x) ^ b := by
    calc
      _ = ((ENNReal.ofReal C)⁻¹ *
          (ENNReal.ofReal (a ^ (d + 1)) ^ a * ENNReal.ofReal (b ^ (d + 1)) ^ b)) *
          ((∫⁻ x, f x) ^ a * (∫⁻ x, g x) ^ b) := by ac_rfl
      _ = ((ENNReal.ofReal C)⁻¹ * ENNReal.ofReal C) *
          ((∫⁻ x, f x) ^ a * (∫⁻ x, g x) ^ b) := by rw [← hcoef]
      _ = _ := by rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top, one_mul]
  rw [hcancel] at hbase
  exact hbase

end AffineFKProof
