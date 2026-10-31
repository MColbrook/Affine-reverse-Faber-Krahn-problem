module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Actual operator-norm power bounds from an L2 order bound -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem positive_l2_operator_mono (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, 0 ≤ f x) → ∀ᵐ x ∂μ, 0 ≤ T f x)
    (f g : Lp ℝ 2 μ) (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    ∀ᵐ x ∂μ, T f x ≤ T g x := by
  have hi : ∀ᵐ x ∂μ, 0 ≤ (g-f) x := by
    filter_upwards [Lp.coeFn_sub g f,hfg] with x hx hle
    simp only [Pi.sub_apply] at hx
    rw [hx]
    linarith
  have ho := hpos (g-f) hi
  rw [map_sub] at ho
  filter_upwards [ho,Lp.coeFn_sub (T g) (T f)] with x hnon hx
  simp only [Pi.sub_apply] at hx
  rw [hx] at hnon
  linarith

theorem positive_l2_operator_abs_domination (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, 0 ≤ f x) → ∀ᵐ x ∂μ, 0 ≤ T f x)
    (f g : Lp ℝ 2 μ) (hfg : ∀ᵐ x ∂μ, |f x| ≤ g x) :
    ∀ᵐ x ∂μ, |T f x| ≤ T g x := by
  have hle : ∀ᵐ x ∂μ, f x ≤ g x := hfg.mono (fun x hx => (le_abs_self _).trans hx)
  have hneg : ∀ᵐ x ∂μ, (-f) x ≤ g x := by
    filter_upwards [hfg,Lp.coeFn_neg f] with x hx hnf
    rw [hnf]
    exact (neg_le_abs _).trans hx
  have hl := positive_l2_operator_mono μ T hpos f g hle
  have hr := positive_l2_operator_mono μ T hpos (-f) g hneg
  rw [map_neg] at hr
  filter_upwards [hl,hr,Lp.coeFn_neg (T f)] with x hleft hright hnf
  rw [hnf] at hright
  simp only [Pi.neg_apply] at hright
  exact abs_le.mpr ⟨by linarith,hleft⟩

theorem positive_l2_operator_power_domination (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, 0 ≤ f x) → ∀ᵐ x ∂μ, 0 ≤ T f x)
    (g : Lp ℝ 2 μ) (C : ℝ) (hC : 0 ≤ C)
    (hbase : ∀ f : Lp ℝ 2 μ, ∀ᵐ x ∂μ, ‖T f x‖ ≤ C*‖f‖*g x) :
    ∀ m : ℕ, ‖T^(m+1)‖ ≤ C * ‖(T^m) g‖ := by
  have hpoint (m : ℕ) (f : Lp ℝ 2 μ) :
      ∀ᵐ x ∂μ, |(T^(m+1)) f x| ≤ (C*‖f‖) * (T^m) g x := by
    induction m with
    | zero => simpa only [Nat.zero_add,pow_one,pow_zero,one_apply_eq_self,Real.norm_eq_abs] using hbase f
    | succ m hm =>
      have hi : ∀ᵐ x ∂μ, |(T^(m+1)) f x| ≤ ((C*‖f‖)•((T^m) g)) x := by
        filter_upwards [hm,Lp.coeFn_smul (C*‖f‖) ((T^m) g)] with x hx hs
        simpa only [hs,Pi.smul_apply,smul_eq_mul] using hx
      have ho := positive_l2_operator_abs_domination μ T hpos _ _ hi
      rw [map_smul] at ho
      filter_upwards [ho,Lp.coeFn_smul (C*‖f‖) (T ((T^m) g))] with x hx hs
      rw [hs] at hx
      simpa only [pow_succ',mul_apply_eq_comp,Pi.smul_apply,smul_eq_mul] using hx
  intro m
  apply (T^(m+1)).opNorm_le_bound (mul_nonneg hC (norm_nonneg _))
  intro f
  have hnorm : ‖(T^(m+1)) f‖ ≤ ‖(C*‖f‖)•((T^m) g)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hpoint m f,Lp.coeFn_smul (C*‖f‖) ((T^m) g)] with x hx hs
    rw [hs]
    change |(T^(m+1)) f x| ≤ |(C*‖f‖)*(T^m) g x|
    exact hx.trans (le_abs_self _)
  calc
    _ ≤ _ := hnorm
    _ = (C*‖(T^m) g‖)*‖f‖ := by
      rw [norm_smul,Real.norm_of_nonneg (mul_nonneg hC (norm_nonneg _))]
      ring

end AffineFKProof
