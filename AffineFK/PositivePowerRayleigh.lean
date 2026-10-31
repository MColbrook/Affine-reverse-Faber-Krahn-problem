module

public import AffineFK.PositivePowerNormRatios
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Module

/-!
# Actual normalized powers approach the extremal Rayleigh quotient

Only self-adjoint norm identities, Cauchy--Schwarz, and quadratic
positivity enter. Compactness, spectral decompositions, eigenvectors,
and simplicity are unnecessary. The explicit domination hypothesis is
an operator-norm estimate, to be proved for the actual Gaussian kernel.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open Filter
open scoped Topology RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem selfAdjoint_power_norm_logconvex (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (g : H) (k : ℕ) :
    ‖(T^(k+1)) g‖^2 ≤ ‖(T^k) g‖ * ‖(T^(k+2)) g‖ := by
  have he : ‖(T^(k+1)) g‖^2 = ⟪(T^k) g, (T^(k+2)) g⟫ := by
    have h1 : (T^(k+1)) g = T ((T^k) g) := by rw [pow_succ', mul_apply_eq_comp]
    have h2 : (T^(k+2)) g = T (T ((T^k) g)) := by
      rw [show k+2=(k+1)+1 by omega, pow_succ', mul_apply_eq_comp, h1]
    rw [h1, h2]
    rw [← real_inner_self_eq_norm_sq]
    exact hT.isSymmetric _ _
  rw [he]
  exact real_inner_le_norm _ _

theorem selfAdjoint_power_norm_ratio_tendsto (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (g : H) (hb : ∀ k : ℕ, 0 < ‖(T^k) g‖) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ j : ℕ, ‖T^(2^j)‖ ≤ C * ‖(T^(2^j-1)) g‖) :
    Tendsto (fun k => ‖(T^(k+1)) g‖ / ‖(T^k) g‖) atTop (𝓝 ‖T‖) := by
  apply positive_power_norm_ratio_tendsto (fun k => ‖(T^k) g‖) ‖T‖ C hb
    (selfAdjoint_power_norm_logconvex T hT g)
  · intro k
    apply (div_le_iff₀ (hb k)).mpr
    simpa only [pow_succ', ContinuousLinearMap.mul_apply] using T.le_opNorm ((T^k) g)
  · exact hC
  · intro j
    rw [← hT.norm_pow_two_pow j]
    exact hdom j

theorem positive_operator_square_residual (T : H →L[ℝ] H)
    (hpos : ∀ v : H, 0 ≤ ⟪T v, v⟫) (r : ℝ) (hr : 0 < r) (v : H) :
    r * ‖T v-r•v‖ ≤ ‖T (T v)-(r^2)•v‖ := by
  let w := T v-r•v
  have hid : T w+r•w = T (T v)-(r^2)•v := by
    dsimp [w]
    simp only [map_sub, map_smul]
    module
  have hi : r * ‖w‖^2 ≤ ⟪T w+r•w,w⟫ := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [hpos w]
  have hc := hi.trans (real_inner_le_norm (T w+r•w) w)
  rw [hid] at hc
  by_cases hw : ‖w‖ = 0
  · simpa only [show T v-r•v=w from rfl, hw, mul_zero] using norm_nonneg (T (T v)-(r^2)•v)
  · have hp : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    change r * ‖w‖ ≤ _
    nlinarith

def positivePowerNormalize (T : H →L[ℝ] H) (g : H) (k : ℕ) : H :=
  ‖(T^k) g‖⁻¹ • (T^k) g

theorem positivePowerNormalize_norm (T : H →L[ℝ] H) (g : H) (k : ℕ)
    (hb : 0 < ‖(T^k) g‖) : ‖positivePowerNormalize T g k‖ = 1 := by
  simp only [positivePowerNormalize, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hb.le), inv_mul_cancel₀ hb.ne']

theorem positivePowerNormalize_apply_norm (T : H →L[ℝ] H) (g : H) (k : ℕ)
    (hb : 0 < ‖(T^k) g‖) :
    ‖T (positivePowerNormalize T g k)‖ = ‖(T^(k+1)) g‖ / ‖(T^k) g‖ := by
  simp only [positivePowerNormalize, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hb.le), pow_succ', ContinuousLinearMap.mul_apply]
  ring

theorem positivePowerNormalize_apply_twice_norm (T : H →L[ℝ] H) (g : H) (k : ℕ)
    (hb : 0 < ‖(T^k) g‖) :
    ‖T (T (positivePowerNormalize T g k))‖ = ‖(T^(k+2)) g‖ / ‖(T^k) g‖ := by
  simp only [positivePowerNormalize, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hb.le), pow_succ', ContinuousLinearMap.mul_apply,
    Nat.add_assoc]
  ring

theorem positivePowerNormalize_rayleigh_tendsto (T : H →L[ℝ] H)
    (hT : IsSelfAdjoint T) (hpos : ∀ v : H, 0 ≤ ⟪T v,v⟫)
    (g : H) (hb : ∀ k : ℕ, 0 < ‖(T^k) g‖) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ j : ℕ, ‖T^(2^j)‖ ≤ C * ‖(T^(2^j-1)) g‖) :
    Tendsto (fun k => ⟪positivePowerNormalize T g k,
      T (positivePowerNormalize T g k)⟫) atTop (𝓝 ‖T‖) := by
  let r := ‖T‖
  let u := positivePowerNormalize T g
  let a : ℕ → ℝ := fun k => ‖(T^(k+1)) g‖ / ‖(T^k) g‖
  have ha : Tendsto a atTop (𝓝 r) :=
    selfAdjoint_power_norm_ratio_tendsto T hT g hb C hC hdom
  have hr : 0 < r := by
    have h := T.le_opNorm g
    have h1 := hb 1
    have h0 := hb 0
    simp only [pow_one] at h1
    simp only [pow_zero, ContinuousLinearMap.one_apply] at h0
    change 0 < ‖T‖
    nlinarith [norm_nonneg T]
  have hun (k : ℕ) : ‖u k‖ = 1 := positivePowerNormalize_norm T g k (hb k)
  have hfirst (k : ℕ) : ‖T (u k)‖ = a k := positivePowerNormalize_apply_norm T g k (hb k)
  have hsecond (k : ℕ) : ‖T (T (u k))‖ = a (k+1) * a k := by
    rw [positivePowerNormalize_apply_twice_norm T g k (hb k)]
    dsimp [a]
    simpa only [Nat.add_assoc] using
      (div_mul_div_cancel₀ (a := ‖(T^(k+2)) g‖) (c := ‖(T^k) g‖) (hb (k+1)).ne').symm
  have hfirstlim : Tendsto (fun k => ‖T (u k)‖) atTop (𝓝 r) := by
    simpa only [hfirst] using ha
  have hsecondlim : Tendsto (fun k => ‖T (T (u k))‖) atTop (𝓝 (r^2)) := by
    simpa only [hsecond, Function.comp_def, pow_two] using
      (ha.comp (tendsto_add_atTop_nat 1)).mul ha
  have hinner (k : ℕ) : ⟪T (T (u k)),u k⟫ = ‖T (u k)‖^2 := by
    calc
      _ = ⟪T (u k),T (u k)⟫ := hT.isSymmetric _ _
      _ = _ := real_inner_self_eq_norm_sq _
  have hres (k : ℕ) : ‖T (T (u k))-(r^2)•u k‖^2 =
      ‖T (T (u k))‖^2-2*r^2*‖T (u k)‖^2+r^4 := by
    rw [norm_sub_sq_real, real_inner_smul_right, hinner, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r), hun]
    ring
  have hreslimsq : Tendsto (fun k => ‖T (T (u k))-(r^2)•u k‖^2) atTop (𝓝 0) := by
    have hp := ((hsecondlim.pow 2).sub ((hfirstlim.pow 2).const_mul (2*r^2))).add_const (r^4)
    have hz : (r^2)^2-2*r^2*r^2+r^4 = 0 := by ring
    simpa only [hres, hz] using hp
  have hreslim : Tendsto (fun k => ‖T (T (u k))-(r^2)•u k‖) atTop (𝓝 0) := by
    have hp := Real.continuous_sqrt.continuousAt.tendsto.comp hreslimsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hp
  have hbound (k : ℕ) : ‖T (u k)-r•u k‖ ≤ ‖T (T (u k))-(r^2)•u k‖ / r := by
    apply (le_div_iff₀ hr).mpr
    simpa only [mul_comm] using positive_operator_square_residual T hpos r hr (u k)
  have hw : Tendsto (fun k => ‖T (u k)-r•u k‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) hbound (by simpa using hreslim.div_const r)
  have hpair (k : ℕ) : ‖⟪u k,T (u k)⟫-r‖ ≤ ‖T (u k)-r•u k‖ := by
    have hp := norm_inner_le_norm (𝕜 := ℝ) (u k) (T (u k)-r•u k)
    simpa only [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      hun, one_pow, mul_one, one_mul] using hp
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hpair hw)

end AffineFKProof
