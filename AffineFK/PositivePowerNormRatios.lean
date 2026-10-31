module

public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Norm-ratio convergence for dominated self-adjoint powers

This scalar lemma isolates the elementary log-convexity argument. Its
dyadic lower bound will be discharged by the genuine operator-norm
identity for self-adjoint operators and Gaussian kernel domination.
It asserts no spectral or analytic conclusion from an assumed eigenvector.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open Filter Set
open scoped Topology

theorem positive_power_norm_ratio_tendsto
    (b : ℕ → ℝ) (r C : ℝ)
    (hb : ∀ k, 0 < b k)
    (hconv : ∀ k, b (k+1)^2 ≤ b k * b (k+2))
    (hupper : ∀ k, b (k+1) / b k ≤ r)
    (hC : 0 ≤ C)
    (hdyadic : ∀ j : ℕ, r^(2^j) ≤ C * b (2^j-1)) :
    Tendsto (fun k => b (k+1) / b k) atTop (𝓝 r) := by
  let a : ℕ → ℝ := fun k => b (k+1) / b k
  have hapos (k : ℕ) : 0 < a k := div_pos (hb _) (hb _)
  have hmono : Monotone a := by
    apply monotone_nat_of_le_succ
    intro k
    apply (div_le_div_iff₀ (hb k) (hb (k+1))).mpr
    nlinarith [hconv k]
  have hbdd : BddAbove (range a) := ⟨r, by rintro _ ⟨k, rfl⟩; exact hupper k⟩
  let l : ℝ := ⨆ k, a k
  have hlim : Tendsto a atTop (𝓝 l) := tendsto_atTop_ciSup hmono hbdd
  have hal (k : ℕ) : a k ≤ l := le_ciSup hbdd k
  have hlpos : 0 < l := (hapos 0).trans_le (hal 0)
  have hlr : l ≤ r := ciSup_le hupper
  have hbl (k : ℕ) : b k ≤ b 0 * l^k := by
    induction k with
    | zero => simp
    | succ k hk =>
        have hr : b (k+1) ≤ l * b k := (div_le_iff₀ (hb k)).mp (hal k)
        calc
          b (k+1) ≤ l * b k := hr
          _ ≤ l * (b 0 * l^k) := mul_le_mul_of_nonneg_left hk hlpos.le
          _ = b 0 * l^(k+1) := by ring
  have hrpos : 0 < r := hlpos.trans_le hlr
  have hrl : r ≤ l := by
    by_contra hn
    have hlt : l < r := lt_of_not_ge hn
    have hratio : l / r < 1 := (div_lt_one hrpos).mpr hlt
    have hpow : Tendsto (fun j : ℕ => (l/r)^(2^j)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hlpos.le hrpos.le) hratio).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    have hbound (j : ℕ) : l ≤ (C * b 0) * (l/r)^(2^j) := by
      have hN : 1 ≤ 2^j := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
      have h := (hdyadic j).trans (mul_le_mul_of_nonneg_left (hbl (2^j-1)) hC)
      have hmul := mul_le_mul_of_nonneg_left h hlpos.le
      have hexp : 2^j-1+1 = 2^j := Nat.sub_add_cancel hN
      have hexact : l * (C * (b 0 * l^(2^j-1))) = (C*b 0)*l^(2^j) := by
        calc
          _ = (C*b 0) * (l^(2^j-1)*l) := by ring
          _ = _ := by rw [← pow_succ, hexp]
      rw [hexact] at hmul
      rw [div_pow, ← mul_div_assoc]
      apply (le_div_iff₀ (pow_pos hrpos (2^j))).mpr
      exact hmul
    have hzero : l ≤ 0 := ge_of_tendsto
      (by simpa only [mul_zero] using hpow.const_mul (C*b 0))
      (Eventually.of_forall hbound)
    exact (not_le_of_gt hlpos) hzero
  have heq : l = r := le_antisymm hlr hrl
  simpa only [heq, a] using hlim

end AffineFKProof
