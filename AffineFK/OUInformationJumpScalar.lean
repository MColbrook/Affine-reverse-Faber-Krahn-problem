module

public import AffineFK.OUFisherWeightedCalculus

/-!
# Scalar weighted integration for the information jump

The positive-time integrated identities supply absolute continuity and
the exponential decay. All finite-interval integrals below have actual
integrability guards. The tail limit follows from that proved decay,
without an assumed endpoint or a pointwise differentiability claim.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter Set
open scoped Topology Interval

theorem positive_time_shifted_weighted_integrated_identity
    (F D : ℝ → ℝ)
    (hi : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable D volume a b)
    (hFTC : ∀ a b : ℝ, 0 < a → a ≤ b → F b - F a = ∫ r in a..b, D r)
    (k s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => Real.exp (k * (r - s)) * (D r + k * F r)) volume s t ∧
      Real.exp (k * (t - s)) * F t - F s =
        ∫ r in s..t, Real.exp (k * (r - s)) * (D r + k * F r) := by
  have h := positive_time_weighted_integrated_identity F D hi hFTC k s t hs hst
  have hw (r : ℝ) : Real.exp (-k * s) * Real.exp (k * r) = Real.exp (k * (r - s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfun : (fun r => Real.exp (-k * s) * (Real.exp (k * r) * (D r + k * F r))) =
      (fun r => Real.exp (k * (r - s)) * (D r + k * F r)) := by
    funext r
    rw [← mul_assoc, hw]
  have hint := h.1.const_mul (Real.exp (-k * s))
  rw [hfun] at hint
  refine ⟨hint, ?_⟩
  calc
    _ = Real.exp (-k * s) * (Real.exp (k * t) * F t - Real.exp (k * s) * F s) := by
      symm
      rw [mul_sub, ← mul_assoc, hw t, ← mul_assoc, hw s]
      simp only [sub_self, mul_zero, Real.exp_zero, one_mul]
    _ = Real.exp (-k * s) * ∫ r in s..t, Real.exp (k * r) * (D r + k * F r) := congrArg _ h.2
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      exact congrFun hfun r

theorem positive_time_dissipation_weighted_integral_bound
    (I K : ℝ → ℝ)
    (hI : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable I volume a b)
    (hK : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable K volume a b)
    (hFTC : ∀ a b : ℝ, 0 < a → a ≤ b → I b - I a = ∫ r in a..b, -2 * I r - 2 * K r)
    (hI0 : ∀ r : ℝ, 0 < r → 0 ≤ I r) (hK0 : ∀ r : ℝ, 0 < r → 0 ≤ K r)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => Real.exp (-2 * (r - s)) * I r) volume s t ∧
      (∫ r in s..t, Real.exp (-2 * (r - s)) * I r) ≤ I s / 4 := by
  have hi : IntervalIntegrable (fun r => Real.exp (-2 * (r - s)) * I r) volume s t :=
    (hI s t hs hst).continuousOn_mul (show Continuous (fun r : ℝ => Real.exp (-2 * (r - s))) from by fun_prop).continuousOn
  refine ⟨hi, ?_⟩
  have hu : IntervalIntegrable (fun r => Real.exp (-4 * (r - s)) * I s) volume s t :=
    (show Continuous (fun r : ℝ => Real.exp (-4 * (r - s)) * I s) from by fun_prop).intervalIntegrable s t
  have hpoint (r : ℝ) (hr : r ∈ Icc s t) : Real.exp (-2 * (r - s)) * I r ≤
      Real.exp (-4 * (r - s)) * I s := by
    have hdec := positive_time_dissipation_exponential_decay I K hI hK hFTC hK0 s r hs hr.1
    have hmul := mul_le_mul_of_nonneg_left hdec (Real.exp_pos (-2 * (r - s))).le
    have he : Real.exp (-2 * (r - s)) * Real.exp (-2 * (r - s)) = Real.exp (-4 * (r - s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simpa only [← mul_assoc, he] using hmul
  have hExpInt : (∫ r in s..t, Real.exp (-4 * (r - s))) ≤ (1 / 4 : ℝ) := by
    have hder (r : ℝ) : HasDerivAt (fun u : ℝ => (-1 / 4 : ℝ) * Real.exp (-4 * (u - s)))
        (Real.exp (-4 * (r - s))) r := by
      convert (((hasDerivAt_id r).sub_const s).const_mul (-4 : ℝ)).exp.const_mul (-1 / 4 : ℝ) using 1
      all_goals simp only [id_eq]
      all_goals ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hder r)
      ((show Continuous (fun r : ℝ => Real.exp (-4 * (r - s))) from by fun_prop).intervalIntegrable s t)]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    nlinarith [Real.exp_pos (-4 * (t - s))]
  calc
    _ ≤ ∫ r in s..t, Real.exp (-4 * (r - s)) * I s := intervalIntegral.integral_mono_on hst hi hu hpoint
    _ = (∫ r in s..t, Real.exp (-4 * (r - s))) * I s := intervalIntegral.integral_mul_const _ _
    _ ≤ (1 / 4 : ℝ) * I s := mul_le_mul_of_nonneg_right hExpInt (hI0 s hs)
    _ = _ := by ring

theorem positive_time_dissipation_weighted_tendsto_zero
    (I K : ℝ → ℝ)
    (hI : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable I volume a b)
    (hK : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable K volume a b)
    (hFTC : ∀ a b : ℝ, 0 < a → a ≤ b → I b - I a = ∫ r in a..b, -2 * I r - 2 * K r)
    (hI0 : ∀ r : ℝ, 0 < r → 0 ≤ I r) (hK0 : ∀ r : ℝ, 0 < r → 0 ≤ K r)
    (s : ℝ) (hs : 0 < s) :
    Tendsto (fun t : ℝ => Real.exp (-2 * (t - s)) * I t) atTop (𝓝 0) := by
  have hExp : Tendsto (fun t : ℝ => Real.exp (-4 * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-4 : ℝ) < 0))
  have hbound : Tendsto (fun t : ℝ => Real.exp (-4 * t) * (Real.exp (4 * s) * I s)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hExp.mul_const (Real.exp (4 * s) * I s)
  apply squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_ge_atTop s] with t ht
    exact mul_nonneg (Real.exp_pos _).le (hI0 t (lt_of_lt_of_le hs ht))
  · filter_upwards [eventually_ge_atTop s] with t ht
    have hdec := positive_time_dissipation_exponential_decay I K hI hK hFTC hK0 s t hs ht
    have hmul := mul_le_mul_of_nonneg_left hdec (Real.exp_pos (-2 * (t - s))).le
    have he : Real.exp (-2 * (t - s)) * Real.exp (-2 * (t - s)) =
        Real.exp (-4 * t) * Real.exp (4 * s) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ Real.exp (-2 * (t - s)) * (Real.exp (-2 * (t - s)) * I s) := hmul
      _ = _ := by rw [← mul_assoc, he, mul_assoc]

end AffineFKProof
