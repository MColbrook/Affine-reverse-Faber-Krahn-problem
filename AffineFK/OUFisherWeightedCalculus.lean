module

public import AffineFK.OUFisherAEDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Genuine weighted calculus for integrated positive-time identities

The exact integrated identity yields absolute continuity. Yizheng Zhu's
Mathlib fundamental theorem and product rule for absolutely continuous
functions justify the exponential weight with the actual AE derivative.
The final scalar decay is derived from this identity and nonnegative
dissipation, rather than assumed as a Gronwall or time-shift premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter Set
open scoped Topology Interval

theorem positive_time_integrated_identity_absolutelyContinuous
    (F D : ℝ → ℝ)
    (hi : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable D volume a b)
    (hFTC : ∀ a b : ℝ, 0 < a → a ≤ b → F b - F a = ∫ r in a..b, D r)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) : AbsolutelyContinuousOnInterval F s t := by
  have hprimitive := (hi s t hs hst).absolutelyContinuousOnInterval_intervalIntegral
    (c := s) (by simp)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => F s) s t :=
    (show ContDiff ℝ 1 (fun _ : ℝ => F s) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval
  apply (hconst.fun_add hprimitive).congr
  intro r hr
  rw [uIcc_of_le hst] at hr
  dsimp only
  linarith [hFTC s r hs hr.1]

theorem positive_time_weighted_integrated_identity
    (F D : ℝ → ℝ)
    (hi : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable D volume a b)
    (hFTC : ∀ a b : ℝ, 0 < a → a ≤ b → F b - F a = ∫ r in a..b, D r)
    (k s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => Real.exp (k * r) * (D r + k * F r)) volume s t ∧
      Real.exp (k * t) * F t - Real.exp (k * s) * F s =
        ∫ r in s..t, Real.exp (k * r) * (D r + k * F r) := by
  have hF := positive_time_integrated_identity_absolutelyContinuous F D hi hFTC s t hs hst
  have hE : ContDiff ℝ 1 (fun r : ℝ => Real.exp (k * r)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hEac := hE.contDiffOn.absolutelyContinuousOnInterval (a := s) (b := t)
  have hL1 : IntervalIntegrable (fun r => Real.exp (k * r) * (D r + k * F r)) volume s t :=
    ((hi s t hs hst).add (hF.continuousOn.intervalIntegrable.const_mul k)).continuousOn_mul hE.continuous.continuousOn
  refine ⟨hL1, ?_⟩
  rw [← hEac.integral_deriv_mul_eq_sub hF]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [positive_time_integrated_identity_ae_hasDerivAt F D hi hFTC s t hs hst,
    (volume : Measure ℝ).ae_ne t] with r hr hrt hrmem
  rw [uIoc_of_le hst] at hrmem
  have hri : r ∈ Ioo s t := ⟨hrmem.1, lt_of_le_of_ne hrmem.2 hrt⟩
  have hExp : HasDerivAt (fun u : ℝ => Real.exp (k * u)) (k * Real.exp (k * r)) r := by
    simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id r).const_mul k).exp
  rw [hExp.deriv, (hr hri).deriv]
  ring

theorem positive_time_dissipation_exponential_decay
    (I K : ℝ → ℝ)
    (hI : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable I volume a b)
    (hK : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable K volume a b)
    (hFTC : ∀ a b : ℝ, 0 < a → a ≤ b → I b - I a = ∫ r in a..b, -2 * I r - 2 * K r)
    (hK0 : ∀ r : ℝ, 0 < r → 0 ≤ K r)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    I t ≤ Real.exp (-2 * (t - s)) * I s := by
  have hi (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      IntervalIntegrable (fun r => -2 * I r - 2 * K r) volume a b :=
    ((hI a b ha hab).const_mul (-2)).sub ((hK a b ha hab).const_mul 2)
  have hw := positive_time_weighted_integrated_identity I _ hi hFTC 2 s t hs hst
  have hnonpos : (∫ r in s..t, Real.exp (2 * r) * ((-2 * I r - 2 * K r) + 2 * I r)) ≤ 0 := by
    have h : 0 ≤ ∫ r in s..t, -(Real.exp (2 * r) * ((-2 * I r - 2 * K r) + 2 * I r)) :=
      intervalIntegral.integral_nonneg hst fun r hr => by
        have hKr := hK0 r (lt_of_lt_of_le hs hr.1)
        have he := Real.exp_pos (2 * r)
        nlinarith [mul_nonneg he.le hKr]
    rw [intervalIntegral.integral_neg] at h
    linarith
  have hweighted : Real.exp (2 * t) * I t ≤ Real.exp (2 * s) * I s := by linarith [hw.2]
  have hexp : Real.exp (2 * s) / Real.exp (2 * t) = Real.exp (-2 * (t - s)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  calc
    _ ≤ (Real.exp (2 * s) * I s) / Real.exp (2 * t) :=
      (le_div_iff₀ (Real.exp_pos (2 * t))).mpr (by nlinarith [hweighted])
    _ = (Real.exp (2 * s) / Real.exp (2 * t)) * I s := by ring
    _ = _ := by rw [hexp]

end AffineFKProof
