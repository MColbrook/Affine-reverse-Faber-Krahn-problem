module

public import AffineFK.OUInformationJumpScalar

/-!
# The scalar information-jump comparison from genuine integrated dissipation

These helper theorems integrate the supplied exact dissipation equations,
which the OU application proves separately. The finite bound retains its
actual boundary terms. Their vanishing follows from the proved weighted
decay of both nonnegative information functions. No initial-time or
infinite-time endpoint, jump, or weighted integral formula is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter Set
open scoped Topology Interval

theorem positive_time_dissipation_gap_finite_bound
    (I K S L : ℝ → ℝ)
    (hI : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable I volume a b)
    (hK : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable K volume a b)
    (hS : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable S volume a b)
    (hL : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable L volume a b)
    (hFTCI : ∀ a b : ℝ, 0 < a → a ≤ b → I b - I a = ∫ r in a..b, -2 * I r - 2 * K r)
    (hFTCS : ∀ a b : ℝ, 0 < a → a ≤ b → S b - S a = ∫ r in a..b, -2 * S r - 2 * L r)
    (hI0 : ∀ r : ℝ, 0 < r → 0 ≤ I r) (hK0 : ∀ r : ℝ, 0 < r → 0 ≤ K r)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hgap : ∀ r : ℝ, 0 < r → c * (I r + K r) ≤ (K r + 2 * I r) - (L r + 2 * S r))
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    I s - S s ≥ Real.exp (-2 * (t - s)) * (I t - S t) -
      c * Real.exp (-2 * (t - s)) * I t + (c / 2) * I s := by
  let DI : ℝ → ℝ := fun r => -2 * I r - 2 * K r
  let DS : ℝ → ℝ := fun r => -2 * S r - 2 * L r
  let Δ : ℝ → ℝ := fun r => I r - S r
  let w : ℝ → ℝ := fun r => Real.exp (-2 * (r - s))
  have hDI (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable DI volume a b :=
    ((hI a b ha hab).const_mul (-2)).sub ((hK a b ha hab).const_mul 2)
  have hDS (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable DS volume a b :=
    ((hS a b ha hab).const_mul (-2)).sub ((hL a b ha hab).const_mul 2)
  have hDΔ (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      IntervalIntegrable (fun r => DI r - DS r) volume a b := (hDI a b ha hab).sub (hDS a b ha hab)
  have hFTCΔ (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      Δ b - Δ a = ∫ r in a..b, DI r - DS r := by
    rw [intervalIntegral.integral_sub (hDI a b ha hab) (hDS a b ha hab),
      ← hFTCI a b ha hab, ← hFTCS a b ha hab]
    dsimp only [Δ]
    ring
  have hwi := positive_time_shifted_weighted_integrated_identity I DI hDI hFTCI (-2) s t hs hst
  have hwΔ := positive_time_shifted_weighted_integrated_identity Δ _ hDΔ hFTCΔ (-2) s t hs hst
  have hB := positive_time_dissipation_weighted_integral_bound I K hI hK hFTCI hI0 hK0 s t hs hst
  let fi : ℝ → ℝ := fun r => w r * (DI r + (-2) * I r)
  let fd : ℝ → ℝ := fun r => w r * ((DI r - DS r) + (-2) * Δ r)
  have hfI : IntervalIntegrable fi volume s t := hwi.1
  have hfΔ : IntervalIntegrable fd volume s t := hwΔ.1
  have hbI : w t * I t - I s = ∫ r in s..t, fi r := hwi.2
  have hbΔ : w t * Δ t - Δ s = ∫ r in s..t, fd r := hwΔ.2
  have hright : IntervalIntegrable (fun r => c * fi r + (2 * c) * (w r * I r)) volume s t :=
    (hfI.const_mul c).add (hB.1.const_mul (2 * c))
  have hpoint (r : ℝ) (hr : r ∈ Icc s t) : fd r ≤ c * fi r + (2 * c) * (w r * I r) := by
    have hg := hgap r (lt_of_lt_of_le hs hr.1)
    have hp := mul_nonneg (Real.exp_pos (-2 * (r - s))).le (sub_nonneg.mpr hg)
    dsimp only [fd, fi, DI, DS, Δ, w]
    nlinarith [hp]
  have hcomparison : w t * Δ t - Δ s ≤
      c * (w t * I t - I s) + (2 * c) * (∫ r in s..t, w r * I r) := by
    rw [hbΔ, hbI]
    calc
      _ ≤ ∫ r in s..t, c * fi r + (2 * c) * (w r * I r) :=
        intervalIntegral.integral_mono_on hst hfΔ hright hpoint
      _ = _ := by
        rw [intervalIntegral.integral_add (hfI.const_mul c) (hB.1.const_mul (2 * c)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hBmul := mul_le_mul_of_nonneg_left hB.2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc0)
  change I s - S s ≥ w t * (I t - S t) - c * w t * I t + (c / 2) * I s
  dsimp only [Δ] at hcomparison
  nlinarith

theorem positive_time_dissipation_gap_bound
    (I K S L : ℝ → ℝ)
    (hI : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable I volume a b)
    (hK : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable K volume a b)
    (hS : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable S volume a b)
    (hL : ∀ a b : ℝ, 0 < a → a ≤ b → IntervalIntegrable L volume a b)
    (hFTCI : ∀ a b : ℝ, 0 < a → a ≤ b → I b - I a = ∫ r in a..b, -2 * I r - 2 * K r)
    (hFTCS : ∀ a b : ℝ, 0 < a → a ≤ b → S b - S a = ∫ r in a..b, -2 * S r - 2 * L r)
    (hI0 : ∀ r : ℝ, 0 < r → 0 ≤ I r) (hK0 : ∀ r : ℝ, 0 < r → 0 ≤ K r)
    (hS0 : ∀ r : ℝ, 0 < r → 0 ≤ S r) (hL0 : ∀ r : ℝ, 0 < r → 0 ≤ L r)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hgap : ∀ r : ℝ, 0 < r → c * (I r + K r) ≤ (K r + 2 * I r) - (L r + 2 * S r))
    (s : ℝ) (hs : 0 < s) : I s - S s ≥ (c / 2) * I s := by
  have hi := positive_time_dissipation_weighted_tendsto_zero I K hI hK hFTCI hI0 hK0 s hs
  have ho := positive_time_dissipation_weighted_tendsto_zero S L hS hL hFTCS hS0 hL0 s hs
  have hlimit : Tendsto (fun t : ℝ => Real.exp (-2 * (t - s)) * (I t - S t) -
      c * Real.exp (-2 * (t - s)) * I t + (c / 2) * I s) atTop (𝓝 ((c / 2) * I s)) := by
    have h := ((hi.sub ho).sub (hi.const_mul c)).add_const ((c / 2) * I s)
    have heq : (fun t : ℝ => Real.exp (-2 * (t - s)) * (I t - S t) -
        c * Real.exp (-2 * (t - s)) * I t + (c / 2) * I s) =
        (fun t : ℝ => (Real.exp (-2 * (t - s)) * I t - Real.exp (-2 * (t - s)) * S t) -
          c * (Real.exp (-2 * (t - s)) * I t) + (c / 2) * I s) := by
      funext t
      ring
    rw [heq]
    simpa only [sub_zero, mul_zero, zero_sub, zero_add] using h
  apply le_of_tendsto hlimit
  filter_upwards [eventually_ge_atTop s] with t ht
  exact positive_time_dissipation_gap_finite_bound I K S L hI hK hS hL hFTCI hFTCS hI0 hK0 c hc0 hgap s t hs ht

end AffineFKProof
