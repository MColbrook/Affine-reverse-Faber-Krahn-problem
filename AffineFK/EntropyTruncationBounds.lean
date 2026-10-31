module

public import AffineFK.EntropyTruncation
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-! Scalar bounds for the smooth relative-entropy truncations. -/

@[expose] public noncomputable section
namespace AffineFKProof
open Set

theorem entropyTruncationDeriv_log_ratio (ε L r : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hr : 0 ≤ r) :
    entropyTruncationDeriv ε L r =
      Real.log ((r + ε) / (r + L)) + Real.log ((1 + L) / (1 + ε)) := by
  have hrε : r + ε ≠ 0 := by positivity
  have hrL : r + L ≠ 0 := by positivity
  have h1ε : 1 + ε ≠ 0 := by positivity
  have h1L : 1 + L ≠ 0 := by positivity
  rw [entropyTruncationDeriv, Real.log_div hrε h1ε, Real.log_div hrL h1L,
    Real.log_div hrε hrL, Real.log_div h1L h1ε]
  ring

theorem entropyTruncationDeriv_uniform_bound (ε L : ℝ) (hε : 0 < ε) (hεL : ε ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → |entropyTruncationDeriv ε L r| ≤ C := by
  have hL : 0 < L := hε.trans_le hεL
  refine ⟨|Real.log (ε / L)| + |Real.log ((1 + L) / (1 + ε))|,
    add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro r hr
  have hrε : 0 < r + ε := by linarith
  have hrL : 0 < r + L := by linarith
  have hlow : ε / L ≤ (r + ε) / (r + L) :=
    (div_le_div_iff₀ hL hrL).mpr (by nlinarith [mul_nonneg hr (sub_nonneg.mpr hεL)])
  have hhigh : (r + ε) / (r + L) ≤ 1 :=
    (div_le_one hrL).mpr (by linarith)
  have hloglow := Real.log_le_log (div_pos hε hL) hlow
  have hloghigh : Real.log ((r + ε) / (r + L)) ≤ 0 := by
    simpa only [Real.log_one] using Real.log_le_log (div_pos hrε hrL) hhigh
  rw [entropyTruncationDeriv_log_ratio ε L r hε hL hr]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log (ε / L)), neg_abs_le (Real.log ((1 + L) / (1 + ε)))]
  · linarith [le_abs_self (Real.log ((1 + L) / (1 + ε))), abs_nonneg (Real.log (ε / L))]

theorem entropyTruncationDeriv_monotone (ε L : ℝ) (hε : 0 < ε) (hεL : ε ≤ L) :
    MonotoneOn (entropyTruncationDeriv ε L) (Ici 0) := by
  have hL : 0 < L := hε.trans_le hεL
  have hc : ContinuousOn (entropyTruncationDeriv ε L) (Ici 0) :=
    fun r hr => (entropyTruncationDeriv_hasDerivAt ε L r hε hL hr).continuousAt.continuousWithinAt
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc
    (fun r hr => (entropyTruncationDeriv_hasDerivAt ε L r hε hL (interior_subset hr)).hasDerivWithinAt)
  intro r hr
  have hr0 : 0 ≤ r := interior_subset hr
  have hrε : 0 < r + ε := by linarith
  have hrL : 0 < r + L := by linarith
  have hid : (r + ε)⁻¹ - (r + L)⁻¹ = (L - ε) / ((r + ε) * (r + L)) := by
    field_simp
    ring
  rw [hid]
  positivity

theorem entropyTruncation_convexOn (ε L : ℝ) (hε : 0 < ε) (hεL : ε ≤ L) :
    ConvexOn ℝ (Ici 0) (entropyTruncation ε L) := by
  have hL : 0 < L := hε.trans_le hεL
  apply MonotoneOn.convexOn_of_deriv (convex_Ici 0)
    (fun r hr => (entropyTruncation_hasDerivAt ε L r hε hL hr).continuousAt.continuousWithinAt)
    (fun r hr => (entropyTruncation_hasDerivAt ε L r hε hL (interior_subset hr)).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  rw [(entropyTruncation_hasDerivAt ε L x hε hL (interior_subset hx)).deriv,
    (entropyTruncation_hasDerivAt ε L y hε hL (interior_subset hy)).deriv]
  exact entropyTruncationDeriv_monotone ε L hε hεL (interior_subset hx) (interior_subset hy) hxy

theorem entropyTruncation_nonneg (ε L r : ℝ) (hε : 0 < ε) (hεL : ε ≤ L) (hr : 0 ≤ r) :
    0 ≤ entropyTruncation ε L r := by
  have hL : 0 < L := hε.trans_le hεL
  have hc := entropyTruncation_convexOn ε L hε hεL
  have hone := entropyTruncation_at_one ε L hε hL
  have hderiv : HasDerivAt (entropyTruncation ε L) 0 1 := by
    simpa only [hone.2] using entropyTruncation_hasDerivAt ε L 1 hε hL (by norm_num)
  rcases lt_trichotomy r 1 with hlt | heq | hgt
  · have hs := hc.slope_le_of_hasDerivAt hr (by norm_num : (1 : ℝ) ∈ Ici 0) hlt hderiv
    rw [slope_def_field, hone.1] at hs
    have h := (div_le_iff₀ (sub_pos.mpr hlt)).mp hs
    linarith
  · simpa only [heq, hone.1] using (le_refl (0 : ℝ))
  · have hs := hc.le_slope_of_hasDerivAt (by norm_num : (1 : ℝ) ∈ Ici 0) hr hgt hderiv
    rw [slope_def_field, hone.1] at hs
    have h := (le_div_iff₀ (sub_pos.mpr hgt)).mp hs
    linarith

end AffineFKProof
