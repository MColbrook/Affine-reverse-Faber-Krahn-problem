module

public import AffineFK.SymmetricConvexInterior
public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Actual Euclidean polar bodies and their Haar volumes

The polar is Mathlib's literal absolute polar for the real inner product.
On a symmetric body this is the usual origin polar. Quantitative ball
inclusions prove compactness and nonempty interior. No universal polar
volume-product bound, reverse Santalo inequality or Milman theorem is
assumed or concluded. Mathlib's polar, convexity, Cauchy--Schwarz and Haar
scaling proofs retain their original contributor attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Metric TopologicalSpace
open scoped ENNReal RealInnerProductSpace Pointwise

theorem gaussianPosition_polar_isClosed (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    IsClosed ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
  rw [LinearMap.polar_eq_biInter_preimage]
  apply isClosed_biInter
  intro x hx
  have hcont : Continuous ((innerₗ (EuclideanSpace ℝ (Fin n))) x) := by
    exact continuous_const.inner continuous_id
  exact isClosed_closedBall.preimage hcont

theorem gaussianPosition_polar_convex (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    Convex ℝ ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
  rw [LinearMap.polar_eq_biInter_preimage]
  exact convex_iInter₂ fun x _hx =>
    (convex_closedBall (0 : ℝ) 1).linear_preimage ((innerₗ (EuclideanSpace ℝ (Fin n))) x)

theorem gaussianPosition_polar_even (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (y : EuclideanSpace ℝ (Fin n)) :
    -y ∈ (innerₗ (EuclideanSpace ℝ (Fin n))).polar K ↔
      y ∈ (innerₗ (EuclideanSpace ℝ (Fin n))).polar K := by
  change (∀ x ∈ K, ‖⟪x, -y⟫‖ ≤ (1 : ℝ)) ↔ ∀ x ∈ K, ‖⟪x, y⟫‖ ≤ (1 : ℝ)
  simp only [inner_neg_right, norm_neg]

theorem gaussianPosition_closedBall_subset_polar (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (R : ℝ) (hR : 0 < R)
    (hbound : ∀ x ∈ K, ‖x‖ ≤ R) :
    closedBall (0 : EuclideanSpace ℝ (Fin n)) R⁻¹ ⊆
      (innerₗ (EuclideanSpace ℝ (Fin n))).polar K := by
  intro y hy x hx
  have hyNorm : ‖y‖ ≤ R⁻¹ := mem_closedBall_zero_iff.mp hy
  change ‖⟪x, y⟫‖ ≤ (1 : ℝ)
  calc
    _ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
    _ ≤ R * R⁻¹ := mul_le_mul (hbound x hx) hyNorm (norm_nonneg y) hR.le
    _ = 1 := mul_inv_cancel₀ hR.ne'

theorem gaussianPosition_polar_subset_closedBall (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ) (hr : 0 < r)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ K) :
    (innerₗ (EuclideanSpace ℝ (Fin n))).polar K ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 / r) := by
  intro y hy
  apply mem_closedBall_zero_iff.mpr
  by_cases hyzero : y = 0
  · simpa only [hyzero, norm_zero] using (div_pos (by norm_num : (0 : ℝ) < 2) hr).le
  have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hyzero
  let c : ℝ := (r / 2) / ‖y‖
  have hc : 0 ≤ c := div_nonneg (by positivity) (norm_nonneg y)
  have hcy : c * ‖y‖ = r / 2 := div_mul_cancel₀ (r / 2) hynorm.ne'
  have hxNorm : ‖c • y‖ = r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, hcy]
  have hx : c • y ∈ K := hball (mem_ball_zero_iff.mpr (by rw [hxNorm]; linarith))
  have hpol := hy (c • y) hx
  simp only [innerₗ_apply_apply, real_inner_smul_left, real_inner_self_eq_norm_sq,
    Real.norm_eq_abs] at hpol
  rw [abs_of_nonneg (mul_nonneg hc (sq_nonneg _))] at hpol
  have hpower : c * ‖y‖ ^ 2 = (r / 2) * ‖y‖ := by
    calc
      _ = (c * ‖y‖) * ‖y‖ := by ring
      _ = _ := by rw [hcy]
  rw [hpower] at hpol
  apply (le_div_iff₀ hr).mpr
  nlinarith

theorem gaussianPosition_polar_convex_body (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K) (hinterior : (interior K).Nonempty)
    (heven : ∀ x, -x ∈ K ↔ x ∈ K) :
    IsCompact ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ∧
      MeasurableSet ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ∧
      Convex ℝ ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ∧
      (∀ y, -y ∈ (innerₗ (EuclideanSpace ℝ (Fin n))).polar K ↔
        y ∈ (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ∧
      (0 : EuclideanSpace ℝ (Fin n)) ∈ interior ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ∧
      0 < volume ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ∧
      volume ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ≠ ∞ ∧
      0 < volume.real ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
  have hzero := symmetric_convex_zero_mem_interior n K hconvex hinterior heven
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  have hclosed := gaussianPosition_polar_isClosed n K
  have hpCompact : IsCompact ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 / r)).of_isClosed_subset hclosed
      (gaussianPosition_polar_subset_closedBall n K r hr hball)
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  have hinner := gaussianPosition_closedBall_subset_polar n K R hR hbound
  have hsmall : ball (0 : EuclideanSpace ℝ (Fin n)) R⁻¹ ⊆
      (innerₗ (EuclideanSpace ℝ (Fin n))).polar K :=
    ball_subset_closedBall.trans hinner
  have hpzero : (0 : EuclideanSpace ℝ (Fin n)) ∈
      interior ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) :=
    mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨R⁻¹, inv_pos.mpr hR, hsmall⟩)
  have hpPos : 0 < volume ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) :=
    (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) (inv_pos.mpr hR)).trans_le
      (measure_mono hsmall)
  exact ⟨hpCompact, hclosed.measurableSet, gaussianPosition_polar_convex n K,
    gaussianPosition_polar_even n K, hpzero, hpPos, hpCompact.measure_ne_top,
    ENNReal.toReal_pos hpPos.ne' hpCompact.measure_ne_top⟩

theorem gaussianPosition_polar_dilation_volume (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    volume ((n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) =
      ENNReal.ofReal ((n : ℝ) ^ n) * volume ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using
    Measure.addHaar_smul_of_nonneg volume (Nat.cast_nonneg n)
      ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K)

theorem gaussianPosition_polar_dilation_real_volume (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    volume.real ((n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) =
      (n : ℝ) ^ n * volume.real ((innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
  simp only [measureReal_def, gaussianPosition_polar_dilation_volume, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (Nat.cast_nonneg n) n)]

theorem gaussianPosition_dilated_polar_finite_volume (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K) (hinterior : (interior K).Nonempty)
    (heven : ∀ x, -x ∈ K ↔ x ∈ K) :
    IsCompact ((n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ∧
      MeasurableSet ((n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ∧
      Convex ℝ ((n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ∧
      (0 : EuclideanSpace ℝ (Fin n)) ∈ interior ((n : ℝ) •
        (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ∧
      0 < volume ((n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ∧
      volume ((n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) ≠ ∞ ∧
      0 < volume.real ((n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
  obtain ⟨hc, _hm, hv, _he, hzero, hpos, _hfin, _hreal⟩ :=
    gaussianPosition_polar_convex_body n K hcompact hconvex hinterior heven
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdc := hc.smul (n : ℝ)
  have hd0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior
      ((n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
    rw [interior_smul₀ hnR.ne']
    exact ⟨0, hzero, smul_zero _⟩
  have hdpos : 0 < volume ((n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K) := by
    rw [gaussianPosition_polar_dilation_volume]
    exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (pow_pos hnR n), hpos⟩
  exact ⟨hdc, hdc.isClosed.measurableSet, hv.smul (n : ℝ), hd0, hdpos,
    hdc.measure_ne_top, ENNReal.toReal_pos hdpos.ne' hdc.measure_ne_top⟩

end AffineFKProof
