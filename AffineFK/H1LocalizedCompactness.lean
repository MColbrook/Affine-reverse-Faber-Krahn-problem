module

public import AffineFK.DirichletSupportCompact
public import AffineFK.DirichletRellichCompactness
public import AffineFK.DirichletSupportConverse
public import AffineFK.BridgeSobolevEnergyLimit
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Compactness for supported L2 sequences with nearby bounded H1 elements

The compact smooth multiplier factors through the genuine bounded-domain
H0 value map. Its compactness uses Adam Benenson's attributed Rellich
proof. The final H1 energy bound is applied to the original nearby
elements, so the localization introduces no energy constant.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Filter Set
open scoped Topology ContDiff

theorem h1_compact_multiplier_value_isCompact (n : ℕ)
    (m : EuclideanSpace ℝ (Fin n) → ℝ) (hm : ContDiff ℝ ∞ m)
    (hsupp : HasCompactSupport m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1) :
    IsCompactOperator ((unweightedValue n).comp (h1Multiplier n m hm C0 C1 hb0 hb1)) := by
  obtain ⟨R, hR⟩ := hsupp.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin n))
  let V : Opens (EuclideanSpace ℝ (Fin n)) := ⟨Metric.ball 0 R, Metric.isOpen_ball⟩
  let L : unweightedSobolevGraph n →L[ℝ] dirichletSobolev n V :=
    (h1Multiplier n m hm C0 C1 hb0 hb1).codRestrict (dirichletSobolev n V)
      (fun v => h1Multiplier_image_in_dirichlet n V m hm hR C0 C1 hb0 hb1 v)
  exact (dirichletValue_isCompact_of_bounded n V Metric.isBounded_ball).comp_clm L

theorem supported_l2_limit (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hsupp : ∀ k, ∀ᵐ x ∂volume, x ∉ K → f k x = 0)
    (hlim : Tendsto f atTop (𝓝 g)) :
    ∀ᵐ x ∂volume, x ∉ K → g x = 0 := by
  obtain ⟨s, _hs, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.mpr hsupp] with x hx hzero hxK
  have hz : Tendsto (fun k => f (s k) x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hzero _ hxK] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hx hz

set_option maxHeartbeats 1000000 in
theorem supported_l2_near_h1_subsequence (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (f : ℕ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (v : ℕ → unweightedSobolevGraph n) (R : ℝ) (hbound : ∀ k, ‖v k‖ ≤ R)
    (hsupp : ∀ k, ∀ᵐ x ∂volume, x ∉ K → f k x = 0)
    (hclose : Tendsto (fun k => unweightedValue n (v k) - f k) atTop (𝓝 0)) :
    ∃ g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ s : ℕ → ℕ, StrictMono s ∧ Tendsto (fun k => f (s k)) atTop (𝓝 g) := by
  obtain ⟨χ, hχone, hχrange, M, _hM, hχgrad⟩ :=
    exists_dirichlet_compact_cutoff n ⊤ K hK (subset_univ _)
  have hχbound (x) : ‖χ x‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hχrange x).1]
    exact (hχrange x).2
  let L := h1Multiplier n (χ : EuclideanSpace ℝ (Fin n) → ℝ) χ.contDiff 1 M hχbound hχgrad
  let T := (unweightedValue n).comp L
  let A := h1ScalarCoefficient n (χ : EuclideanSpace ℝ (Fin n) → ℝ) χ.contDiff 1 hχbound
  have hfix (k : ℕ) : A (f k) = f k := by
    apply Lp.ext
    filter_upwards [h1ScalarCoefficient_coe n _ χ.contDiff 1 hχbound (f k), hsupp k] with x hx hs
    rw [hx]
    by_cases hxK : x ∈ K
    · rw [hχone x hxK, one_mul]
    · rw [hs hxK, mul_zero]
  have hident (k : ℕ) : T (v k) - f k = A (unweightedValue n (v k) - f k) := by
    rw [map_sub, hfix]
    rfl
  have hsmall : Tendsto (fun k => T (v k) - f k) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hident, map_zero] using (A.continuous.tendsto 0).comp hclose
  have hcompact : IsCompactOperator T :=
    h1_compact_multiplier_value_isCompact n _ χ.contDiff χ.hasCompactSupport 1 M hχbound hχgrad
  obtain ⟨g, _hg, s, hs, hconv⟩ :=
    (hcompact.isCompact_closure_image_closedBall (f := T.toLinearMap) R).tendsto_subseq
      (fun k => subset_closure ⟨v k, mem_closedBall_zero_iff.mpr (hbound k), rfl⟩)
  refine ⟨g, s, hs, ?_⟩
  have h := hconv.sub (hsmall.comp hs.tendsto_atTop)
  change Tendsto (fun k => T (v (s k)) - (T (v (s k)) - f (s k))) atTop (𝓝 (g - 0)) at h
  have heq (k : ℕ) : T (v (s k)) - (T (v (s k)) - f (s k)) = f (s k) := by abel
  simpa only [heq, sub_zero] using h

end AffineFKProof
