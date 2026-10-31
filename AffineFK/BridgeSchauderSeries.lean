module

public import AffineFK.BridgeGaussianProfile
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# The literal dyadic tents and their deterministic bridge series

The tents have height one and dyadic support. Their disjoint nonzero
supports give one coefficient at each level, rather than a factor `2^j`
in the uniform path bound. Uniform convergence and continuity reuse
Mathlib's function-series theorems (Mathlib contributors, Apache-2.0).
Identification of this random series with the standard Brownian bridge
and the killed-kernel/Rayleigh comparison remain separate obligations.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology

def bridgeTent (j k : ℕ) (t : ℝ) : ℝ :=
  max 0 (1 - |(2 : ℝ) ^ (j + 1) * t - (2 * (k : ℝ) + 1)|)

theorem bridgeTent_nonneg (j k : ℕ) (t : ℝ) : 0 ≤ bridgeTent j k t := le_max_left _ _

theorem bridgeTent_le_one (j k : ℕ) (t : ℝ) : bridgeTent j k t ≤ 1 := by
  unfold bridgeTent
  exact max_le (by norm_num) (by linarith [abs_nonneg ((2 : ℝ) ^ (j + 1) * t - (2 * (k : ℝ) + 1))])

theorem bridgeTent_continuous (j k : ℕ) : Continuous (bridgeTent j k) := by
  unfold bridgeTent
  fun_prop

theorem bridgeTent_unique (j k l : ℕ) (t : ℝ)
    (hk : bridgeTent j k t ≠ 0) (hl : bridgeTent j l t ≠ 0) : k = l := by
  have hkpos := lt_of_le_of_ne (bridgeTent_nonneg j k t) (Ne.symm hk)
  have hlpos := lt_of_le_of_ne (bridgeTent_nonneg j l t) (Ne.symm hl)
  have hkabs : |(2 : ℝ) ^ (j + 1) * t - (2 * (k : ℝ) + 1)| < 1 := by
    unfold bridgeTent at hkpos
    have := (lt_max_iff.mp hkpos).resolve_left (lt_irrefl _)
    linarith
  have hlabs : |(2 : ℝ) ^ (j + 1) * t - (2 * (l : ℝ) + 1)| < 1 := by
    unfold bridgeTent at hlpos
    have := (lt_max_iff.mp hlpos).resolve_left (lt_irrefl _)
    linarith
  rw [abs_lt] at hkabs hlabs
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · have : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hkl
    linarith
  · have : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlk
    linarith

def bridgeSchauderLevel (n j : ℕ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) •
    ∑ k : Fin (2 ^ j), (bridgeTent j k t) • ω j k

def bridgeSchauderSeries (n : ℕ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) := ∑' j, bridgeSchauderLevel n j ω t

theorem bridgeSchauderLevel_continuous (n j : ℕ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) :
    Continuous (bridgeSchauderLevel n j ω) := by
  unfold bridgeSchauderLevel bridgeTent
  fun_prop

theorem bridgeTent_sum_single (n j : ℕ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (∑ k : Fin (2 ^ j), (bridgeTent j k t) • ω j k) = 0 ∨
      ∃ k : Fin (2 ^ j), (∑ l : Fin (2 ^ j), (bridgeTent j l t) • ω j l) =
        (bridgeTent j k t) • ω j k := by
  classical
  by_cases h : ∃ k : Fin (2 ^ j), bridgeTent j k t ≠ 0
  · obtain ⟨k, hk⟩ := h
    right
    refine ⟨k, Finset.sum_eq_single k ?_ (by simp)⟩
    intro l _ hl
    have hz : bridgeTent j l t = 0 := by
      by_contra hne
      exact hl (Fin.ext (bridgeTent_unique j l k t hne hk))
    simp [hz]
  · left
    push_neg at h
    simp [h]

theorem bridgeSchauder_weight_identity (a : ℝ) (j : ℕ) :
    ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) * ((2 : ℝ) ^ (a * (j : ℝ))) =
      (1 / 2 : ℝ) * (2 : ℝ) ^ ((a - 1 / 2) * (j : ℝ)) := by
  rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
  rw [show -(j : ℝ) / 2 - 1 + a * (j : ℝ) = ((a - 1 / 2) * (j : ℝ)) + (-1) by ring,
    Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
  norm_num [Real.rpow_neg_one, mul_comm]

theorem bridgeSchauderLevel_norm_bound (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ x ∈ D, ‖x‖ ≤ M) (a : ℝ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n))
    (hω : ω ∈ bridgeCoefficientEvent n D a) (j : ℕ) (t : ℝ) :
    ‖bridgeSchauderLevel n j ω t‖ ≤
      (M / 2) * (2 : ℝ) ^ ((a - 1 / 2) * (j : ℝ)) := by
  have hweight : 0 ≤ (2 : ℝ) ^ (-(j : ℝ) / 2 - 1) := by positivity
  have hb : 0 ≤ (2 : ℝ) ^ (a * (j : ℝ)) := by positivity
  have hnorm : ∀ k : Fin (2 ^ j), ‖ω j k‖ ≤ ((2 : ℝ) ^ (a * (j : ℝ))) * M := by
    intro k
    have hk : ω j k ∈ ((2 : ℝ) ^ (a * (j : ℝ))) • D := hω j (by simp) k (by simp)
    obtain ⟨x, hx, heq⟩ := hk
    rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    exact mul_le_mul_of_nonneg_left (hbound x hx) hb
  have hsum : ‖∑ k : Fin (2 ^ j), (bridgeTent j k t) • ω j k‖ ≤
      ((2 : ℝ) ^ (a * (j : ℝ))) * M := by
    rcases bridgeTent_sum_single n j ω t with hzero | ⟨k, hk⟩
    · rw [hzero, norm_zero]
      positivity
    · rw [hk, norm_smul, Real.norm_eq_abs, abs_of_nonneg (bridgeTent_nonneg _ _ _)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (bridgeTent_le_one _ _ _)).trans (hnorm k)
  unfold bridgeSchauderLevel
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hweight]
  calc
    _ ≤ ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) * (((2 : ℝ) ^ (a * (j : ℝ))) * M) :=
      mul_le_mul_of_nonneg_left hsum hweight
    _ = _ := by rw [← mul_assoc, bridgeSchauder_weight_identity]; ring

theorem bridgeSchauderLevel_gauge_bound (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (a : ℝ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n))
    (hω : ω ∈ bridgeCoefficientEvent n D a) (j : ℕ) (t : ℝ) :
    gauge D (bridgeSchauderLevel n j ω t) ≤
      (1 / 2 : ℝ) * (2 : ℝ) ^ ((a - 1 / 2) * (j : ℝ)) := by
  have hweight : 0 ≤ (2 : ℝ) ^ (-(j : ℝ) / 2 - 1) := by positivity
  have hb : 0 ≤ (2 : ℝ) ^ (a * (j : ℝ)) := by positivity
  have hgauge : ∀ k : Fin (2 ^ j), gauge D (ω j k) ≤ (2 : ℝ) ^ (a * (j : ℝ)) :=
    fun k => gauge_le_of_mem hb (hω j (by simp) k (by simp))
  have hsum : gauge D (∑ k : Fin (2 ^ j), (bridgeTent j k t) • ω j k) ≤
      (2 : ℝ) ^ (a * (j : ℝ)) := by
    rcases bridgeTent_sum_single n j ω t with hzero | ⟨k, hk⟩
    · rw [hzero, gauge_zero]
      exact hb
    · rw [hk, gauge_smul_of_nonneg (bridgeTent_nonneg _ _ _), smul_eq_mul]
      exact (mul_le_of_le_one_left (gauge_nonneg _) (bridgeTent_le_one _ _ _)).trans (hgauge k)
  unfold bridgeSchauderLevel
  rw [gauge_smul_of_nonneg hweight, smul_eq_mul]
  exact (mul_le_mul_of_nonneg_left hsum hweight).trans_eq (bridgeSchauder_weight_identity a j)

/-- Uniform convergence, continuity and the exact Minkowski-functional radius
on the actual coefficient event. This is a deterministic series theorem. -/
theorem bridgeSchauderSeries_controlled (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D)
    (hconvex : Convex ℝ D) (hzero : 0 ∈ interior D)
    (a : ℝ) (ha : a < 1 / 2)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n))
    (hω : ω ∈ bridgeCoefficientEvent n D a) :
    Continuous (bridgeSchauderSeries n ω) ∧
    TendstoUniformly
      (fun N : ℕ => fun t : ℝ => ∑ j ∈ Finset.range N, bridgeSchauderLevel n j ω t)
      (bridgeSchauderSeries n ω) atTop ∧
    ∀ t : ℝ, gauge D (bridgeSchauderSeries n ω t) ≤
      1 / (2 * (1 - (2 : ℝ) ^ (a - 1 / 2))) := by
  obtain ⟨M, hM, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  let u : ℕ → ℝ := fun j => (M / 2) * (2 : ℝ) ^ ((a - 1 / 2) * (j : ℝ))
  let v : ℕ → ℝ := fun j => (1 / 2 : ℝ) * (2 : ℝ) ^ ((a - 1 / 2) * (j : ℝ))
  have hgeom := two_rpow_multiple_hasSum (a - 1 / 2) (by linarith)
  have hu : Summable u := hgeom.summable.mul_left (M / 2)
  have hnorm (j : ℕ) (t : ℝ) : ‖bridgeSchauderLevel n j ω t‖ ≤ u j :=
    bridgeSchauderLevel_norm_bound n D M hM.le hbound a ω hω j t
  have hunif := tendstoUniformly_tsum_nat hu hnorm
  have hcont : Continuous (bridgeSchauderSeries n ω) :=
    continuous_tsum (fun j => bridgeSchauderLevel_continuous n j ω) hu hnorm
  refine ⟨hcont, hunif, ?_⟩
  intro t
  have hv : HasSum v ((1 / 2 : ℝ) * (1 - (2 : ℝ) ^ (a - 1 / 2))⁻¹) :=
    hgeom.mul_left (1 / 2 : ℝ)
  have hseries : Summable (fun j => bridgeSchauderLevel n j ω t) :=
    hu.of_norm_bounded (fun j => hnorm j t)
  have hnhds : D ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) := mem_interior_iff_mem_nhds.mp hzero
  have hlimit := ((continuous_gauge hconvex hnhds).tendsto
    (bridgeSchauderSeries n ω t)).comp hseries.hasSum
  have hle : gauge D (bridgeSchauderSeries n ω t) ≤
      (1 / 2 : ℝ) * (1 - (2 : ℝ) ^ (a - 1 / 2))⁻¹ := by
    apply le_of_tendsto_of_tendsto' hlimit hv
    intro s
    exact (gauge_sum_le hconvex (absorbent_nhds_zero hnhds) s _).trans
      (Finset.sum_le_sum (fun j _ => bridgeSchauderLevel_gauge_bound n D a ω hω j t))
  convert hle using 1
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

end AffineFKProof
