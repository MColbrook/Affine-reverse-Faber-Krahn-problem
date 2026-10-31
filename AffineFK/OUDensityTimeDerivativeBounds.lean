module

public import AffineFK.OUDensityTimeKernel

/-!
# Compact space/time bounds for the actual OU density derivative

The explicit kernel derivative is locally uniformly bounded on bounded
spatial sets using only the original first moment. This supplies domination
for later compact spatial entropy chain rules; no entropy derivative or
Fisher-information identity is assumed or concluded here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

/-- The explicit derivative of the positive-time Gaussian-mixture density.
The integral and coefficients are the actual kernel chain-rule formula. -/
def ouDensityTimeDerivative (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-2 * t))
  let r := b⁻¹
  let dr := -(Real.exp (-2 * t) / b) / b ^ 2
  ((n : ℝ) * r ^ (n - 1) * dr) *
      (∫ u, standardGaussianDensity n (r • (x - a • u)) ∂ν) +
    r ^ n * (∫ u, fderiv ℝ (standardGaussianDensity n) (r • (x - a • u))
      (r • (a • u) + dr • (x - a • u)) ∂ν)

theorem ou_density_time_derivative_hasDerivAt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => gaussianSmoothingDensity n ν (Real.exp (-s))
      (Real.sqrt (1 - Real.exp (-2 * s))) x) (ouDensityTimeDerivative n ν t x) t :=
  ou_gaussian_density_hasDerivAt n ν hU x t ht

theorem ou_density_time_derivative_local_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (M : ℝ) (hM : 0 ≤ M) :
    ∃ S : Set ℝ, S ∈ 𝓝 t ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ S, 0 < s ∧ ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ M →
        ‖ouDensityTimeDerivative n ν s x‖ ≤ C := by
  let E := EuclideanSpace ℝ (Fin n)
  let a : ℝ → ℝ := fun s => Real.exp (-s)
  let b : ℝ → ℝ := fun s => Real.sqrt (1 - Real.exp (-2 * s))
  let r : ℝ → ℝ := fun s => (b s)⁻¹
  let d : ℝ → ℝ := fun s => -(Real.exp (-2 * s) / b s) / (b s) ^ 2
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hb : Continuous b := by dsimp [b]; fun_prop
  have hr : ContinuousAt r t := hb.continuousAt.inv₀ (ou_smoothing_scale_domain t ht).2.1.ne'
  have hd : ContinuousAt d t := by
    dsimp [d]
    exact ((by fun_prop : Continuous (fun s : ℝ => Real.exp (-2 * s))).continuousAt.div
      hb.continuousAt (ou_smoothing_scale_domain t ht).2.1.ne').neg.div
        (hb.continuousAt.pow 2) (pow_ne_zero _ (ou_smoothing_scale_domain t ht).2.1.ne')
  let A := ‖a t‖ + 1
  let R := ‖r t‖ + 1
  let D := ‖d t‖ + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hAn : ∀ᶠ s in 𝓝 t, ‖a s‖ < A :=
    ha.continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖a t‖))
  have hRn : ∀ᶠ s in 𝓝 t, ‖r s‖ < R :=
    hr.norm.eventually (gt_mem_nhds (lt_add_one ‖r t‖))
  have hDn : ∀ᶠ s in 𝓝 t, ‖d s‖ < D :=
    hd.norm.eventually (gt_mem_nhds (lt_add_one ‖d t‖))
  let S : Set ℝ := {s | 0 < s ∧ ‖a s‖ ≤ A ∧ ‖r s‖ ≤ R ∧ ‖d s‖ ≤ D}
  have hS : S ∈ 𝓝 t := by
    filter_upwards [lt_mem_nhds ht, hAn, hRn, hDn] with s hs has hrs hds
    exact ⟨hs, has.le, hrs.le, hds.le⟩
  obtain ⟨K, hK, hKb⟩ := standardGaussianDensity_iteratedFDeriv_bound n 1
  have hKbound (y : E) : ‖fderiv ℝ (standardGaussianDensity n) y‖ ≤ K := by
    simpa only [norm_iteratedFDeriv_one] using hKb y
  let J : ℝ := ∫ u : E, ‖u‖ ∂ν
  have hJ : 0 ≤ J := integral_nonneg (fun u => norm_nonneg u)
  let L := R * A * J + D * (M + A * J)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let C := (n : ℝ) * R ^ (n - 1) * D * standardGaussianDensity n 0 + R ^ n * K * L
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity [standardGaussianDensity_pos n 0]
  refine ⟨S, hS, C, hC, ?_⟩
  intro s hs
  refine ⟨hs.1, ?_⟩
  intro x hx
  let z : E → E := fun u => r s • (x - a s • u)
  let v : E → E := fun u => r s • (a s • u) + d s • (x - a s • u)
  have hk0 : ‖∫ u, standardGaussianDensity n (z u) ∂ν‖ ≤ standardGaussianDensity n 0 := by
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := ν) (f := fun u => standardGaussianDensity n (z u))
        (Filter.Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_of_pos (standardGaussianDensity_pos n _)]
          exact gaussianSmoothingDensity_standard_le n _))
  let bound : E → ℝ := fun u => K * (R * A * ‖u‖ + D * (M + A * ‖u‖))
  have hbound_int : Integrable bound ν :=
    ((hU.norm.const_mul (R * A)).add
      (((integrable_const M).add (hU.norm.const_mul A)).const_mul D)).const_mul K
  have hbound (u : E) : ‖fderiv ℝ (standardGaussianDensity n) (z u) (v u)‖ ≤ bound u := by
    have hau : ‖a s • u‖ ≤ A * ‖u‖ := by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right hs.2.1 (norm_nonneg _)
    have hxu : ‖x - a s • u‖ ≤ M + A * ‖u‖ :=
      (norm_sub_le _ _).trans (add_le_add hx hau)
    have hv : ‖v u‖ ≤ R * A * ‖u‖ + D * (M + A * ‖u‖) := by
      calc
        ‖v u‖ ≤ ‖r s • (a s • u)‖ + ‖d s • (x - a s • u)‖ := norm_add_le _ _
        _ = ‖r s‖ * ‖a s • u‖ + ‖d s‖ * ‖x - a s • u‖ := by simp only [norm_smul]
        _ ≤ R * (A * ‖u‖) + D * (M + A * ‖u‖) :=
          add_le_add (mul_le_mul hs.2.2.1 hau (norm_nonneg _) hR)
            (mul_le_mul hs.2.2.2 hxu (norm_nonneg _) hD)
        _ = _ := by ring
    exact ((fderiv ℝ (standardGaussianDensity n) (z u)).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (hKbound _) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hv hK))
  have hk1 : ‖∫ u, fderiv ℝ (standardGaussianDensity n) (z u) (v u) ∂ν‖ ≤ K * L := by
    have hi := norm_integral_le_of_norm_le hbound_int (Filter.Eventually.of_forall hbound)
    have heq : (∫ u, bound u ∂ν) = K * L := by
      rw [integral_const_mul,
        integral_add (f := fun u : E => R * A * ‖u‖) (g := fun u => D * (M + A * ‖u‖))
          (hU.norm.const_mul (R * A))
          (((integrable_const M).add (hU.norm.const_mul A)).const_mul D),
        integral_const_mul, integral_const_mul,
        integral_add (f := fun _ : E => M) (g := fun u => A * ‖u‖)
          (integrable_const M) (hU.norm.const_mul A), integral_const_mul, integral_const]
      simp only [probReal_univ, one_smul]
      rfl
    exact hi.trans_eq heq
  have hpref : ‖(n : ℝ) * (r s) ^ (n - 1) * d s‖ ≤ (n : ℝ) * R ^ (n - 1) * D := by
    rw [norm_mul, norm_mul, norm_natCast, norm_pow]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs.2.2.1 _) (Nat.cast_nonneg _))
      hs.2.2.2 (norm_nonneg _) (by positivity)
  have hpow : ‖(r s) ^ n‖ ≤ R ^ n := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hs.2.2.1 _
  change ‖((n : ℝ) * (r s) ^ (n - 1) * d s) * (∫ u, standardGaussianDensity n (z u) ∂ν) +
    (r s) ^ n * (∫ u, fderiv ℝ (standardGaussianDensity n) (z u) (v u) ∂ν)‖ ≤ C
  calc
    _ ≤ ‖((n : ℝ) * (r s) ^ (n - 1) * d s) * (∫ u, standardGaussianDensity n (z u) ∂ν)‖ +
        ‖(r s) ^ n * (∫ u, fderiv ℝ (standardGaussianDensity n) (z u) (v u) ∂ν)‖ := norm_add_le _ _
    _ = ‖(n : ℝ) * (r s) ^ (n - 1) * d s‖ * ‖∫ u, standardGaussianDensity n (z u) ∂ν‖ +
        ‖(r s) ^ n‖ * ‖∫ u, fderiv ℝ (standardGaussianDensity n) (z u) (v u) ∂ν‖ := by
      simp only [norm_mul]
    _ ≤ ((n : ℝ) * R ^ (n - 1) * D) * standardGaussianDensity n 0 + (R ^ n) * (K * L) :=
      add_le_add (mul_le_mul hpref hk0 (norm_nonneg _) (by positivity))
        (mul_le_mul hpow hk1 (norm_nonneg _) (by positivity))
    _ = C := by dsimp [C]; ring

end AffineFKProof
