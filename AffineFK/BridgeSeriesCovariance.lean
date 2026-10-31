module

public import AffineFK.BridgeScalarL2Series
public import AffineFK.BridgeCoefficientCovariance
public import AffineFK.BridgePathLawGaussian

/-!
# The actual series covariance, before Brownian kernel identification

The covariance below is proved from the actual independent coefficients
and convergent L2 series. It is an explicit deterministic tent series.
Equality of that series to `min(s,t)-s*t` remains a separate obligation.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridgeScalarLevelL2_mean (n : ℕ) (i : Fin n) (j : ℕ) (t : ℝ) :
    (∫ ω, bridgeScalarLevelL2 n i j t ω ∂bridgeCoefficientMeasure n) = 0 := by
  calc
    _ = ⟪bridgeScalarLevelL2 n i j t, Lp.const 2 (bridgeCoefficientMeasure n) (1 : ℝ)⟫ :=
      integral_eq_inner_one _
    _ = ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) * ∑ k : Fin (2 ^ j), (bridgeTent j k t) *
        ⟪bridgeScalarCoefficientL2 n j k i, Lp.const 2 (bridgeCoefficientMeasure n) (1 : ℝ)⟫ := by
      simp [bridgeScalarLevelL2, sum_inner, real_inner_smul_left]
    _ = 0 := by
      simp only [← integral_eq_inner_one, bridgeScalarCoefficientL2_mean, mul_zero,
        Finset.sum_const_zero]

theorem bridgeScalarL2Series_mean (n : ℕ) (i : Fin n) (t : ℝ) :
    (∫ ω, bridgeScalarL2Series n i t ω ∂bridgeCoefficientMeasure n) = 0 := by
  rw [integral_eq_inner_one]
  have h := (innerSL ℝ (Lp.const 2 (bridgeCoefficientMeasure n) (1 : ℝ))).map_tsum
    (bridgeScalarLevelL2_summable n i t)
  have heq : ⟪bridgeScalarL2Series n i t, Lp.const 2 (bridgeCoefficientMeasure n) (1 : ℝ)⟫ =
      ∑' j, ⟪bridgeScalarLevelL2 n i j t, Lp.const 2 (bridgeCoefficientMeasure n) (1 : ℝ)⟫ := by
    simpa only [bridgeScalarL2Series, innerSL_apply_apply, real_inner_comm] using h
  rw [heq]
  simp only [← integral_eq_inner_one, bridgeScalarLevelL2_mean, tsum_zero]

theorem bridgeScalarLevelL2_inner (n : ℕ) (i l : Fin n) (j r : ℕ) (s t : ℝ) :
    ⟪bridgeScalarLevelL2 n i j s, bridgeScalarLevelL2 n l r t⟫ =
      if j = r then ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) ^ 2 *
        (∑ k : Fin (2 ^ j), bridgeTent j k s * bridgeTent j k t) *
          (if i = l then 1 else 0) else 0 := by
  classical
  have hcoef (k : Fin (2 ^ j)) (q : Fin (2 ^ r)) :
      ⟪bridgeScalarCoefficientL2 n j k i, bridgeScalarCoefficientL2 n r q l⟫ =
        if (⟨j, k⟩ : Σ j : ℕ, Fin (2 ^ j)) = ⟨r, q⟩ then
          (if i = l then 1 else 0) else 0 :=
    bridgeScalarCoefficientL2_inner n ⟨j, k⟩ ⟨r, q⟩ i l
  by_cases hjr : j = r
  · subst r
    by_cases hil : i = l
    · subst l
      simp [bridgeScalarLevelL2, real_inner_smul_left, real_inner_smul_right,
        sum_inner, inner_sum, hcoef, mul_ite, ite_mul, Finset.mul_sum]
      ring_nf
      exact Finset.sum_congr rfl (fun k _ => by ring)
    · simp [bridgeScalarLevelL2, real_inner_smul_left, real_inner_smul_right,
        sum_inner, inner_sum, hcoef, hil]
  · have hne (k : Fin (2 ^ j)) (q : Fin (2 ^ r)) :
        (⟨j, k⟩ : Σ j : ℕ, Fin (2 ^ j)) ≠ ⟨r, q⟩ :=
      fun h => hjr (congrArg Sigma.fst h)
    simp [bridgeScalarLevelL2, real_inner_smul_left, real_inner_smul_right,
      sum_inner, inner_sum, hcoef, hne, hjr]

def bridgeSeriesCovarianceKernel (s t : ℝ) : ℝ :=
  ∑' j : ℕ, ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) ^ 2 *
    ∑ k : Fin (2 ^ j), bridgeTent j k s * bridgeTent j k t

theorem bridgeScalarL2Series_inner (n : ℕ) (i l : Fin n) (s t : ℝ) :
    ⟪bridgeScalarL2Series n i s, bridgeScalarL2Series n l t⟫ =
      bridgeSeriesCovarianceKernel s t * (if i = l then 1 else 0) := by
  have hleft : ⟪bridgeScalarL2Series n i s, bridgeScalarL2Series n l t⟫ =
      ∑' j, ⟪bridgeScalarLevelL2 n i j s, bridgeScalarL2Series n l t⟫ := by
    simpa only [bridgeScalarL2Series, innerSL_apply_apply, real_inner_comm] using
      (innerSL ℝ (bridgeScalarL2Series n l t)).map_tsum (bridgeScalarLevelL2_summable n i s)
  have hright (j : ℕ) : ⟪bridgeScalarLevelL2 n i j s, bridgeScalarL2Series n l t⟫ =
      ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) ^ 2 *
        (∑ k : Fin (2 ^ j), bridgeTent j k s * bridgeTent j k t) * (if i = l then 1 else 0) := by
    have h := (innerSL ℝ (bridgeScalarLevelL2 n i j s)).map_tsum
      (bridgeScalarLevelL2_summable n l t)
    change _ = _ at h
    rw [show ⟪bridgeScalarLevelL2 n i j s, bridgeScalarL2Series n l t⟫ =
        ∑' r, ⟪bridgeScalarLevelL2 n i j s, bridgeScalarLevelL2 n l r t⟫ by
      simpa only [bridgeScalarL2Series, innerSL_apply_apply] using h]
    simp only [bridgeScalarLevelL2_inner, tsum_ite_eq']
  rw [hleft]
  simp_rw [hright]
  exact tsum_mul_right

theorem bridgeContinuousSeries_coordinate_mean (n : ℕ) (i : Fin n) (t : Icc (0 : ℝ) 1) :
    (∫ ω, bridgeContinuousSeries n ω t i ∂bridgeCoefficientMeasure n) = 0 := by
  rw [← integral_congr_ae (bridgeScalarL2Series_coe n i t)]
  exact bridgeScalarL2Series_mean n i t

theorem bridgeContinuousSeries_coordinate_covariance (n : ℕ) (i l : Fin n)
    (s t : Icc (0 : ℝ) 1) :
    cov[fun ω => bridgeContinuousSeries n ω s i,
      fun ω => bridgeContinuousSeries n ω t l; bridgeCoefficientMeasure n] =
        bridgeSeriesCovarianceKernel s t * (if i = l then 1 else 0) := by
  have hs := (Lp.memLp (bridgeScalarL2Series n i s)).ae_eq (bridgeScalarL2Series_coe n i s)
  have ht := (Lp.memLp (bridgeScalarL2Series n l t)).ae_eq (bridgeScalarL2Series_coe n l t)
  rw [covariance_eq_sub hs ht, bridgeContinuousSeries_coordinate_mean,
    bridgeContinuousSeries_coordinate_mean, zero_mul, sub_zero]
  calc
    _ = ∫ ω, bridgeScalarL2Series n i s ω * bridgeScalarL2Series n l t ω
        ∂bridgeCoefficientMeasure n := by
      apply integral_congr_ae
      filter_upwards [bridgeScalarL2Series_coe n i s, bridgeScalarL2Series_coe n l t] with ω hs ht
      change bridgeContinuousSeries n ω s i * bridgeContinuousSeries n ω t l = _
      rw [← hs, ← ht]
    _ = ⟪bridgeScalarL2Series n i s, bridgeScalarL2Series n l t⟫ := integral_mul_eq_inner _ _
    _ = _ := bridgeScalarL2Series_inner n i l s t

end AffineFKProof
