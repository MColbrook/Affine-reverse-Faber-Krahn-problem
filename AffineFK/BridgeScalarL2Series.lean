module

public import AffineFK.BridgeCoefficientL2

/-!
# L2 convergence of every actual scalar path coordinate

At a fixed time at most one tent contributes at each level. The L2 norm
therefore decays as `2^(-j/2-1)`, with no dyadic multiplicity loss.
The L2 limit is identified AE with the already constructed continuous
path coordinate, rather than an arbitrary chosen random-variable limit.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridgeScalarLevelL2_coe (n : ℕ) (i : Fin n) (j : ℕ) (t : ℝ) :
    (bridgeScalarLevelL2 n i j t :
      (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) → ℝ) =ᵐ[bridgeCoefficientMeasure n]
        (fun ω => bridgeSchauderLevel n j ω t i) := by
  have hterm : ∀ᵐ ω ∂bridgeCoefficientMeasure n, ∀ k : Fin (2 ^ j),
      ((bridgeTent j k t) • bridgeScalarCoefficientL2 n j k i) ω =
        (bridgeTent j k t) * ω j k i := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [Lp.coeFn_smul (bridgeTent j k t) (bridgeScalarCoefficientL2 n j k i),
      bridgeScalarCoefficientL2_coe n j k i] with ω hsmul hcoe
    rw [hsmul]
    change (bridgeTent j k t) * bridgeScalarCoefficientL2 n j k i ω = _
    rw [hcoe]
  filter_upwards [Lp.coeFn_smul ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1))
    (∑ k : Fin (2 ^ j), (bridgeTent j k t) • bridgeScalarCoefficientL2 n j k i),
    Lp.coeFn_finsetSum Finset.univ
      (fun k : Fin (2 ^ j) => (bridgeTent j k t) • bridgeScalarCoefficientL2 n j k i), hterm]
    with ω hw hsum hk
  have hcoord : bridgeSchauderLevel n j ω t i =
      ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) *
        ∑ k : Fin (2 ^ j), (bridgeTent j k t) * ω j k i := by
    rw [← coordinateFunctional_apply n i]
    simp only [bridgeSchauderLevel, map_smul, map_sum, coordinateFunctional_apply, smul_eq_mul]
  rw [hcoord]
  unfold bridgeScalarLevelL2
  rw [hw]
  change ((2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) *
    (∑ k : Fin (2 ^ j), (bridgeTent j k t) • bridgeScalarCoefficientL2 n j k i) ω = _
  rw [hsum]
  simp only [Finset.sum_apply]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => hk k)

theorem bridgeScalarLevelL2_summable_norm (n : ℕ) (i : Fin n) (t : ℝ) :
    Summable (fun j : ℕ => ‖bridgeScalarLevelL2 n i j t‖) := by
  have heq (j : ℕ) : (2 : ℝ) ^ (-(j : ℝ) / 2 - 1) =
      (1 / 2 : ℝ) * (2 : ℝ) ^ ((-1 / 2 : ℝ) * (j : ℝ)) := by
    have h := bridgeSchauder_weight_identity (0 : ℝ) j
    simpa only [zero_mul, Real.rpow_zero, mul_one, zero_sub, neg_div] using h
  have hs : Summable (fun j : ℕ => (2 : ℝ) ^ (-(j : ℝ) / 2 - 1)) :=
    ((two_rpow_multiple_hasSum (-1 / 2 : ℝ) (by norm_num)).summable.mul_left (1 / 2 : ℝ)).congr
      (fun j => (heq j).symm)
  exact hs.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => bridgeScalarLevelL2_norm_bound n i j t)

def bridgeScalarL2Series (n : ℕ) (i : Fin n) (t : ℝ) : Lp ℝ 2 (bridgeCoefficientMeasure n) :=
  ∑' j, bridgeScalarLevelL2 n i j t

theorem bridgeScalarLevelL2_summable (n : ℕ) (i : Fin n) (t : ℝ) :
    Summable (fun j : ℕ => bridgeScalarLevelL2 n i j t) :=
  (bridgeScalarLevelL2_summable_norm n i t).of_norm

theorem bridgeScalarL2Series_coe (n : ℕ) (i : Fin n) (t : Icc (0 : ℝ) 1) :
    (bridgeScalarL2Series n i t :
      (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) → ℝ) =ᵐ[bridgeCoefficientMeasure n]
        (fun ω => bridgeContinuousSeries n ω t i) := by
  have hsum := Lp.coeFn_tsum
    (tsum_enorm_ne_top_iff_summable_norm.mpr (bridgeScalarLevelL2_summable_norm n i t))
  have hlevels : ∀ᵐ ω ∂bridgeCoefficientMeasure n, ∀ j : ℕ,
      bridgeScalarLevelL2 n i j t ω = bridgeSchauderLevel n j ω t i :=
    ae_all_iff.mpr (fun j => bridgeScalarLevelL2_coe n i j t)
  filter_upwards [hsum, hlevels, bridgeContinuousSeries_ae_summable n] with ω hω hlevel hcontinuous
  calc
    bridgeScalarL2Series n i t ω = ∑' j, bridgeScalarLevelL2 n i j t ω := hω
    _ = ∑' j, bridgeSchauderLevel n j ω t i := tsum_congr (fun j => hlevel j)
    _ = bridgeContinuousSeries n ω t i := by
      let L : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
        (coordinateFunctional n i).comp (ContinuousMap.evalCLM ℝ t)
      simpa only [L, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
        coordinateFunctional_apply, bridgeSchauderLevelMap, bridgeContinuousSeries, ContinuousMap.coe_mk] using
          (L.map_tsum hcontinuous).symm

end AffineFKProof
