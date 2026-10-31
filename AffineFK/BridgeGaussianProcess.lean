module

public import AffineFK.BridgeScalarL2Series

/-!
# Gaussian finite-dimensional laws of the actual continuous series

Finite partial paths are genuine finite linear transformations of the
jointly Gaussian coefficient process. Their actual L2 limits identify
the coordinates of the measurable continuous path. The Gaussian-limit
step reuses the attributed Armstrong--Loher proofs in `GaussianL2Limit`.
The Brownian covariance `min(s,t)-s*t` is not a premise or conclusion here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

def bridgeScalarPartialEval (n N : ℕ) (p : ℝ × Fin n)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j ∈ Finset.range N, bridgeSchauderLevel n j ω p.1 p.2

theorem bridgeScalarPartialEval_gaussian_process (n N : ℕ) :
    IsGaussianProcess (bridgeScalarPartialEval n N) (bridgeCoefficientMeasure n) := by
  classical
  apply (bridgeCoefficient_isGaussianProcess n).of_isGaussianProcess
  intro p
  let S : Finset (Σ j : ℕ, Fin (2 ^ j)) :=
    (Finset.range N).sigma (fun j => (Finset.univ : Finset (Fin (2 ^ j))))
  let L : (S → EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
    ∑ q : S, (((2 : ℝ) ^ (-(q.1.1 : ℝ) / 2 - 1)) * bridgeTent q.1.1 q.1.2 p.1) •
      ((coordinateFunctional n p.2).comp (ContinuousLinearMap.proj q))
  refine ⟨S, L, ?_⟩
  intro ω
  simp only [L, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Finset.restrict_def, coordinateFunctional_apply]
  rw [Finset.sum_coe_sort (s := S) (f := fun q : Σ j : ℕ, Fin (2 ^ j) =>
      ((2 : ℝ) ^ (-(q.1 : ℝ) / 2 - 1)) * bridgeTent q.1 q.2 p.1 * ω q.1 q.2 p.2),
    show S = (Finset.range N).sigma
    (fun j => (Finset.univ : Finset (Fin (2 ^ j)))) from rfl, Finset.sum_sigma]
  unfold bridgeScalarPartialEval
  apply Finset.sum_congr rfl
  intro j _
  rw [← coordinateFunctional_apply n p.2]
  simp only [bridgeSchauderLevel, map_smul, map_sum, coordinateFunctional_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

def bridgeScalarL2Partial (n N : ℕ) (p : ℝ × Fin n) : Lp ℝ 2 (bridgeCoefficientMeasure n) :=
  ∑ j ∈ Finset.range N, bridgeScalarLevelL2 n p.2 j p.1

theorem bridgeScalarL2Partial_coe (n N : ℕ) (p : ℝ × Fin n) :
    (bridgeScalarL2Partial n N p :
      (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) → ℝ) =ᵐ[bridgeCoefficientMeasure n]
        bridgeScalarPartialEval n N p := by
  have hlevels : ∀ᵐ ω ∂bridgeCoefficientMeasure n, ∀ j : ℕ,
      bridgeScalarLevelL2 n p.2 j p.1 ω = bridgeSchauderLevel n j ω p.1 p.2 :=
    ae_all_iff.mpr (fun j => bridgeScalarLevelL2_coe n p.2 j p.1)
  filter_upwards [Lp.coeFn_finsetSum (Finset.range N)
    (fun j => bridgeScalarLevelL2 n p.2 j p.1), hlevels] with ω hsum hlevels
  change (∑ j ∈ Finset.range N, bridgeScalarLevelL2 n p.2 j p.1) ω = _
  rw [hsum]
  simp only [Finset.sum_apply, bridgeScalarPartialEval]
  exact Finset.sum_congr rfl (fun j _ => hlevels j)

theorem bridgeScalarL2Partial_gaussian_process (n N : ℕ) :
    IsGaussianProcess (fun p : ℝ × Fin n =>
      (bridgeScalarL2Partial n N p :
        (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) → ℝ))
      (bridgeCoefficientMeasure n) :=
  (bridgeScalarPartialEval_gaussian_process n N).congr (fun p => (bridgeScalarL2Partial_coe n N p).symm)

theorem bridgeScalarL2Partial_tendsto (n : ℕ) (p : ℝ × Fin n) :
    Tendsto (fun N => bridgeScalarL2Partial n N p) atTop (𝓝 (bridgeScalarL2Series n p.2 p.1)) :=
  (bridgeScalarLevelL2_summable n p.2 p.1).hasSum.tendsto_sum_nat

theorem bridgeScalarL2Series_gaussian_process (n : ℕ) :
    IsGaussianProcess (fun p : ℝ × Fin n =>
      (bridgeScalarL2Series n p.2 p.1 :
        (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) → ℝ))
      (bridgeCoefficientMeasure n) := by
  exact isGaussianProcess_of_tendsto_L2 (fun N p => bridgeScalarL2Partial n N p)
    (fun p => bridgeScalarL2Series n p.2 p.1)
    (bridgeScalarL2Partial_gaussian_process n) (bridgeScalarL2Partial_tendsto n)

theorem bridgeContinuousSeries_gaussian_process (n : ℕ) :
    IsGaussianProcess (fun p : Icc (0 : ℝ) 1 × Fin n =>
      (fun ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n) => bridgeContinuousSeries n ω p.1 p.2))
      (bridgeCoefficientMeasure n) := by
  have h := (bridgeScalarL2Series_gaussian_process n).comp_right
    (fun p : Icc (0 : ℝ) 1 × Fin n => ((p.1 : ℝ), p.2))
  exact h.congr (fun p => bridgeScalarL2Series_coe n p.2 p.1)

end AffineFKProof
