module

public import AffineFK.SobolevCutoff
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# The constant function in the weighted H1 completion

Smooth compactly supported cutoffs converge to one in L2, while their actual
gradients converge to zero in L2. Dominated convergence and the uniform
M/R gradient estimate supply the two limits.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Filter
open scoped Distributions Topology

def cutoffSequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : 𝓓((⊤ : Opens E), ℝ)) (k : ℕ) : 𝓓((⊤ : Opens E), ℝ) :=
  scaledTestFunction ((k : ℝ) + 1) (by positivity) χ

theorem cutoffSequence_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : 𝓓((⊤ : Opens E), ℝ)) (k : ℕ) (x : E) :
    cutoffSequence χ k x = χ (((k : ℝ) + 1)⁻¹ • x) := by
  rfl

theorem tendsto_inverse_succ :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

theorem cutoffSequence_tendsto_L2_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (χ : 𝓓((⊤ : Opens E), ℝ)) (hχ0 : χ 0 = 1)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    Tendsto (fun k => testFunctionToL2 ν (cutoffSequence χ k)) atTop
      (𝓝 (Lp.const 2 ν (1 : ℝ))) := by
  let F : ℕ → E → ℝ := fun k x => (cutoffSequence χ k x - 1) ^ 2
  have hmeas (k : ℕ) : AEStronglyMeasurable (F k) ν :=
    (((cutoffSequence χ k).continuous.sub continuous_const).pow 2).aestronglyMeasurable
  have hbound (k : ℕ) : ∀ᵐ x ∂ν, ‖F k x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    dsimp [F]
    rw [abs_of_nonneg (sq_nonneg _), cutoffSequence_apply]
    obtain ⟨hlo, hhi⟩ := hχ (((k : ℝ) + 1)⁻¹ • x)
    nlinarith
  have hpoint : ∀ᵐ x ∂ν, Tendsto (fun k => F k x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with x
    have hx : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x) atTop (𝓝 (0 : E)) := by
      simpa only [zero_smul] using tendsto_inverse_succ.smul_const x
    have hc : Tendsto (fun k => cutoffSequence χ k x) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, cutoffSequence_apply, hχ0] using (χ.continuous.tendsto 0).comp hx
    simpa only [F, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hc.sub_const 1).pow 2
  have hint := tendsto_integral_of_dominated_convergence (fun _ : E => (1 : ℝ))
    hmeas (integrable_const _) hbound hpoint
  have hnorm (k : ℕ) :
      ‖testFunctionToL2 ν (cutoffSequence χ k) - Lp.const 2 ν (1 : ℝ)‖ ^ 2 =
        ∫ x, F k x ∂ν := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (testFunctionToL2 ν (cutoffSequence χ k)) (Lp.const 2 ν (1 : ℝ)),
      testFunctionToL2_coe ν (cutoffSequence χ k), Lp.coeFn_const 2 ν (1 : ℝ)] with x hd hc h1
    rw [hd]
    simp only [Pi.sub_apply]
    rw [hc, h1]
    simp only [Function.const_apply, Real.norm_eq_abs, sq_abs, F]
  have hsquare : Tendsto (fun k =>
      ‖testFunctionToL2 ν (cutoffSequence χ k) - Lp.const 2 ν (1 : ℝ)‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hnorm, integral_zero] using hint
  have hnormzero := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  have hnormlimit : Tendsto (fun k =>
      ‖testFunctionToL2 ν (cutoffSequence χ k) - Lp.const 2 ν (1 : ℝ)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hnormzero
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnormlimit

theorem cutoffSequence_gradient_tendsto_L2_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (χ : 𝓓((⊤ : Opens E), ℝ)) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ x, ‖gradient χ x‖ ≤ M) :
    Tendsto (fun k => testFunctionToL2 ν (testFunctionGradient (cutoffSequence χ k)))
      atTop (𝓝 (0 : Lp E 2 ν)) := by
  have hbound (k : ℕ) :
      ‖testFunctionToL2 ν (testFunctionGradient (cutoffSequence χ k))‖ ≤ M / ((k : ℝ) + 1) := by
    have hr : 0 < (k : ℝ) + 1 := by positivity
    have h := Lp.norm_le_of_ae_bound (f := testFunctionToL2 ν (testFunctionGradient (cutoffSequence χ k)))
      (div_nonneg hM0 hr.le) (by
        filter_upwards [testFunctionToL2_coe ν (testFunctionGradient (cutoffSequence χ k))] with x hx
        rw [hx, testFunctionGradient_apply]
        exact gradient_scaledTestFunction_bound _ hr χ M hM x)
    simpa [measureUnivNNReal] using h
  have hlimit : Tendsto (fun k : ℕ => M / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul tendsto_inverse_succ
  have hnorm := squeeze_zero (fun _k => norm_nonneg _) hbound hlimit
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- The constant-one function with zero gradient belongs to the actual H1
completion, by a sequence of genuine compactly supported smooth cutoffs. -/
theorem constant_one_mem_sobolevGraph
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] :
    WithLp.toLp 2 (Lp.const 2 ν (1 : ℝ), (0 : Lp (EuclideanSpace ℝ (Fin n)) 2 ν)) ∈
      weightedSobolevGraph ν := by
  obtain ⟨χ, hχ, hinner, _houter, M, hM0, hM⟩ := exists_smooth_unit_cutoff n
  have hχ0 : χ 0 = 1 := hinner 0 (by simp)
  have hvalue := cutoffSequence_tendsto_L2_one ν χ hχ0 hχ
  have hgradient := cutoffSequence_gradient_tendsto_L2_zero ν χ M hM0 hM
  have hpair : Tendsto (fun k => smoothGradientPair ν (cutoffSequence χ k)) atTop
      (𝓝 (WithLp.toLp 2 (Lp.const 2 ν (1 : ℝ), (0 : Lp (EuclideanSpace ℝ (Fin n)) 2 ν)))) := by
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 ν)
      (Lp (EuclideanSpace ℝ (Fin n)) 2 ν)).symm.continuous.tendsto _).comp
        (hvalue.prodMk_nhds hgradient)
  exact (weightedSobolevGraph_isClosed ν).mem_of_tendsto hpair
    (Eventually.of_forall fun k => smoothGradientPair_mem ν (cutoffSequence χ k))

/-- The canonical constant-one element of the constructed H1 completion. -/
def sobolevOne (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] :
    weightedSobolevGraph ν :=
  ⟨WithLp.toLp 2 (Lp.const 2 ν (1 : ℝ), 0), constant_one_mem_sobolevGraph n ν⟩

theorem sobolevOne_value
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] :
    sobolevValue ν (sobolevOne n ν) = Lp.const 2 ν (1 : ℝ) := by
  rfl

theorem sobolevOne_gradient
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] :
    sobolevGradient ν (sobolevOne n ν) = 0 := by
  rfl

theorem sobolevOne_mean
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] :
    l2Mean ν (sobolevValue ν (sobolevOne n ν)) = 1 := by
  rw [sobolevOne_value, l2Mean_apply]
  calc
    _ = ∫ _x, (1 : ℝ) ∂ν := integral_congr_ae (Lp.coeFn_const 2 ν (1 : ℝ))
    _ = _ := by simp

end AffineFKProof
