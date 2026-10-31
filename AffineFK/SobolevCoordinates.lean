module

public import AffineFK.PoissonTests
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Abel

/-!
# Coordinate cutoffs in the weighted H1 completion

Coordinates are approximated by multiplication with the genuine smooth
cutoffs. The derivative formula separates the cutoff error from the
coordinate times the cutoff gradient.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology

def coordinateFunctional (n : ℕ) (i : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  toDual ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace.basisFun (Fin n) ℝ i)

theorem coordinateFunctional_apply
    (n : ℕ) (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFunctional n i x = x i := by
  exact EuclideanSpace.basisFun_inner (Fin n) ℝ x i

theorem coordinateFunctional_gradient
    (n : ℕ) (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (coordinateFunctional n i) x = EuclideanSpace.basisFun (Fin n) ℝ i := by
  rw [gradient, (coordinateFunctional n i).fderiv]
  exact (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm_apply_apply _

def coordinateCutoff
    (n : ℕ) (i : Fin n) (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (k : ℕ) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  ⟨(coordinateFunctional n i : EuclideanSpace ℝ (Fin n) → ℝ) *
      (cutoffSequence χ k : EuclideanSpace ℝ (Fin n) → ℝ),
    (coordinateFunctional n i).contDiff.mul (cutoffSequence χ k).contDiff,
    (cutoffSequence χ k).hasCompactSupport.mul_left, Set.subset_univ _⟩

theorem coordinateCutoff_apply
    (n : ℕ) (i : Fin n) (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateCutoff n i χ k x = x i * cutoffSequence χ k x := by
  change ((coordinateFunctional n i : EuclideanSpace ℝ (Fin n) → ℝ) *
    (cutoffSequence χ k : EuclideanSpace ℝ (Fin n) → ℝ)) x = _
  rw [Pi.mul_apply, coordinateFunctional_apply]

theorem coordinateCutoff_gradient
    (n : ℕ) (i : Fin n) (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (coordinateCutoff n i χ k) x =
      (cutoffSequence χ k x) • EuclideanSpace.basisFun (Fin n) ℝ i +
        (x i) • gradient (cutoffSequence χ k) x := by
  have hc : HasFDerivAt (coordinateFunctional n i) (coordinateFunctional n i) x :=
    (coordinateFunctional n i).hasFDerivAt
  have hχ : HasFDerivAt (cutoffSequence χ k) (fderiv ℝ (cutoffSequence χ k) x) x :=
    ((cutoffSequence χ k).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hm := hc.mul hχ
  change (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ ((coordinateFunctional n i : EuclideanSpace ℝ (Fin n) → ℝ) *
      (cutoffSequence χ k : EuclideanSpace ℝ (Fin n) → ℝ)) x) = _
  rw [hm.fderiv, map_add, map_smul, map_smul]
  have hinv : (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (coordinateFunctional n i) =
      EuclideanSpace.basisFun (Fin n) ℝ i :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm_apply_apply _
  rw [hinv]
  change (coordinateFunctional n i x) • gradient (cutoffSequence χ k) x +
    (cutoffSequence χ k x) • EuclideanSpace.basisFun (Fin n) ℝ i = _
  rw [coordinateFunctional_apply]
  exact add_comm _ _

theorem coordinateCutoff_gradient_error
    (n : ℕ) (i : Fin n) (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (coordinateCutoff n i χ k) x - EuclideanSpace.basisFun (Fin n) ℝ i =
      (cutoffSequence χ k x - 1) • EuclideanSpace.basisFun (Fin n) ℝ i +
        (x i) • gradient (cutoffSequence χ k) x := by
  rw [coordinateCutoff_gradient, sub_smul, one_smul]
  abel

theorem norm_add_sq_bound
    {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := (sq_le_sq₀ (norm_nonneg (a + b))
    (add_nonneg (norm_nonneg a) (norm_nonneg b))).mpr (norm_add_le a b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem coordinateCutoff_gradient_error_bound
    (n : ℕ) (i : Fin n) (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, ‖gradient χ x‖ ≤ M)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient (coordinateCutoff n i χ k) x - EuclideanSpace.basisFun (Fin n) ℝ i‖ ^ 2 ≤
      2 * (cutoffSequence χ k x - 1) ^ 2 +
        2 * (x i) ^ 2 * (M / ((k : ℝ) + 1)) ^ 2 := by
  rw [coordinateCutoff_gradient_error]
  have hsum := norm_add_sq_bound
    ((cutoffSequence χ k x - 1) • EuclideanSpace.basisFun (Fin n) ℝ i)
    ((x i) • gradient (cutoffSequence χ k) x)
  have ha : ‖(cutoffSequence χ k x - 1) • EuclideanSpace.basisFun (Fin n) ℝ i‖ ^ 2 =
      (cutoffSequence χ k x - 1) ^ 2 := by
    rw [norm_smul, (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one, mul_one,
      Real.norm_eq_abs, sq_abs]
  have hr : 0 < (k : ℝ) + 1 := by positivity
  have hg : ‖gradient (cutoffSequence χ k) x‖ ≤ M / ((k : ℝ) + 1) :=
    gradient_scaledTestFunction_bound _ hr χ M hM x
  have hb : ‖(x i) • gradient (cutoffSequence χ k) x‖ ^ 2 ≤
      (x i) ^ 2 * (M / ((k : ℝ) + 1)) ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (div_nonneg hM0 hr.le)).mpr hg) (sq_nonneg _)
  rw [ha] at hsum
  nlinarith [hb]

/-- Finite second moment gives the actual L2 coordinate limit of the smooth
coordinate cutoffs. No fourth-moment or bounded-support assumption is needed. -/
theorem coordinateCutoff_tendsto_L2_value
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    Tendsto (fun k => testFunctionToL2 ν (coordinateCutoff n i χ k)) Filter.atTop
      (𝓝 (hxi.toLp (fun x => x i))) := by
  let F : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun k x => (x i * (cutoffSequence χ k x - 1)) ^ 2
  have hcoord : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) := by
    have heq : (coordinateFunctional n i : EuclideanSpace ℝ (Fin n) → ℝ) = (fun x => x i) :=
      funext (coordinateFunctional_apply n i)
    rw [← heq]
    exact (coordinateFunctional n i).continuous
  have hmeas (k : ℕ) : AEStronglyMeasurable (F k) ν :=
    ((hcoord.mul ((cutoffSequence χ k).continuous.sub continuous_const)).pow 2).aestronglyMeasurable
  have hintbound : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2) ν := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hxi.aestronglyMeasurable).mp hxi
  have hbound (k : ℕ) : ∀ᵐ x ∂ν, ‖F k x‖ ≤ (x i) ^ 2 := by
    filter_upwards [] with x
    dsimp [F]
    rw [abs_of_nonneg (sq_nonneg _)]
    have hc : (cutoffSequence χ k x - 1) ^ 2 ≤ 1 := by
      rw [cutoffSequence_apply]
      obtain ⟨hlo, hhi⟩ := hχ (((k : ℝ) + 1)⁻¹ • x)
      nlinarith
    simpa only [mul_pow, mul_one] using mul_le_mul_of_nonneg_left hc (sq_nonneg (x i))
  have hpoint : ∀ᵐ x ∂ν, Tendsto (fun k => F k x) Filter.atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with x
    have hx : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x) Filter.atTop
        (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
      simpa only [zero_smul] using tendsto_inverse_succ.smul_const x
    have hc : Tendsto (fun k => cutoffSequence χ k x) Filter.atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, cutoffSequence_apply, hχ0] using (χ.continuous.tendsto 0).comp hx
    simpa only [F, sub_self, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (tendsto_const_nhds.mul (hc.sub_const 1)).pow 2
  have hint := tendsto_integral_of_dominated_convergence _ hmeas hintbound hbound hpoint
  have hnorm (k : ℕ) :
      ‖testFunctionToL2 ν (coordinateCutoff n i χ k) - hxi.toLp (fun x => x i)‖ ^ 2 =
        ∫ x, F k x ∂ν := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (testFunctionToL2 ν (coordinateCutoff n i χ k))
      (hxi.toLp (fun x => x i)), testFunctionToL2_coe ν (coordinateCutoff n i χ k),
      hxi.coeFn_toLp] with x hd hc hx
    rw [hd]
    simp only [Pi.sub_apply]
    rw [hc, hx, coordinateCutoff_apply]
    have hfactor : x i * cutoffSequence χ k x - x i = x i * (cutoffSequence χ k x - 1) := by ring
    rw [hfactor]
    simp only [Real.norm_eq_abs, sq_abs, F]
  have hsquare : Tendsto (fun k =>
      ‖testFunctionToL2 ν (coordinateCutoff n i χ k) - hxi.toLp (fun x => x i)‖ ^ 2)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [hnorm, integral_zero] using hint
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

/-- The coordinate-gradient error converges in L2 under the same second
moment assumption used for the coordinate value. -/
theorem coordinateCutoff_tendsto_L2_gradient
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, ‖gradient χ x‖ ≤ M) :
    Tendsto (fun k => testFunctionToL2 ν (testFunctionGradient (coordinateCutoff n i χ k)))
      atTop (𝓝 (Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i))) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ i
  let F : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun k x => ‖gradient (coordinateCutoff n i χ k) x - e‖ ^ 2
  have hcoord : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) := by
    have heq : (coordinateFunctional n i : EuclideanSpace ℝ (Fin n) → ℝ) = (fun x => x i) :=
      funext (coordinateFunctional_apply n i)
    rw [← heq]
    exact (coordinateFunctional n i).continuous
  have hmeas (k : ℕ) : AEStronglyMeasurable (F k) ν := by
    have hg : Continuous (fun x => gradient (coordinateCutoff n i χ k) x) := by
      have heq : (fun x => gradient (coordinateCutoff n i χ k) x) =
          (testFunctionGradient (coordinateCutoff n i χ k) :
            EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
        funext x
        exact (testFunctionGradient_apply _ x).symm
      rw [heq]
      exact (testFunctionGradient (coordinateCutoff n i χ k)).continuous
    exact ((hg.sub continuous_const).norm.pow 2).aestronglyMeasurable
  have hintxi : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2) ν := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hxi.aestronglyMeasurable).mp hxi
  have hintbound : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      2 + (2 * M ^ 2) * (x i) ^ 2) ν :=
    (integrable_const _).add (hintxi.const_mul _)
  have hbound (k : ℕ) : ∀ᵐ x ∂ν, ‖F k x‖ ≤ 2 + (2 * M ^ 2) * (x i) ^ 2 := by
    filter_upwards [] with x
    dsimp [F, e]
    rw [abs_of_nonneg (sq_nonneg _)]
    have hc : (cutoffSequence χ k x - 1) ^ 2 ≤ 1 := by
      rw [cutoffSequence_apply]
      obtain ⟨hlo, hhi⟩ := hχ (((k : ℝ) + 1)⁻¹ • x)
      nlinarith
    have hr : 0 < (k : ℝ) + 1 := by positivity
    have hd : M / ((k : ℝ) + 1) ≤ M := by
      apply (div_le_iff₀ hr).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hs := (sq_le_sq₀ (div_nonneg hM0 hr.le) hM0).mpr hd
    have hprod := mul_le_mul_of_nonneg_left hs
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (x i)))
    have hb := coordinateCutoff_gradient_error_bound n i χ M hM0 hM k x
    nlinarith
  have hpoint : ∀ᵐ x ∂ν, Tendsto (fun k => F k x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with x
    have hx : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x) atTop
        (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
      simpa only [zero_smul] using tendsto_inverse_succ.smul_const x
    have hc : Tendsto (fun k => cutoffSequence χ k x) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, cutoffSequence_apply, hχ0] using
        (χ.continuous.tendsto 0).comp hx
    have hg : Tendsto (fun k => gradient (cutoffSequence χ k) x) atTop
        (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
      have hnorm := squeeze_zero (fun _k => norm_nonneg _)
        (fun k => gradient_scaledTestFunction_bound _ (by positivity) χ M hM x)
        (show Tendsto (fun k : ℕ => M / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) from by
          simpa only [div_eq_mul_inv, mul_zero] using
            tendsto_const_nhds.mul tendsto_inverse_succ)
      exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    have herr : Tendsto (fun k => gradient (coordinateCutoff n i χ k) x - e)
        atTop (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
      simpa only [coordinateCutoff_gradient_error, e, sub_self, zero_smul,
        smul_zero, zero_add] using ((hc.sub_const 1).smul_const e).add (hg.const_smul (x i))
    simpa only [F, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using herr.norm.pow 2
  have hint := tendsto_integral_of_dominated_convergence _ hmeas hintbound hbound hpoint
  have hnorm (k : ℕ) :
      ‖testFunctionToL2 ν (testFunctionGradient (coordinateCutoff n i χ k)) -
        Lp.const 2 ν e‖ ^ 2 = ∫ x, F k x ∂ν := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub
      (testFunctionToL2 ν (testFunctionGradient (coordinateCutoff n i χ k))) (Lp.const 2 ν e),
      testFunctionToL2_coe ν (testFunctionGradient (coordinateCutoff n i χ k)),
      Lp.coeFn_const 2 ν e] with x hd hc he
    rw [hd]
    simp only [Pi.sub_apply]
    rw [hc, he, testFunctionGradient_apply]
    rfl
  have hsquare : Tendsto (fun k =>
      ‖testFunctionToL2 ν (testFunctionGradient (coordinateCutoff n i χ k)) -
        Lp.const 2 ν e‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hnorm, integral_zero] using hint
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

/-- A coordinate and its genuine constant gradient belong to the constructed
Sobolev completion whenever that coordinate has finite second moment. -/
theorem coordinate_mem_sobolevGraph
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν) :
    WithLp.toLp 2 (hxi.toLp (fun x => x i),
      Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)) ∈ weightedSobolevGraph ν := by
  obtain ⟨χ, hχ, hinner, _houter, M, hM0, hM⟩ := exists_smooth_unit_cutoff n
  have hχ0 : χ 0 = 1 := hinner 0 (by simp)
  have hvalue := coordinateCutoff_tendsto_L2_value n ν i hxi χ hχ0 hχ
  have hgradient := coordinateCutoff_tendsto_L2_gradient n ν i hxi χ hχ0 hχ M hM0 hM
  have hpair : Tendsto (fun k => smoothGradientPair ν (coordinateCutoff n i χ k)) atTop
      (𝓝 (WithLp.toLp 2 (hxi.toLp (fun x => x i),
        Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)))) := by
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 ν)
      (Lp (EuclideanSpace ℝ (Fin n)) 2 ν)).symm.continuous.tendsto _).comp
        (hvalue.prodMk_nhds hgradient)
  exact (weightedSobolevGraph_isClosed ν).mem_of_tendsto hpair
    (Eventually.of_forall fun k => smoothGradientPair_mem ν (coordinateCutoff n i χ k))

def sobolevCoordinate
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν) :
    weightedSobolevGraph ν :=
  ⟨WithLp.toLp 2 (hxi.toLp (fun x => x i), Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i)),
    coordinate_mem_sobolevGraph n ν i hxi⟩

theorem sobolevCoordinate_value
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν) :
    sobolevValue ν (sobolevCoordinate n ν i hxi) = hxi.toLp (fun x => x i) := by rfl

theorem sobolevCoordinate_gradient
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν) :
    sobolevGradient ν (sobolevCoordinate n ν i hxi) =
      Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i) := by rfl

end AffineFKProof
