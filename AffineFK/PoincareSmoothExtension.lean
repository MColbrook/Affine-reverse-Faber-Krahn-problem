module

public import AffineFK.SobolevCoordinates
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Smooth L2 functions and extension of the Poincare inequality

Multiplication by the existing genuine smooth cutoffs approximates both a
smooth function and its actual gradient in L2. The Poincare inequality then
follows from the already proved continuous extension to the Sobolev graph.
The dominated-convergence and L2-space results are reused from Mathlib.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter ProbabilityTheory
open scoped Distributions RealInnerProductSpace Topology ContDiff

theorem poincareSmoothExtension_L2_tendsto
    {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (ν : Measure X) (v : ℕ → Lp F 2 ν) (w : Lp F 2 ν)
    (fs : ℕ → X → F) (f : X → F)
    (hv : ∀ k, v k =ᵐ[ν] fs k) (hw : w =ᵐ[ν] f)
    (B : X → ℝ) (hB : Integrable B ν)
    (hbound : ∀ k, ∀ᵐ x ∂ν, ‖fs k x - f x‖ ^ 2 ≤ B x)
    (hpoint : ∀ᵐ x ∂ν, Tendsto (fun k => fs k x) atTop (𝓝 (f x))) :
    Tendsto v atTop (𝓝 w) := by
  let H : ℕ → X → ℝ := fun k x => ‖fs k x - f x‖ ^ 2
  have hmeas (k) : AEStronglyMeasurable (H k) ν :=
    ((((Lp.aestronglyMeasurable (v k)).congr (hv k)).sub
      ((Lp.aestronglyMeasurable w).congr hw)).norm.pow 2)
  have hbound' (k) : ∀ᵐ x ∂ν, ‖H k x‖ ≤ B x := by
    filter_upwards [hbound k] with x hx
    change |‖fs k x - f x‖ ^ 2| ≤ B x
    rwa [abs_of_nonneg (sq_nonneg _)]
  have hpoint' : ∀ᵐ x ∂ν, Tendsto (fun k => H k x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hpoint] with x hx
    simpa only [H, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((hx.sub_const (f x)).norm.pow 2)
  have hint := tendsto_integral_of_dominated_convergence B hmeas hB hbound' hpoint'
  have hnorm (k) : ‖v k - w‖ ^ 2 = ∫ x, H k x ∂ν := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (v k) w, hv k, hw] with x hx hvx hwx
    rw [hx]
    simp only [Pi.sub_apply, hvx, hwx, H]
  have hsquare : Tendsto (fun k => ‖v k - w‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hnorm, integral_zero] using hint
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

def poincareSmoothCutoff (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (k : ℕ) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  ⟨f * (cutoffSequence χ k : EuclideanSpace ℝ (Fin n) → ℝ),
    hf.mul (cutoffSequence χ k).contDiff,
    (cutoffSequence χ k).hasCompactSupport.mul_left, Set.subset_univ _⟩

theorem poincareSmoothCutoff_apply (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    poincareSmoothCutoff n f hf χ k x = f x * cutoffSequence χ k x := rfl

theorem poincareSmoothCutoff_gradient (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (poincareSmoothCutoff n f hf χ k) x =
      cutoffSequence χ k x • gradient f x + f x • gradient (cutoffSequence χ k) x := by
  have hm := ((hf.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt.mul
    (((cutoffSequence χ k).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt)
  change (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ (f * (cutoffSequence χ k : EuclideanSpace ℝ (Fin n) → ℝ)) x) = _
  rw [hm.fderiv, map_add, map_smul, map_smul]
  exact add_comm _ _

theorem poincareSmoothCutoff_gradient_error (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (poincareSmoothCutoff n f hf χ k) x - gradient f x =
      (cutoffSequence χ k x - 1) • gradient f x + f x • gradient (cutoffSequence χ k) x := by
  rw [poincareSmoothCutoff_gradient, sub_smul, one_smul]
  abel

theorem poincareSmoothCutoff_pointwise (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (M : ℝ) (hM : ∀ x, ‖gradient χ x‖ ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => poincareSmoothCutoff n f hf χ k x) atTop (𝓝 (f x)) ∧
      Tendsto (fun k => gradient (poincareSmoothCutoff n f hf χ k) x) atTop (𝓝 (gradient f x)) := by
  have hx : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x) atTop
      (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
    simpa only [zero_smul] using tendsto_inverse_succ.smul_const x
  have hc : Tendsto (fun k => cutoffSequence χ k x) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, cutoffSequence_apply, hχ0] using (χ.continuous.tendsto 0).comp hx
  have hg : Tendsto (fun k => gradient (cutoffSequence χ k) x) atTop
      (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
    have hnorm := squeeze_zero (fun _ => norm_nonneg _)
      (fun k => gradient_scaledTestFunction_bound _ (by positivity) χ M hM x)
      (show Tendsto (fun k : ℕ => M / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) from by
        simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul tendsto_inverse_succ)
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  constructor
  · simpa only [poincareSmoothCutoff_apply, mul_one] using tendsto_const_nhds.mul hc
  · simpa only [poincareSmoothCutoff_gradient, one_smul, smul_zero, add_zero] using
      (hc.smul_const (gradient f x)).add (hg.const_smul (f x))

theorem poincareSmoothCutoff_bounds (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ x, ‖gradient χ x‖ ≤ M)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖poincareSmoothCutoff n f hf χ k x - f x‖ ^ 2 ≤ (f x) ^ 2 ∧
      ‖gradient (poincareSmoothCutoff n f hf χ k) x - gradient f x‖ ^ 2 ≤
        2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * (f x) ^ 2 := by
  have hc : (cutoffSequence χ k x - 1) ^ 2 ≤ 1 := by
    rw [cutoffSequence_apply]
    obtain ⟨hlo, hhi⟩ := hχ (((k : ℝ) + 1)⁻¹ • x)
    nlinarith
  have hg : ‖gradient (cutoffSequence χ k) x‖ ≤ M := by
    have hr : 0 < (k : ℝ) + 1 := by positivity
    apply (gradient_scaledTestFunction_bound _ hr χ M hM x).trans
    apply (div_le_iff₀ hr).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  constructor
  · rw [poincareSmoothCutoff_apply]
    have heq : f x * cutoffSequence χ k x - f x = f x * (cutoffSequence χ k x - 1) := by ring
    rw [heq, Real.norm_eq_abs, sq_abs, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (f x))]
  · rw [poincareSmoothCutoff_gradient_error]
    have hh := norm_add_sq_bound ((cutoffSequence χ k x - 1) • gradient f x)
      (f x • gradient (cutoffSequence χ k) x)
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hh
    have hg2 := (sq_le_sq₀ (norm_nonneg _) hM0).mpr hg
    nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg ‖gradient f x‖),
      mul_le_mul_of_nonneg_left hg2 (sq_nonneg (f x))]

theorem poincareSmoothExtension_mem_graph (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hL2 : MemLp f 2 ν) (hgradL2 : MemLp (gradient f) 2 ν) :
    WithLp.toLp 2 (hL2.toLp f, hgradL2.toLp (gradient f)) ∈ weightedSobolevGraph ν := by
  obtain ⟨χ, hχ, hinner, _, M, hM0, hM⟩ := exists_smooth_unit_cutoff n
  have hχ0 : χ 0 = 1 := hinner 0 (by simp)
  have hvalue : Tendsto (fun k => testFunctionToL2 ν (poincareSmoothCutoff n f hf χ k)) atTop
      (𝓝 (hL2.toLp f)) := by
    apply poincareSmoothExtension_L2_tendsto ν _ _
      (fun k => (poincareSmoothCutoff n f hf χ k : EuclideanSpace ℝ (Fin n) → ℝ)) f
      (fun k => testFunctionToL2_coe ν _) hL2.coeFn_toLp (fun x => (f x) ^ 2)
    · simpa only [Real.norm_eq_abs, sq_abs] using
        (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2
    · exact fun k => Eventually.of_forall fun x => (poincareSmoothCutoff_bounds n f hf χ hχ M hM0 hM k x).1
    · exact Eventually.of_forall fun x => (poincareSmoothCutoff_pointwise n f hf χ hχ0 M hM x).1
  have hgradient : Tendsto (fun k => testFunctionToL2 ν
      (testFunctionGradient (poincareSmoothCutoff n f hf χ k))) atTop
      (𝓝 (hgradL2.toLp (gradient f))) := by
    apply poincareSmoothExtension_L2_tendsto ν _ _
      (fun k => gradient (poincareSmoothCutoff n f hf χ k)) (gradient f)
      (fun k => (testFunctionToL2_coe ν _).trans
        (Eventually.of_forall fun x => testFunctionGradient_apply _ x)) hgradL2.coeFn_toLp
      (fun x => 2 * ‖gradient f x‖ ^ 2 + 2 * M ^ 2 * (f x) ^ 2)
    · have hi := (memLp_two_iff_integrable_sq_norm hgradL2.aestronglyMeasurable).mp hgradL2
      have hf2 : Integrable (fun x => (f x) ^ 2) ν := by
        simpa only [Real.norm_eq_abs, sq_abs] using
          (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2
      exact (hi.const_mul 2).add (hf2.const_mul (2 * M ^ 2))
    · exact fun k => Eventually.of_forall fun x => (poincareSmoothCutoff_bounds n f hf χ hχ M hM0 hM k x).2
    · exact Eventually.of_forall fun x => (poincareSmoothCutoff_pointwise n f hf χ hχ0 M hM x).2
  have hpair : Tendsto (fun k => smoothGradientPair ν (poincareSmoothCutoff n f hf χ k)) atTop
      (𝓝 (WithLp.toLp 2 (hL2.toLp f, hgradL2.toLp (gradient f)))) := by
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 ν)
      (Lp (EuclideanSpace ℝ (Fin n)) 2 ν)).symm.continuous.tendsto _).comp
        (hvalue.prodMk_nhds hgradient)
  exact (weightedSobolevGraph_isClosed ν).mem_of_tendsto hpair
    (Eventually.of_forall fun k => smoothGradientPair_mem ν _)

theorem poincareSmoothExtension (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hL2 : MemLp f 2 ν) (hgradL2 : MemLp (gradient f) 2 ν) :
    (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν) := by
  let v : weightedSobolevGraph ν :=
    ⟨WithLp.toLp 2 (hL2.toLp f, hgradL2.toLp (gradient f)),
      poincareSmoothExtension_mem_graph n ν f hf hL2 hgradL2⟩
  have h := weighted_poincare_extension ν P (test_poincare_graph_bound ν P hP) v
  change ‖hL2.toLp f‖ ^ 2 - (l2Mean ν (hL2.toLp f)) ^ 2 ≤ P * ‖hgradL2.toLp (gradient f)‖ ^ 2 at h
  have hn : ‖hL2.toLp f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂ν := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hL2.coeFn_toLp] with x hx
    simp only [hx, Real.norm_eq_abs, sq_abs]
  have hg : ‖hgradL2.toLp (gradient f)‖ ^ 2 = ∫ x, ‖gradient f x‖ ^ 2 ∂ν := by
    rw [l2_norm_sq_integral]
    exact integral_congr_ae (hgradL2.coeFn_toLp.fun_comp fun y => ‖y‖ ^ 2)
  have hm : l2Mean ν (hL2.toLp f) = ∫ x, f x ∂ν := by
    rw [l2Mean_apply]
    exact integral_congr_ae hL2.coeFn_toLp
  rw [hn, hg, hm] at h
  have hv : (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) =
      (∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 :=
    (variance_eq_integral hL2.aemeasurable).symm.trans (variance_eq_sub hL2)
  rwa [hv]

end AffineFKProof
