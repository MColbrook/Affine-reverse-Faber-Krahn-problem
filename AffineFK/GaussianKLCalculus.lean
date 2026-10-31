module

public import AffineFK.GaussianMixtureEntropy
public import AffineFK.L2Coordinates
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# The exact Gaussian joint relative-entropy calculation

Only the original vector's second moment is required. All log-likelihood
ratios are proved integrable before using the genuine extended-valued
Kullback--Leibler formula. Gaussian moments reuse Mathlib's actual standard
Gaussian mean/covariance results; no Gaussian KL formula is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace

theorem gaussian_entropy_coordinate_second_moment (n : ℕ) (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), (x i) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 1 := by
  have hmean := integral_strongDual_stdGaussian (coordinateFunctional n i)
  have hv := variance_dual_stdGaussian (coordinateFunctional n i)
  rw [variance_of_integral_eq_zero (coordinateFunctional n i).continuous.measurable.aemeasurable hmean] at hv
  simp only [coordinateFunctional_apply] at hv
  simpa [coordinateFunctional] using hv

theorem gaussian_entropy_norm_second_moment (n : ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = n := by
  have hG : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := IsGaussian.memLp_id _ 2 (by norm_num)
  refine ⟨(memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG, ?_⟩
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ => (hG.eval_piLp i).integrable_sq)]
  simp only [gaussian_entropy_coordinate_second_moment, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem gaussian_entropy_product_inner (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : MemLp (fun u : EuclideanSpace ℝ (Fin n) => u) 2 ν) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ⟪p.1, p.2⟫)
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), ⟪p.1, p.2⟫
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) = 0 := by
  have hG : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := IsGaussian.memLp_id _ 2 (by norm_num)
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ⟪p.1, p.2⟫)
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := memLp_one_iff_integrable.mp
    ((innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).memLp_of_bilin
      1 (hU.comp_fst _) (hG.comp_snd ν))
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint]
  have hzero (u : EuclideanSpace ℝ (Fin n)) :
      (∫ g, ⟪u, g⟫ ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
    have h := (innerSL ℝ u).integral_comp_comm (hG.integrable (by norm_num))
    simpa only [innerSL_apply_apply, integral_id_stdGaussian, map_zero] using h
  simp_rw [hzero]
  exact integral_zero _ _

theorem gaussian_entropy_smoothed_second_moment (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : MemLp (fun u : EuclideanSpace ℝ (Fin n) => u) 2 ν) (a b : ℝ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖a • p.1 + b • p.2‖ ^ 2) (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), ‖a • p.1 + b • p.2‖ ^ 2
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) = a ^ 2 * (∫ u, ‖u‖ ^ 2 ∂ν) + b ^ 2 * n := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hG : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x) 2 γ :=
    IsGaussian.memLp_id _ 2 (by norm_num)
  have hUf := hU.comp_fst γ
  have hGs := hG.comp_snd ν
  have hUsq := (memLp_two_iff_integrable_sq_norm hUf.aestronglyMeasurable).mp hUf
  have hGsq := (memLp_two_iff_integrable_sq_norm hGs.aestronglyMeasurable).mp hGs
  have hmix := gaussian_entropy_product_inner n ν hU
  have hW := (hUf.const_smul a).add (hGs.const_smul b)
  refine ⟨(memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW, ?_⟩
  have heq : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖a • p.1 + b • p.2‖ ^ 2) =
      (fun p => a ^ 2 * ‖p.1‖ ^ 2 + (2 * a * b) * ⟪p.1, p.2⟫ + b ^ 2 * ‖p.2‖ ^ 2) := by
    funext p
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
    simp only [mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [heq, integral_add
    (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      a ^ 2 * ‖p.1‖ ^ 2 + (2 * a * b) * ⟪p.1, p.2⟫)
    (g := fun p => b ^ 2 * ‖p.2‖ ^ 2)
    ((hUsq.const_mul (a ^ 2)).add (hmix.1.const_mul (2 * a * b)))
    (hGsq.const_mul (b ^ 2)), integral_add (hUsq.const_mul (a ^ 2)) (hmix.1.const_mul (2 * a * b))]
  rw [integral_const_mul, integral_const_mul, integral_const_mul, hmix.2]
  simp only [mul_zero, add_zero]
  have hfst : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), ‖p.1‖ ^ 2 ∂ν.prod γ) =
      ∫ u, ‖u‖ ^ 2 ∂ν := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_fst (μ := ν) (ν := γ) (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ ^ 2))
  have hsnd : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), ‖p.2‖ ^ 2 ∂ν.prod γ) = n := by
    calc
      _ = ∫ g, ‖g‖ ^ 2 ∂γ := by
        simpa only [probReal_univ, one_smul] using
          (integral_fun_snd (μ := ν) (ν := γ) (fun g : EuclideanSpace ℝ (Fin n) => ‖g‖ ^ 2))
      _ = _ := (gaussian_entropy_norm_second_moment n).2
  rw [hfst, hsnd]

theorem log_gaussianJointRatio_affine (n : ℕ) (a b : ℝ) (hb : 0 < b)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    Real.log (gaussianJointRatio n a b (gaussianJointAffineMap n a b p)) =
      -(n : ℝ) * Real.log b + (‖a • p.1 + b • p.2‖ ^ 2 - ‖p.2‖ ^ 2) / 2 := by
  unfold gaussianJointRatio gaussianJointAffineMap
  dsimp only
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hb.ne', one_smul,
    Real.log_div (mul_ne_zero (inv_ne_zero (pow_ne_zero n hb.ne')) (standardGaussianDensity_pos n _).ne')
      (standardGaussianDensity_pos n _).ne',
    Real.log_mul (inv_ne_zero (pow_ne_zero n hb.ne')) (standardGaussianDensity_pos n _).ne',
    Real.log_inv, Real.log_pow, log_standardGaussianDensity, log_standardGaussianDensity]
  ring

theorem gaussian_joint_klDiv_exact (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : MemLp (fun u : EuclideanSpace ℝ (Fin n) => u) 2 ν)
    (a b : ℝ) (hb : 0 < b) :
    klDiv ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (gaussianJointAffineMap n a b)) (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      ENNReal.ofReal ((1 / 2 : ℝ) * (a ^ 2 * (∫ u, ‖u‖ ^ 2 ∂ν) +
        n * (b ^ 2 - 1 - Real.log (b ^ 2)))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let μ := ν.prod γ
  let P := μ.map (gaussianJointAffineMap n a b)
  have hT : Measurable (gaussianJointAffineMap n a b) := by unfold gaussianJointAffineMap; fun_prop
  have hR : Measurable (fun p => ENNReal.ofReal (gaussianJointRatio n a b p)) :=
    (gaussianJointRatio_continuous n a b).measurable.ennreal_ofReal
  have heq : P = μ.withDensity (fun p => ENNReal.ofReal (gaussianJointRatio n a b p)) :=
    gaussian_joint_affine_withDensity n ν a b hb
  have hac : P ≪ μ := gaussian_joint_affine_ac n ν a b hb
  have hrn : P.rnDeriv μ =ᵐ[μ] (fun p => ENNReal.ofReal (gaussianJointRatio n a b p)) := by
    have h := Measure.rnDeriv_withDensity μ hR
    rw [← heq] at h
    exact h
  have hllr : llr P μ =ᵐ[P] (fun p => Real.log (gaussianJointRatio n a b p)) := by
    filter_upwards [hac.ae_le hrn] with p hp
    simp only [llr, hp, ENNReal.toReal_ofReal (gaussianJointRatio_pos n a b hb p).le]
  have hlog : StronglyMeasurable (fun p => Real.log (gaussianJointRatio n a b p)) :=
    ((gaussianJointRatio_continuous n a b).log (fun p => (gaussianJointRatio_pos n a b hb p).ne')).stronglyMeasurable
  have hW := gaussian_entropy_smoothed_second_moment n ν hU a b
  have hGsq : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖p.2‖ ^ 2) μ :=
    (gaussian_entropy_norm_second_moment n).1.comp_snd ν
  have hpoly : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      -(n : ℝ) * Real.log b + (‖a • p.1 + b • p.2‖ ^ 2 - ‖p.2‖ ^ 2) / 2) μ :=
    (integrable_const _).add ((hW.1.sub hGsq).div_const 2)
  have hlogP : Integrable (fun p => Real.log (gaussianJointRatio n a b p)) P := by
    apply (integrable_map_measure hlog.aestronglyMeasurable hT.aemeasurable).mpr
    exact hpoly.congr (Filter.Eventually.of_forall fun p => (log_gaussianJointRatio_affine n a b hb p).symm)
  have hllrP : Integrable (llr P μ) P := hlogP.congr hllr.symm
  change klDiv P μ = _
  rw [klDiv_of_ac_of_integrable hac hllrP]
  simp only [probReal_univ, add_sub_cancel_right]
  congr 1
  rw [integral_congr_ae hllr, integral_map hT.aemeasurable hlog.aestronglyMeasurable]
  calc
    _ = ∫ p, -(n : ℝ) * Real.log b + (‖a • p.1 + b • p.2‖ ^ 2 - ‖p.2‖ ^ 2) / 2 ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun p => log_gaussianJointRatio_affine n a b hb p)
    _ = -(n : ℝ) * Real.log b +
        ((∫ p, ‖a • p.1 + b • p.2‖ ^ 2 ∂μ) - (∫ p, ‖p.2‖ ^ 2 ∂μ)) / 2 := by
      rw [integral_add (μ := μ)
        (f := fun _ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => -(n : ℝ) * Real.log b)
        (g := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (‖a • p.1 + b • p.2‖ ^ 2 - ‖p.2‖ ^ 2) / 2)
        (integrable_const _) ((hW.1.sub hGsq).div_const 2),
        integral_const, integral_div 2
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖a • p.1 + b • p.2‖ ^ 2 - ‖p.2‖ ^ 2),
        integral_sub hW.1 hGsq]
      simp only [probReal_univ, one_smul]
      rfl
    _ = _ := by
      rw [hW.2]
      have hgm : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), ‖p.2‖ ^ 2 ∂μ) = n := by
        calc
          _ = ∫ g, ‖g‖ ^ 2 ∂γ := by
            simpa only [probReal_univ, one_smul] using
              (integral_fun_snd (μ := ν) (ν := γ) (fun g : EuclideanSpace ℝ (Fin n) => ‖g‖ ^ 2))
          _ = _ := (gaussian_entropy_norm_second_moment n).2
      rw [hgm, Real.log_pow]
      ring

end AffineFKProof
