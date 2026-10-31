module

public import AffineFK.GaussianVarianceRotation
public import AffineFK.GaussianSmoothingProduct
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Genuine differentiation of the Gaussian rotation covariance integral. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace ENNReal

def gaussianVarianceCorrelation (n : ℕ)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (θ : ℝ) : ℝ :=
  ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
    f p.1 * f (Real.cos θ • p.1 + Real.sin θ • p.2)
    ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))

theorem gaussianVarianceCorrelation_derivative_bound (n : ℕ)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (C D : ℝ) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hC : ∀ x, ‖f x‖ ≤ C) (hD : ∀ x, ‖gradient f x‖ ≤ D)
    (θ : ℝ) (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    ‖f p.1 * fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2)
      ((-Real.sin θ) • p.1 + Real.cos θ • p.2)‖ ≤ (C * D) * (‖p.1‖ + ‖p.2‖) := by
  have hv : ‖(-Real.sin θ) • p.1 + Real.cos θ • p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_smul, Real.norm_eq_abs, abs_neg]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (norm_nonneg p.1)
    · rw [norm_smul, Real.norm_eq_abs]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg p.2)
  have hd : ‖fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2)‖ ≤ D := by
    rw [← norm_gradient_eq_fderiv]
    exact hD _
  have hh := ((fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2)).le_opNorm
    ((-Real.sin θ) • p.1 + Real.cos θ • p.2)).trans
      (mul_le_mul hd hv (norm_nonneg _) hD0)
  rw [norm_mul]
  exact (mul_le_mul (hC p.1) hh (norm_nonneg _) hC0).trans_eq (mul_assoc _ _ _).symm

theorem gaussianVarianceCorrelation_hasDerivAt (n : ℕ)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (θ : ℝ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      f p.1 * fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2)
        ((-Real.sin θ) • p.1 + Real.cos θ • p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    HasDerivAt (gaussianVarianceCorrelation n f)
      (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        f p.1 * fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2)
          ((-Real.sin θ) • p.1 + Real.cos θ • p.2)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) θ := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let μ := γ.prod γ
  obtain ⟨C, D, hC0, hD0, hC, hD⟩ := poincareConvolution_test_bounds n f
  have hdf : Continuous (fderiv ℝ f) := f.contDiff.continuous_fderiv (by simp)
  have hid : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 γ :=
    IsGaussian.memLp_two_id
  have hi1 : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖p.1‖) μ :=
    ((hid.comp_fst γ).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm
  have hi2 : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖p.2‖) μ :=
    ((hid.comp_snd γ).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (α : ℝ) (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
      f p.1 * f (Real.cos α • p.1 + Real.sin α • p.2))
    (F' := fun (α : ℝ) (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
      f p.1 * fderiv ℝ f (Real.cos α • p.1 + Real.sin α • p.2)
        ((-Real.sin α) • p.1 + Real.cos α • p.2))
    (s := Set.univ) (bound := fun p => (C * D) * (‖p.1‖ + ‖p.2‖)) Filter.univ_mem
  · exact Eventually.of_forall fun α =>
      (show Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        f p.1 * f (Real.cos α • p.1 + Real.sin α • p.2)) from by fun_prop).aestronglyMeasurable
  · apply (integrable_const (C ^ 2)).mono'
      (show Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        f p.1 * f (Real.cos θ • p.1 + Real.sin θ • p.2)) from by fun_prop).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      rw [norm_mul, pow_two]
      exact mul_le_mul (hC _) (hC _) (norm_nonneg _) hC0
  · exact (show Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      f p.1 * fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2)
        ((-Real.sin θ) • p.1 + Real.cos θ • p.2)) from by fun_prop).aestronglyMeasurable
  · exact Eventually.of_forall fun p α _ =>
      gaussianVarianceCorrelation_derivative_bound n f C D hC0 hD0 hC hD α p
  · exact (hi1.add hi2).const_mul (C * D)
  · exact Eventually.of_forall fun p α _ => by
      have hrot := ((Real.hasDerivAt_cos α).smul_const p.1).add
        ((Real.hasDerivAt_sin α).smul_const p.2)
      exact (((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt α hrot).const_mul (f p.1))

theorem gaussianVarianceCorrelation_zero (n : ℕ)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    gaussianVarianceCorrelation n f 0 = ∫ x, (f x) ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  simp only [gaussianVarianceCorrelation, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero, ← pow_two]
  simpa only [probReal_univ, one_smul] using
    (integral_fun_fst (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))
      (ν := stdGaussian (EuclideanSpace ℝ (Fin n))) (fun x => (f x) ^ 2))

theorem gaussianVarianceCorrelation_pi_div_two (n : ℕ)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    gaussianVarianceCorrelation n f (Real.pi / 2) =
      (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ^ 2 := by
  simp only [gaussianVarianceCorrelation, Real.cos_pi_div_two, Real.sin_pi_div_two,
    zero_smul, one_smul, zero_add, integral_prod_mul, pow_two]

end AffineFKProof
