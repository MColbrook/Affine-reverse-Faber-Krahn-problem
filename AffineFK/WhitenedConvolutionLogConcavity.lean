module

public import AffineFK.WhitenedConvolutionIsotropy
public import AffineFK.NormalizedConvolutionLogConcavity

/-!
# Log-concavity of the actual whitened convolution density

Prékopa's theorem applies to the two actual input densities. The extended
convolution has mass one, which gives pointwise finiteness; hence its real
representative retains log-concavity everywhere. The actual invertible
whitening map then transports both the law and its density.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem ordinaryFisherConvolutionDensity_logConcave_two (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f) (hg : Measurable g)
    [IsProbabilityMeasure (densityMeasure n f)] [IsProbabilityMeasure (densityMeasure n g)]
    (hlf : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hlg : LogConcaveDensity (fun x => ENNReal.ofReal (g x))) :
    LogConcaveDensity (fun x => ENNReal.ofReal
      (ordinaryFisherConvolutionDensity n (densityMeasure n f) g x)) := by
  let F := ordinaryFisherConvolutionDensityENNReal n (densityMeasure n f) g
  have hF : Measurable F := ordinaryFisherConvolutionDensityENNReal_measurable n _ g hg
  have hFlc : LogConcaveDensity F := by
    have h := logConcaveDensity_convolution_euclidean n
      (fun x => ENNReal.ofReal (g x)) (fun x => ENNReal.ofReal (f x))
      hg.ennreal_ofReal hf.ennreal_ofReal hlg hlf
    have heq (z : EuclideanSpace ℝ (Fin n)) :
        F z = ∫⁻ y, ENNReal.ofReal (g (z - y)) * ENNReal.ofReal (f y) := by
      change (∫⁻ y, ENNReal.ofReal (g (z - y)) ∂volume.withDensity
        (fun y => ENNReal.ofReal (f y))) = _
      rw [lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal
        (g := fun y => ENNReal.ofReal (g (z - y)))
        (hg.comp (measurable_const.sub measurable_id)).ennreal_ofReal]
      apply lintegral_congr
      intro y
      change ENNReal.ofReal (f y) * ENNReal.ofReal (g (z - y)) = _
      exact mul_comm _ _
    simpa only [← heq] using h
  have hm : (∫⁻ z, F z) = 1 :=
    (ordinaryFisherConvolutionDensity_mass_finite n (densityMeasure n f) g hg).1
  have hne (z) : F z ≠ ∞ := logConcaveDensity_ne_top_of_finite_mass n F hF hFlc
    (by rw [hm]; exact one_ne_zero) (by rw [hm]; exact ENNReal.one_ne_top) z
  have heq : (fun x => ENNReal.ofReal
      (ordinaryFisherConvolutionDensity n (densityMeasure n f) g x)) = F := by
    funext x
    exact ENNReal.ofReal_toReal (hne x)
  rw [heq]
  exact hFlc

theorem whitenedSumLaw_logConcave_density (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f) (hg : Measurable g)
    [IsProbabilityMeasure (densityMeasure n f)] [IsProbabilityMeasure (densityMeasure n g)]
    (hlf : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hlg : LogConcaveDensity (fun x => ENNReal.ofReal (g x)))
    (hY : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 (densityMeasure n g))
    (hmeanY : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂densityMeasure n g) = 0)
    (hPη : poincareConstant n (densityMeasure n g) ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1) :
    ∃ h : EuclideanSpace ℝ (Fin n) → ℝ,
      Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      LogConcaveDensity (fun x => ENNReal.ofReal (h x)) ∧
      whitenedSumLaw n (densityMeasure n f) (densityMeasure n g) α = densityMeasure n h := by
  let η := densityMeasure n g
  let κ := ordinaryFisherConvolutionDensity n (densityMeasure n f) g
  have hκ : Measurable κ :=
    (ordinaryFisherConvolutionDensityENNReal_measurable n _ g hg).ennreal_toReal
  have hM := (convolutionCovarianceMatrix_bounds n η hY hmeanY hPη α hα hαone).2.2
  let A := covarianceWhiteningLinear n (convolutionCovarianceMatrix n α η) hM
  refine ⟨ordinaryFisherLinearDensity n A κ,
    measurable_const.mul (hκ.comp A.symm.continuous.measurable), ?_, ?_, ?_⟩
  · intro x
    exact mul_nonneg (ordinaryFisherLinearJacobian_pos n A).le ENNReal.toReal_nonneg
  · exact ordinaryFisherLinearDensity_logConcave n A κ
      (ordinaryFisherConvolutionDensity_logConcave_two n f g hf hg hlf hlg)
  · rw [whitenedSumLaw_eq_linear_image,
      ordinaryFisherConvolutionDensity_law n (densityMeasure n f) g hg]
    exact ordinaryFisherLinearDensity_law n A κ hκ

end AffineFKProof
