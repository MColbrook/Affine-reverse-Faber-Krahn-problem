module

public import AffineFK.LogConcaveDensityFinite
public import AffineFK.NormalizedConvolutionDensity

/-!
# The genuine real density of normalized independent copies

Prékopa's marginal theorem first gives log-concavity of the extended
convolution. Its mass is one, so pointwise finiteness follows from
LogConcaveDensityFinite. The real convolution representative and its
invertible-linear Jacobian transform therefore retain pointwise
log-concavity, with the actual product pushforward as their law.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem ordinaryFisherConvolutionDensity_logConcave (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x))) :
    LogConcaveDensity (fun x => ENNReal.ofReal
      (ordinaryFisherConvolutionDensity n (densityMeasure n f) f x)) := by
  let F := ordinaryFisherConvolutionDensityENNReal n (densityMeasure n f) f
  have hF : Measurable F := ordinaryFisherConvolutionDensityENNReal_measurable n _ f hf
  have hFlc : LogConcaveDensity F := by
    have h := logConcaveDensity_convolution_euclidean n
      (fun x => ENNReal.ofReal (f x)) (fun x => ENNReal.ofReal (f x))
      hf.ennreal_ofReal hf.ennreal_ofReal hlc hlc
    have heq (z : EuclideanSpace ℝ (Fin n)) :
        F z = ∫⁻ y, ENNReal.ofReal (f (z - y)) * ENNReal.ofReal (f y) := by
      change (∫⁻ y, ENNReal.ofReal (f (z - y)) ∂volume.withDensity
        (fun y => ENNReal.ofReal (f y))) = _
      rw [lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal
        (g := fun y => ENNReal.ofReal (f (z - y)))
        (hf.comp (measurable_const.sub measurable_id)).ennreal_ofReal]
      apply lintegral_congr
      intro y
      change ENNReal.ofReal (f y) * ENNReal.ofReal (f (z - y)) = _
      exact mul_comm _ _
    simpa only [← heq] using h
  have hm : (∫⁻ z, F z) = 1 :=
    (ordinaryFisherConvolutionDensity_mass_finite n (densityMeasure n f) f hf).1
  have hne (z) : F z ≠ ∞ := logConcaveDensity_ne_top_of_finite_mass n F hF hFlc
    (by rw [hm]; exact one_ne_zero) (by rw [hm]; exact ENNReal.one_ne_top) z
  have heq : (fun x => ENNReal.ofReal
      (ordinaryFisherConvolutionDensity n (densityMeasure n f) f x)) = F := by
    funext x
    exact ENNReal.ofReal_toReal (hne x)
  rw [heq]
  exact hFlc

theorem ordinaryFisherLinearDensity_logConcave (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x))) :
    LogConcaveDensity (fun x => ENNReal.ofReal (ordinaryFisherLinearDensity n A f x)) := by
  have hcomp : LogConcaveDensity (fun x => ENNReal.ofReal (f (A.symm x))) :=
    logConcaveDensity_comp_linearMap _ hlc A.symm.toLinearEquiv.toLinearMap
  have h := logConcaveDensity_mul
    (fun _ : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (ordinaryFisherLinearJacobian n A))
    (fun x => ENNReal.ofReal (f (A.symm x))) (logConcaveDensity_const _)
    hcomp
  simpa only [ordinaryFisherLinearDensity,
    ENNReal.ofReal_mul (ordinaryFisherLinearJacobian_pos n A).le] using h

theorem normalized_copies_logConcave_density (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (a : ℝ) (ha : a ≠ 0) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      LogConcaveDensity (fun x => ENNReal.ofReal (g x)) ∧
      ((densityMeasure n f).prod (densityMeasure n f)).map
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          a • p.1 + a • p.2) = densityMeasure n g := by
  let κ := ordinaryFisherConvolutionDensity n (densityMeasure n f) f
  have hκ : Measurable κ :=
    (ordinaryFisherConvolutionDensityENNReal_measurable n _ f hf).ennreal_toReal
  let A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.smulOfNeZero ℝ _ a ha).toContinuousLinearEquiv
  refine ⟨ordinaryFisherLinearDensity n A κ,
    measurable_const.mul (hκ.comp A.symm.continuous.measurable), ?_, ?_, ?_⟩
  · intro x
    exact mul_nonneg (ordinaryFisherLinearJacobian_pos n A).le ENNReal.toReal_nonneg
  · exact ordinaryFisherLinearDensity_logConcave n A κ
      (ordinaryFisherConvolutionDensity_logConcave n f hf hlc)
  · calc
      _ = (((densityMeasure n f).prod (densityMeasure n f)).map
          (fun p => p.1 + p.2)).map A := by
        rw [Measure.map_map A.continuous.measurable (by fun_prop)]
        congr 1
        funext p
        exact (smul_add a p.1 p.2).symm
      _ = _ := by
        rw [ordinaryFisherConvolutionDensity_law n (densityMeasure n f) f hf,
          ordinaryFisherLinearDensity_law n A κ hκ]

end AffineFKProof
