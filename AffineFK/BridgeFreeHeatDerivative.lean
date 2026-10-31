module

public import AffineFK.BridgeFreeHeatKernel
public import AffineFK.BridgeGaussianBessel
public import AffineFK.AffineGaussianIntegrationByParts
public import AffineFK.GaussianSmoothingRegularity

/-!
# Actual free heat averages of compact smooth functions

Dominated differentiation and genuine Gaussian integration by parts
identify the spatial derivatives. Bessel's inequality gives a pointwise
dimension-free bound with the exact time normalization for generator Δ/2.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal Distributions ContDiff RealInnerProductSpace BigOperators

def bridgeFreeHeatAverage (n : ℕ) (t : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ u, f (x + Real.sqrt t • u) ∂stdGaussian (EuclideanSpace ℝ (Fin n))

theorem bridgeFreeHeatAverage_eq_killed (n : ℕ) (t : ℝ) (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : AEStronglyMeasurable f volume) :
    bridgeFreeHeatAverage n t f = bridgeKilledIntegral n t ht univ isOpen_univ f := by
  funext x
  exact (bridgeKilledIntegral_univ n t ht f hf x).symm

theorem bridgeFreeHeatAverage_test_smooth (n : ℕ) (t : ℝ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ContDiff ℝ ∞ (bridgeFreeHeatAverage n t φ) := by
  unfold bridgeFreeHeatAverage
  have hb (r : ℕ) : ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ r φ y‖ ≤ C := by
    obtain ⟨C, _, hC⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff r
    exact ⟨C, hC r le_rfl⟩
  simpa only [neg_smul, sub_neg_eq_add] using
    gaussianSmoothingRegularity_contDiff_translation_integral n
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (-Real.sqrt t) φ φ.contDiff hb

theorem bridgeFreeHeatAverage_test_hasFDerivAt (n : ℕ) (t : ℝ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (bridgeFreeHeatAverage n t φ)
      (∫ u, fderiv ℝ φ (x + Real.sqrt t • u)
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) x := by
  unfold bridgeFreeHeatAverage
  obtain ⟨C, _, hC⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff 1
  have hv (y) : ‖φ y‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using hC 0 (by omega) y
  have hd (y) : ‖fderiv ℝ φ y‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_one] using hC 1 le_rfl y
  simpa only [neg_smul, sub_neg_eq_add] using
    gaussianSmoothingRegularity_hasFDerivAt_translation_integral n
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (-Real.sqrt t) φ φ.contDiff C C hv hd x

theorem bridgeFreeHeatAverage_test_gradient_coordinate (n : ℕ) (t : ℝ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    gradient (bridgeFreeHeatAverage n t φ) x i =
      bridgeFreeHeatAverage n t (partialTest n i φ) x := by
  have hc := (φ.contDiff.continuous_fderiv (by simp)).comp
    (show Continuous (fun u : EuclideanSpace ℝ (Fin n) => x + Real.sqrt t • u) by fun_prop)
  obtain ⟨C, _, hC⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff 1
  have hb (u : EuclideanSpace ℝ (Fin n)) :
      ‖fderiv ℝ φ (x + Real.sqrt t • u)‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_one] using hC 1 le_rfl (x + Real.sqrt t • u)
  have hi : Integrable (fun u : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ (x + Real.sqrt t • u))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    (integrable_const C).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have he : gradient (bridgeFreeHeatAverage n t φ) x i =
      fderiv ℝ (bridgeFreeHeatAverage n t φ) x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    rw [← inner_gradient_left, real_inner_comm]
    exact (EuclideanSpace.basisFun_inner (Fin n) ℝ _ i).symm
  rw [he, (bridgeFreeHeatAverage_test_hasFDerivAt n t φ x).fderiv,
    ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => (partialTest_fderiv n i φ _).symm

theorem bridgeFreeHeatAverage_test_gaussian_correlation (n : ℕ) (t : ℝ) (ht : 0 < t)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (∫ u, u i * φ (x + Real.sqrt t • u) ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      Real.sqrt t * gradient (bridgeFreeHeatAverage n t φ) x i := by
  rw [bridgeFreeHeatAverage_test_gradient_coordinate]
  simpa only [bridgeFreeHeatAverage, add_comm] using
    (stdGaussian_affine_integration_by_parts n i (Real.sqrt t)
      (Real.sqrt_pos.mpr ht).ne' x φ).2.2

theorem bridgeFreeHeatAverage_test_pointwise_energy (n : ℕ) (t : ℝ) (ht : 0 < t)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    t * ‖gradient (bridgeFreeHeatAverage n t φ) x‖^2 ≤
      bridgeFreeHeatAverage n t (fun y => (φ y)^2) x -
        (bridgeFreeHeatAverage n t φ x)^2 := by
  have hf : MemLp (fun u => φ (x + Real.sqrt t • u)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    bridgeFreeHeat_integrable_translate n t ht φ
      (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport) x
  have hb := bridgeGaussian_coordinate_bessel_variance n _ hf
  simp_rw [bridgeFreeHeatAverage_test_gaussian_correlation n t ht φ x,
    mul_pow, Real.sq_sqrt ht.le] at hb
  rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq] at hb
  exact hb

end AffineFKProof
