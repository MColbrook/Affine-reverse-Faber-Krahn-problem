module

public import AffineFK.BridgeFreeHeatConservation

/-!
# The genuine free-heat energy estimate on compact smooth inputs

The pointwise Gaussian Bessel bound is integrated only after proving
the full Haar/Fubini conservation and both terms' integrability.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set TopologicalSpace InnerProductSpace
open scoped ENNReal Distributions RealInnerProductSpace

theorem bridgeFreeHeatAverage_test_memLp (n : ℕ) (t : ℝ) (ht : 0 < t)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    MemLp (bridgeFreeHeatAverage n t φ) 2 volume := by
  rw [bridgeFreeHeatAverage_eq_killed n t ht φ φ.continuous.aestronglyMeasurable]
  exact (bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht univ isOpen_univ φ
    (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)).1

theorem bridgeFreeHeatAverage_test_gradient_continuous (n : ℕ) (t : ℝ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Continuous (gradient (bridgeFreeHeatAverage n t φ)) :=
  (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
    ((bridgeFreeHeatAverage_test_smooth n t φ).continuous_fderiv (by simp))

theorem bridgeFreeHeatAverage_test_energy (n : ℕ) (t : ℝ) (ht : 0 < t)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    MemLp (gradient (bridgeFreeHeatAverage n t φ)) 2 volume ∧
      t * (∫ x, ‖gradient (bridgeFreeHeatAverage n t φ) x‖^2 ∂volume) ≤
        (∫ x, (φ x)^2 ∂volume) -
          (∫ x, (bridgeFreeHeatAverage n t φ x)^2 ∂volume) := by
  have hφ : MemLp (φ : EuclideanSpace ℝ (Fin n) → ℝ) 2 volume :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hφsq : Integrable (fun x => (φ x)^2) volume :=
    (memLp_two_iff_integrable_sq φ.continuous.aestronglyMeasurable).mp hφ
  have hQsq := bridgeFreeHeatAverage_integrable_and_integral n t (fun x => (φ x)^2)
    (φ.continuous.pow 2) hφsq
  have hQφ := bridgeFreeHeatAverage_test_memLp n t ht φ
  have hiQφ : Integrable (fun x => (bridgeFreeHeatAverage n t φ x)^2) volume :=
    (memLp_two_iff_integrable_sq hQφ.aestronglyMeasurable).mp hQφ
  have hR : Integrable (fun x => bridgeFreeHeatAverage n t (fun y => (φ y)^2) x -
      (bridgeFreeHeatAverage n t φ x)^2) volume := hQsq.1.sub hiQφ
  have hgrad := bridgeFreeHeatAverage_test_gradient_continuous n t φ
  have hi : Integrable (fun x => t * ‖gradient (bridgeFreeHeatAverage n t φ) x‖^2) volume := by
    apply hR.mono' ((continuous_const.mul (hgrad.norm.pow 2)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      change ‖t * ‖gradient (bridgeFreeHeatAverage n t φ) x‖^2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.le (sq_nonneg _))]
      exact bridgeFreeHeatAverage_test_pointwise_energy n t ht φ x
  have hiG : Integrable (fun x => ‖gradient (bridgeFreeHeatAverage n t φ) x‖^2) volume := by
    convert hi.const_mul t⁻¹ using 1
    funext x
    rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  refine ⟨(memLp_two_iff_integrable_sq_norm hgrad.aestronglyMeasurable).mpr hiG, ?_⟩
  have hb := integral_mono hi hR (bridgeFreeHeatAverage_test_pointwise_energy n t ht φ)
  rw [integral_const_mul, integral_sub hQsq.1 hiQφ, hQsq.2] at hb
  exact hb

end AffineFKProof
