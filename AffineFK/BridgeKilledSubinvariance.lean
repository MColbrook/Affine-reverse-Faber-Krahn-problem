module

public import AffineFK.BridgeKilledKernelSymmetry

/-!
# Lebesgue subinvariance for the genuine killed Brownian semigroup

The actual finite row masses and the everywhere symmetry of the fixed
jointly measurable bridge density give the nonnegative-integral contraction
by Tonelli. No invariant measure or symmetric-semigroup property is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem bridgeKilledKernel_row_integral_le_one (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) (x : EuclideanSpace ℝ (Fin n)) :
    (∫⁻ y, bridgeKilledKernel n T x Ω y ∂volume) ≤ 1 := by
  have h := bridgeKilledTransitionKernel_mass_le_one n T hT Ω hΩ x
  rw [bridgeKilledTransitionKernel_eq_withDensity n T hT Ω hΩ x,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  exact h

theorem bridgeKilledKernel_integral_subinvariant (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, bridgeKilledKernel n T x Ω y * f y ∂volume ∂volume) ≤
      ∫⁻ y, f y ∂volume := by
  have hj := (bridgeKilledKernel_joint_measurable n T hT Ω hΩ).mul (hf.comp measurable_snd)
  rw [lintegral_lintegral_swap hj.aemeasurable]
  calc
    _ = ∫⁻ y, (∫⁻ x, bridgeKilledKernel n T y Ω x ∂volume) * f y ∂volume := by
      apply lintegral_congr
      intro y
      simp_rw [bridgeKilledKernel_symmetric n T hT _ y Ω hΩ]
      exact lintegral_mul_const (f y) (bridgeKilledKernel_measurable n T y Ω hΩ)
    _ ≤ ∫⁻ y, 1 * f y ∂volume := lintegral_mono (fun y => by
      simpa only [mul_comm] using
        mul_le_mul_right (bridgeKilledKernel_row_integral_le_one n T hT Ω hΩ y) (f y))
    _ = _ := by simp only [one_mul]

theorem bridgeKilledTransitionKernel_integral_subinvariant (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, f y ∂bridgeKilledTransitionKernel n T hT Ω hΩ x ∂volume) ≤
      ∫⁻ y, f y ∂volume := by
  have he (x : EuclideanSpace ℝ (Fin n)) :
      (∫⁻ y, f y ∂bridgeKilledTransitionKernel n T hT Ω hΩ x) =
        ∫⁻ y, bridgeKilledKernel n T x Ω y * f y ∂volume := by
    rw [bridgeKilledTransitionKernel_eq_withDensity n T hT Ω hΩ x]
    exact lintegral_withDensity_eq_lintegral_mul volume (bridgeKilledKernel_measurable n T x Ω hΩ) hf
  simp_rw [he]
  exact bridgeKilledKernel_integral_subinvariant n T hT Ω hΩ f hf

end AffineFKProof
