module

public import AffineFK.GroundstateGaussianMultiplier

/-!
# Algebra and genuine moment integrability for the Gaussian ground-state factor

The pointwise identity pairs the original gradient with the gradient of
the squared-weight test. Thus its integration needs only genuine L2
gradient pairings and an explicitly dominated moment term. It does not
assume an eigenfunction or the computed integrated energy identity.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped RealInnerProductSpace

theorem groundstate_gaussian_energy_pointwise (n : ℕ) (p : ℝ)
    (g x : EuclideanSpace ℝ (Fin n)) :
    ‖groundstateGaussianFactor n x • g + p • gradient (groundstateGaussianFactor n) x‖ ^ 2 =
      ⟪g, groundstateGaussianWeight n x • g + p • gradient (groundstateGaussianWeight n) x⟫ +
        (1 / 4 : ℝ) * ‖x‖ ^ 2 * (groundstateGaussianFactor n x * p) ^ 2 := by
  rw [groundstateGaussianFactor_gradient, groundstateGaussianWeight_gradient,
    ← groundstateGaussianFactor_sq]
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_add_right, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
    starRingEnd_apply, star_trivial]
  ring

theorem groundstate_gaussian_moment_domination (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (p : ℝ) :
    ‖x‖ ^ 2 * (groundstateGaussianFactor n x * p) ^ 2 ≤ 25 * p ^ 2 := by
  have h0 : 0 ≤ ‖x‖ * groundstateGaussianFactor n x :=
    mul_nonneg (norm_nonneg _) (groundstateGaussianFactor_pos n x).le
  have hs : (‖x‖ * groundstateGaussianFactor n x) ^ 2 ≤ (5 : ℝ) ^ 2 :=
    (sq_le_sq₀ h0 (by norm_num)).mpr (groundstateGaussianFactor_norm_mul_le n x)
  calc
    _ = (‖x‖ * groundstateGaussianFactor n x) ^ 2 * p ^ 2 := by ring
    _ ≤ (5 : ℝ) ^ 2 * p ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg p)
    _ = _ := by ring

theorem groundstate_gaussian_moment_integrable (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemLp f 2 μ) :
    Integrable (fun x => ‖x‖ ^ 2 * (groundstateGaussianFactor n x * f x) ^ 2) μ := by
  have hf2 : Integrable (fun x => f x ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hm : AEStronglyMeasurable (fun x => ‖x‖ ^ 2 * (groundstateGaussianFactor n x * f x) ^ 2) μ :=
    continuous_norm.aestronglyMeasurable.pow 2 |>.mul
      (((groundstateGaussianFactor_smooth n).continuous.aestronglyMeasurable.mul
        hf.aestronglyMeasurable).pow 2)
  apply (hf2.const_mul 25).mono' hm
  exact ae_of_all μ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact groundstate_gaussian_moment_domination n x (f x)

end AffineFKProof
