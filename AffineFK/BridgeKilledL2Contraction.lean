module

public import AffineFK.BridgeKilledSubinvariance
public import AffineFK.BridgeSubprobabilityJensen
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Actual quadratic contraction of the killed Brownian integral

The Gaussian bound controls every row by a finite multiple of Lebesgue
measure. Thus every Lebesgue L2 input is genuinely integrable in every
row; no default Bochner integral supports the conclusion. Quadratic
Jensen and the proved Lebesgue subinvariance give the L2 estimate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem bridge_standardGaussianDensity_le_zero (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    standardGaussianDensity n z ≤ standardGaussianDensity n 0 := by
  apply (Real.log_le_log_iff (standardGaussianDensity_pos n z)
    (standardGaussianDensity_pos n 0)).mp
  rw [log_standardGaussianDensity, log_standardGaussianDensity, norm_zero]
  nlinarith [sq_nonneg ‖z‖]

theorem bridgeKilledKernel_uniform_bound (n : ℕ) (T : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    bridgeKilledKernel n T x Ω y ≤
      ENNReal.ofReal ((Real.sqrt T ^ n)⁻¹ * standardGaussianDensity n 0) := by
  apply (bridgeKilledKernel_le_free n T x y Ω).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (bridge_standardGaussianDensity_le_zero n _)
    (by positivity)

theorem bridgeKilledTransitionKernel_le_smul_volume (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) (x : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledTransitionKernel n T hT Ω hΩ x ≤
      ENNReal.ofReal ((Real.sqrt T ^ n)⁻¹ * standardGaussianDensity n 0) • volume := by
  rw [bridgeKilledTransitionKernel_eq_withDensity n T hT Ω hΩ x,
    ← withDensity_const (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))]
  exact withDensity_mono (Filter.Eventually.of_forall
    (fun y => bridgeKilledKernel_uniform_bound n T x y Ω))

theorem bridge_memLp_killed_row (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemLp f 2 volume)
    (x : EuclideanSpace ℝ (Fin n)) : MemLp f 2 (bridgeKilledTransitionKernel n T hT Ω hΩ x) :=
  hf.of_measure_le_smul ENNReal.ofReal_ne_top
    (bridgeKilledTransitionKernel_le_smul_volume n T hT Ω hΩ x)

/-- The actual Bochner integral of a real function against the genuine
killed Brownian transition measure. Subsequent L2 statements prove the
integrability of every row before using this integral. -/
def bridgeKilledIntegral (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y, f y ∂bridgeKilledTransitionKernel n T hT Ω hΩ x

theorem bridgeKilledIntegral_lintegral_sq_le (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable f) (hf : MemLp f 2 volume) :
    (∫⁻ x, ENNReal.ofReal ((bridgeKilledIntegral n T hT Ω hΩ f x)^2) ∂volume) ≤
      ∫⁻ y, ENNReal.ofReal ((f y)^2) ∂volume := by
  apply le_trans (lintegral_mono (fun x => ?_))
    (bridgeKilledTransitionKernel_integral_subinvariant n T hT Ω hΩ _
      (hm.pow_const 2).ennreal_ofReal)
  have hx := bridge_memLp_killed_row n T hT Ω hΩ f hf x
  have hs := bridge_subprobability_integral_sq_le
    (bridgeKilledTransitionKernel n T hT Ω hΩ x)
    (bridgeKilledTransitionKernel_mass_le_one n T hT Ω hΩ x) f hx
  change ENNReal.ofReal ((∫ y, f y ∂bridgeKilledTransitionKernel n T hT Ω hΩ x)^2) ≤ _
  calc
    _ ≤ ENNReal.ofReal (∫ y, (f y)^2 ∂bridgeKilledTransitionKernel n T hT Ω hΩ x) :=
      ENNReal.ofReal_le_ofReal hs
    _ = _ := ofReal_integral_eq_lintegral_ofReal hx.integrable_sq
      (Filter.Eventually.of_forall (fun y => sq_nonneg (f y)))

theorem bridgeKilledIntegral_memLp_and_sq_bound (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable f) (hf : MemLp f 2 volume) :
    MemLp (bridgeKilledIntegral n T hT Ω hΩ f) 2 volume ∧
      (∫ x, (bridgeKilledIntegral n T hT Ω hΩ f x)^2 ∂volume) ≤ ∫ y, (f y)^2 ∂volume := by
  have hL := bridgeKilledIntegral_lintegral_sq_le n T hT Ω hΩ f hm hf
  have hPs : StronglyMeasurable (bridgeKilledIntegral n T hT Ω hΩ f) :=
    hm.stronglyMeasurable.integral_kernel
  have hR : (∫⁻ y, ENNReal.ofReal ((f y)^2) ∂volume) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.integrable_sq.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => sq_nonneg (f y)))).mpr hf.integrable_sq
  have hPf : (∫⁻ x, ENNReal.ofReal ((bridgeKilledIntegral n T hT Ω hΩ f x)^2) ∂volume) ≠ ∞ := by
    intro htop
    rw [htop] at hL
    exact hR (top_le_iff.mp hL)
  have hPi : Integrable (fun x => (bridgeKilledIntegral n T hT Ω hΩ f x)^2) volume :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hPs.measurable.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))).mp hPf
  refine ⟨(memLp_two_iff_integrable_sq hPs.aestronglyMeasurable).mpr hPi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hPi
    (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
      (Filter.Eventually.of_forall (fun y => sq_nonneg (f y)))] at hL
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun y => sq_nonneg (f y)))).mp hL

end AffineFKProof
