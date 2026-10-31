module

public import AffineFK.StrongLogConcavePoincare
public import AffineFK.StrongLogConcavePoincareSmoothing
public import AffineFK.PoincareConstantAttainment
public import AffineFK.OUInitialLimit
public import AffineFK.SteinTestIdentities

/-!
# Unit Poincare inequality for supported strongly log-concave densities

Actual OU laws converge on bounded continuous tests. Compact smooth
values, their squares and the genuine gradient square are such tests,
so the Poincare bound passes to the original law. The strong
log-concavity of every positive-time density is proved by Gaussian
square completion and Prékopa, not assumed as a limiting certificate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped Distributions ENNReal NNReal Topology BoundedContinuousFunction RealInnerProductSpace

theorem strongLogConcave_poincareConstant_le_of_ou (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hP : ∀ t : ℝ, 0 < t → poincareConstant n (ouInitialLaw n ν t) ≤ 1) :
    poincareConstant n ν ≤ 1 := by
  apply poincareConstant_le_of_admissible n ν 1
  intro f
  let fB : EuclideanSpace ℝ (Fin n) →ᵇ ℝ := f
  let gB : EuclideanSpace ℝ (Fin n) →ᵇ ℝ :=
    ∑ i : Fin n, (partialTest n i f : EuclideanSpace ℝ (Fin n) →ᵇ ℝ) ^ 2
  have hg (x : EuclideanSpace ℝ (Fin n)) : gB x = ‖gradient f x‖ ^ 2 := by
    simpa only [gB, BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.pow_apply,
      TestFunction.coe_toBoundedContinuousFunction, partialTest_apply] using
      (EuclideanSpace.real_norm_sq_eq (gradient f x)).symm
  have hmean := ouInitial_integral_boundedContinuous_tendsto n ν fB
  have hsecond := ouInitial_integral_boundedContinuous_tendsto n ν (fB ^ 2)
  have hgradient := ouInitial_integral_boundedContinuous_tendsto n ν gB
  change Tendsto (fun t => ∫ x, f x ∂ouInitialLaw n ν t) (𝓝 0) (𝓝 (∫ x, f x ∂ν)) at hmean
  change Tendsto (fun t => ∫ x, (f x) ^ 2 ∂ouInitialLaw n ν t) (𝓝 0)
    (𝓝 (∫ x, (f x) ^ 2 ∂ν)) at hsecond
  simp_rw [hg] at hgradient
  have hvar (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ] :
      (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) =
        (∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
    have hf : MemLp f 2 μ := f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
    exact (variance_eq_integral hf.aemeasurable).symm.trans (variance_eq_sub hf)
  have hbound (k : ℕ) :
      (∫ x, (f x) ^ 2 ∂ouInitialLaw n ν ((k : ℝ) + 1)⁻¹) -
        (∫ x, f x ∂ouInitialLaw n ν ((k : ℝ) + 1)⁻¹) ^ 2 ≤
      ∫ x, ‖gradient f x‖ ^ 2 ∂ouInitialLaw n ν ((k : ℝ) + 1)⁻¹ := by
    have h := admissiblePoincareConstant_of_poincareConstant_le n
      (ouInitialLaw n ν ((k : ℝ) + 1)⁻¹) 1 (hP _ (by positivity)) f
    rwa [hvar, NNReal.coe_one, one_mul] at h
  have hlimit := le_of_tendsto_of_tendsto'
    ((hsecond.sub (hmean.pow 2)).comp tendsto_inverse_succ)
    (hgradient.comp tendsto_inverse_succ) hbound
  simpa only [hvar, NNReal.coe_one, one_mul] using hlimit

theorem strongLogConcave_density_poincareConstant_le_one (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal
      (ρ x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)))) :
    poincareConstant n (densityMeasure n ρ) ≤ 1 := by
  apply strongLogConcave_poincareConstant_le_of_ou n (densityMeasure n ρ)
  intro t ht
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-2 * t))
  have hb : 0 < b := by
    apply Real.sqrt_pos.mpr
    have h := Real.exp_lt_one_iff.mpr (show -2 * t < 0 by linarith)
    exact sub_pos.mpr h
  have hab : a ^ 2 + b ^ 2 = 1 := by
    dsimp [a, b]
    have he : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [ou_exponential_power, Real.sq_sqrt (sub_nonneg.mpr he)]
    ring
  let σ := gaussianSmoothingDensity n (densityMeasure n ρ) a b
  have hlaw : ouInitialLaw n (densityMeasure n ρ) t = densityMeasure n σ :=
    gaussianSmoothingDensity_law n (densityMeasure n ρ) a b hb
  let : IsProbabilityMeasure (densityMeasure n σ) := by rw [← hlaw]; infer_instance
  have h := strongLogConcave_smooth_probability_poincareConstant_le_one n σ
    (gaussianSmoothingDensity_smooth n (densityMeasure n ρ) a b)
    (gaussianSmoothingDensity_pos n (densityMeasure n ρ) a b hb)
    (strongLogConcave_gaussianSmoothingDensity n ρ hρ hρ0 hlc a b hb hab)
  rwa [← hlaw] at h

end AffineFKProof
