module

public import AffineFK.OUDensityTimeScoreEquation

/-!
# The compact spatial nonlinear OU dissipation identity

The time-dependent test is formed from a compact spatial test and a smooth
scalar function of the actual positive relative density. Its genuine
gradient chain rule identifies the score-square term. The identity is
proved before any spatial or scalar cutoff limit is taken.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ContDiff

/-- A genuine compact smooth test obtained by multiplying a test by a
smooth scalar function of a positive smooth function. -/
def entropyDerivativeTest (n : ℕ) (q : EuclideanSpace ℝ (Fin n) → ℝ)
    (hq : ContDiff ℝ ∞ q) (hqpos : ∀ x, 0 < q x)
    (g : ℝ → ℝ) (hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ g r)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  ⟨fun x => φ x * g (q x), by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact φ.contDiff.contDiffAt.mul ((hg (q x) (hqpos x)).comp x hq.contDiffAt),
    φ.hasCompactSupport.mul_right, Set.subset_univ _⟩

theorem positive_function_log_gradient_direction (n : ℕ)
    (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ ∞ q)
    (hqpos : ∀ x, 0 < q x) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ q x (gradient (fun y => Real.log (q y)) x) =
      q x * ‖gradient (fun y => Real.log (q y)) x‖ ^ 2 := by
  let v := gradient (fun y => Real.log (q y)) x
  have heq : fderiv ℝ (fun y => Real.log (q y)) x v = ‖v‖ ^ 2 := by
    rw [← inner_gradient_left]
    exact real_inner_self_eq_norm_sq v
  rw [fderiv.log ((hq.differentiable (by simp)).differentiableAt) (hqpos x).ne',
    ContinuousLinearMap.smul_apply, smul_eq_mul] at heq
  have h := congrArg (fun z : ℝ => q x * z) heq
  simpa only [← mul_assoc, mul_inv_cancel₀ (hqpos x).ne', one_mul] using h

theorem entropyDerivativeTest_score_flux (n : ℕ)
    (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ ∞ q) (hqpos : ∀ x, 0 < q x)
    (g g' : ℝ → ℝ) (hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ g r)
    (hg' : ∀ r : ℝ, 0 < r → HasDerivAt g (g' r) r)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪gradient (fun y => Real.log (q y)) x,
      gradient (entropyDerivativeTest n q hq hqpos g hg φ) x⟫ =
      g (q x) * ⟪gradient (fun y => Real.log (q y)) x, gradient φ x⟫ +
        φ x * g' (q x) * q x * ‖gradient (fun y => Real.log (q y)) x‖ ^ 2 := by
  let v := gradient (fun y => Real.log (q y)) x
  have hqD : HasFDerivAt q (fderiv ℝ q x) x :=
    (hq.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := (hg' (q x) (hqpos x)).comp_hasFDerivAt x hqD
  have hφD : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hprod := hφD.mul hcomp
  rw [real_inner_comm, inner_gradient_left]
  change fderiv ℝ ((φ : EuclideanSpace ℝ (Fin n) → ℝ) * g ∘ q) x v = _
  rw [hprod.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Function.comp_apply]
  rw [positive_function_log_gradient_direction n q hq hqpos x]
  rw [← inner_gradient_left, real_inner_comm]
  ring

theorem ou_compact_nonlinear_dissipation (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (ψ g g' : ℝ → ℝ)
    (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (g r) r)
    (hg : ∀ r : ℝ, 0 < r → ContDiffAt ℝ ∞ g r)
    (hg' : ∀ r : ℝ, 0 < r → HasDerivAt g (g' r) r)
    (hgm : Measurable g) (B : ℝ) (hB : 0 ≤ B)
    (hgb : ∀ r : ℝ, 0 < r → ‖g r‖ ≤ B)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (t : ℝ) (ht : 0 < t) :
    let a := Real.exp (-t)
    let b := Real.sqrt (1 - Real.exp (-2 * t))
    let q := gaussianSmoothingRelativeDensity n ν a b
    let score := gaussianSmoothingScore n ν a b
    Integrable (fun x => g (q x) * ⟪score x, gradient φ x⟫ +
      φ x * g' (q x) * q x * ‖score x‖ ^ 2)
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
    HasDerivAt (fun s : ℝ => ∫ x : EuclideanSpace ℝ (Fin n), φ x *
      (standardGaussianDensity n x * ψ (gaussianSmoothingDensity n ν (Real.exp (-s))
        (Real.sqrt (1 - Real.exp (-2 * s))) x / standardGaussianDensity n x)))
      (-(∫ x, g (q x) * ⟪score x, gradient φ x⟫ +
        φ x * g' (q x) * q x * ‖score x‖ ^ 2
        ∂densityMeasure n (gaussianSmoothingDensity n ν a b))) t := by
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-2 * t))
  let q := gaussianSmoothingRelativeDensity n ν a b
  have hqprops := gaussianSmoothingRelativeDensity_properties n ν a b
    (ou_smoothing_scale_domain t ht).2.1
  let χ := entropyDerivativeTest n q hqprops.1 hqprops.2.1 g hg φ
  have hchain := (ou_compact_entropy_chain_rule n ν hU ψ g hψ hgm B hB hgb φ t ht).2
  have hfluxAll := ou_density_time_derivative_score_flux n ν hU χ t ht
  have hflux := hfluxAll.2
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      ⟪gaussianSmoothingScore n ν a b x, gradient χ x⟫ =
      g (q x) * ⟪gaussianSmoothingScore n ν a b x, gradient φ x⟫ +
        φ x * g' (q x) * q x * ‖gaussianSmoothingScore n ν a b x‖ ^ 2 :=
    entropyDerivativeTest_score_flux n q hqprops.1 hqprops.2.1 g g' hg hg' φ x
  have hderiv : (∫ x : EuclideanSpace ℝ (Fin n), φ x * g (q x) * ouDensityTimeDerivative n ν t x) =
      -(∫ x, g (q x) * ⟪gaussianSmoothingScore n ν a b x, gradient φ x⟫ +
        φ x * g' (q x) * q x * ‖gaussianSmoothingScore n ν a b x‖ ^ 2
        ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
    change (∫ x : EuclideanSpace ℝ (Fin n), χ x * ouDensityTimeDerivative n ν t x) = _
    rw [hflux]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  refine ⟨?_, ?_⟩
  · exact hfluxAll.1.congr (Filter.Eventually.of_forall hpoint)
  · change HasDerivAt _ _ _
    rw [← hderiv]
    exact hchain

end AffineFKProof
