module

public import AffineFK.OUDensityTimeDerivativeBounds
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# A genuine compact spatial entropy chain rule for the OU density

The scalar function is differentiated only at positive relative densities.
Its first derivative is bounded on that domain. The dominating function
comes from the proved compact space/time kernel-derivative bound and the
actual compact test. This is a proved chain rule under an integral, not an
assumed entropy-dissipation premise. Removing the spatial cutoff and then
the scalar truncation remain separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Filter Set
open scoped Distributions Topology

theorem ou_density_time_derivative_stronglyMeasurable (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] (t : ℝ) :
    StronglyMeasurable (ouDensityTimeDerivative n ν t) := by
  let E := EuclideanSpace ℝ (Fin n)
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-2 * t))
  let r := b⁻¹
  let d := -(Real.exp (-2 * t) / b) / b ^ 2
  have hkD : Continuous (fderiv ℝ (standardGaussianDensity n)) :=
    ((standardGaussianDensity_smooth n).fderiv_right (m := 0) (by simp)).continuous
  have hI0 : StronglyMeasurable (fun x : E =>
      ∫ u, standardGaussianDensity n (r • (x - a • u)) ∂ν) := by
    apply StronglyMeasurable.integral_prod_right
    have hc : Continuous (fun p : E × E => standardGaussianDensity n (r • (p.1 - a • p.2))) :=
      (standardGaussianDensity_smooth n).continuous.comp (by fun_prop)
    exact hc.stronglyMeasurable
  have hI1 : StronglyMeasurable (fun x : E =>
      ∫ u, fderiv ℝ (standardGaussianDensity n) (r • (x - a • u))
        (r • (a • u) + d • (x - a • u)) ∂ν) := by
    apply StronglyMeasurable.integral_prod_right
    have hc : Continuous (fun p : E × E => fderiv ℝ (standardGaussianDensity n)
        (r • (p.1 - a • p.2)) (r • (a • p.2) + d • (p.1 - a • p.2))) :=
      (hkD.comp (by fun_prop)).clm_apply (by fun_prop)
    exact hc.stronglyMeasurable
  exact (hI0.const_mul ((n : ℝ) * r ^ (n - 1) * d)).add (hI1.const_mul (r ^ n))

theorem ou_compact_entropy_chain_rule (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (ψ ψ' : ℝ → ℝ)
    (hψ : ∀ q : ℝ, 0 < q → HasDerivAt ψ (ψ' q) q)
    (hψ'm : Measurable ψ') (B : ℝ) (hB : 0 ≤ B)
    (hψ'b : ∀ q : ℝ, 0 < q → ‖ψ' q‖ ≤ B)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x => φ x * ψ' (gaussianSmoothingDensity n ν (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t))) x / standardGaussianDensity n x) *
        ouDensityTimeDerivative n ν t x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    HasDerivAt (fun s : ℝ => ∫ x : EuclideanSpace ℝ (Fin n), φ x *
      (standardGaussianDensity n x * ψ (gaussianSmoothingDensity n ν (Real.exp (-s))
        (Real.sqrt (1 - Real.exp (-2 * s))) x / standardGaussianDensity n x)))
      (∫ x : EuclideanSpace ℝ (Fin n), φ x * ψ' (gaussianSmoothingDensity n ν (Real.exp (-t))
        (Real.sqrt (1 - Real.exp (-2 * t))) x / standardGaussianDensity n x) *
          ouDensityTimeDerivative n ν t x) t := by
  let E := EuclideanSpace ℝ (Fin n)
  let k : E → ℝ := standardGaussianDensity n
  let ρ : ℝ → E → ℝ := fun s => gaussianSmoothingDensity n ν (Real.exp (-s))
    (Real.sqrt (1 - Real.exp (-2 * s)))
  let q : ℝ → E → ℝ := fun s x => ρ s x / k x
  let D : ℝ → E → ℝ := ouDensityTimeDerivative n ν
  have hkpos (x : E) : 0 < k x := standardGaussianDensity_pos n x
  have hρ (s : ℝ) : Continuous (ρ s) := gaussianSmoothingDensity_continuous n ν _ _
  have hq (s : ℝ) : Continuous (q s) :=
    (hρ s).div (standardGaussianDensity_smooth n).continuous (fun x => (hkpos x).ne')
  have hqpos (s : ℝ) (hs : 0 < s) (x : E) : 0 < q s x :=
    div_pos (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain s hs).2.1 x) (hkpos x)
  have hψq (s : ℝ) (hs : 0 < s) : Continuous (fun x : E => ψ (q s x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hψ (q s x) (hqpos s hs x)).continuousAt.comp (hq s).continuousAt
  obtain ⟨M, hM, hMbound⟩ := φ.hasCompactSupport.isBounded.exists_pos_norm_le
  obtain ⟨S, hS, C, hC, hCb⟩ := ou_density_time_derivative_local_bound n ν hU t ht M hM.le
  let F : ℝ → E → ℝ := fun s x => φ x * (k x * ψ (q s x))
  let F' : ℝ → E → ℝ := fun s x => φ x * ψ' (q s x) * D s x
  have hF (s : ℝ) (hs : 0 < s) : Continuous (F s) :=
    φ.continuous.mul ((standardGaussianDensity_smooth n).continuous.mul (hψq s hs))
  have hF_int : Integrable (F t) (volume : Measure E) :=
    (hF t ht).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hF'_meas : AEStronglyMeasurable (F' t) (volume : Measure E) :=
    ((φ.continuous.measurable.mul (hψ'm.comp (hq t).measurable)).stronglyMeasurable.mul
      (ou_density_time_derivative_stronglyMeasurable n ν t)).aestronglyMeasurable
  let bound : E → ℝ := fun x => (B * C) * ‖φ x‖
  have hbound_int : Integrable bound (volume : Measure E) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.const_mul (B * C)
  have hbound : ∀ᵐ x ∂(volume : Measure E), ∀ s ∈ S, ‖F' s x‖ ≤ bound x := by
    exact Filter.Eventually.of_forall fun x s hs => by
      by_cases hx : φ x = 0
      · simp only [F', bound, hx, zero_mul, norm_zero, mul_zero, le_refl]
      · have hxM : ‖x‖ ≤ M := hMbound x (subset_tsupport φ hx)
        have hds := (hCb s hs).2 x hxM
        calc
          ‖F' s x‖ = ‖φ x‖ * ‖ψ' (q s x)‖ * ‖D s x‖ := by simp only [F', norm_mul]
          _ ≤ ‖φ x‖ * B * C := mul_le_mul
            (mul_le_mul_of_nonneg_left (hψ'b _ (hqpos s (hCb s hs).1 x)) (norm_nonneg _))
            hds (norm_nonneg _) (mul_nonneg (norm_nonneg _) hB)
          _ = bound x := by dsimp [bound]; ring
  have hdiff : ∀ᵐ x ∂(volume : Measure E), ∀ s ∈ S, HasDerivAt (F · x) (F' s x) s := by
    exact Filter.Eventually.of_forall fun x s hs => by
      have hd := (ou_density_time_derivative_hasDerivAt n ν hU x s (hCb s hs).1).div_const (k x)
      have hqder : HasDerivAt (fun s => q s x) (D s x / k x) s := hd
      have hcomp := ((hψ _ (hqpos s (hCb s hs).1 x)).comp s hqder).const_mul (φ x * k x)
      convert! hcomp using 1
      · funext r
        dsimp [F]
        ring
      · dsimp [F']
        field_simp [(hkpos x).ne']
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (volume : Measure E) := by
    filter_upwards [hS] with s hs
    exact (hF s (hCb s hs).1).aestronglyMeasurable
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    hF_meas hF_int hF'_meas hbound hbound_int hdiff

end AffineFKProof
