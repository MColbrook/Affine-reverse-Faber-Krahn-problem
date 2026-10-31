module

public import AffineFK.GaussianPositionRestriction
public import AffineFK.StrongLogConcavePoincareLimit

/-!
# Poincare and covariance upper bounds for a restricted Gaussian

The normalized restriction to a measurable convex set has an actual
Lebesgue density. Its quadratic exponential tilt is constant on that
set, so the supported strong log-concavity theorem gives Poincare
constant at most one. No boundary smoothness is required.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ContDiff

theorem gaussianPosition_logConcave_indicator_const {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (K : Set E) (hK : Convex ℝ K) (c : ℝ≥0∞) :
    LogConcaveDensity (K.indicator (fun _ : E => c)) := by
  classical
  intro t ht ht1 x y
  rcases ht.eq_or_lt with ht0 | htpos
  · subst t
    simp
  rcases ht1.eq_or_lt with htone | htlt
  · subst t
    simp
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ K
    · have hz := hK hx hy (sub_nonneg.mpr ht1) ht (by ring : (1 - t) + t = 1)
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
      exact logConcaveDensity_const c t ht ht1 x y
    · simp only [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos htpos, mul_zero]
      exact zero_le
  · simp only [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos (sub_pos.mpr htlt), zero_mul]
    exact zero_le

def gaussianPositionRestrictedDensity (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  K.indicator (fun y => ((stdGaussian (EuclideanSpace ℝ (Fin n))) K).toReal⁻¹ *
    standardGaussianDensity n y) x

theorem gaussianPositionRestrictedDensity_measurable (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K) :
    Measurable (gaussianPositionRestrictedDensity n K) :=
  (measurable_const.mul (standardGaussianDensity_smooth n).continuous.measurable).indicator hK

theorem gaussianPositionRestrictedDensity_nonneg (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ gaussianPositionRestrictedDensity n K x := by
  classical
  exact Set.indicator_nonneg (fun y _ =>
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (standardGaussianDensity_pos n y).le) x

theorem gaussianPositionRestrictedDensity_law (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0) :
    densityMeasure n (gaussianPositionRestrictedDensity n K) =
      ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K := by
  classical
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hq : 0 < (γ K).toReal := ENNReal.toReal_pos hKpos (measure_ne_top γ K)
  have heq : (fun x => ENNReal.ofReal (gaussianPositionRestrictedDensity n K x)) =
      (γ K)⁻¹ • K.indicator (fun x => ENNReal.ofReal (standardGaussianDensity n x)) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [gaussianPositionRestrictedDensity, Set.indicator_of_mem hx,
        Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg)]
      rw [ENNReal.ofReal_inv_of_pos hq, ENNReal.ofReal_toReal (measure_ne_top γ K)]
    · simp [gaussianPositionRestrictedDensity, hx]
  rw [densityMeasure, heq,
    withDensity_smul (γ K)⁻¹
      ((standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal.indicator hK),
    withDensity_indicator hK, ← restrict_withDensity hK]
  change (γ K)⁻¹ • (densityMeasure n (standardGaussianDensity n)).restrict K = _
  rw [← stdGaussian_eq_densityMeasure]
  rfl

theorem gaussianPosition_gaussian_quadratic_tilt (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    standardGaussianDensity n x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2) =
      Real.exp ((n : ℝ) * Real.log ((Real.sqrt (2 * Real.pi))⁻¹)) := by
  rw [← Real.exp_log (standardGaussianDensity_pos n x), ← Real.exp_add,
    log_standardGaussianDensity]
  congr 1
  ring

theorem gaussianPositionRestrictedDensity_strong_logConcave (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : Convex ℝ K) :
    LogConcaveDensity (fun x => ENNReal.ofReal
      (gaussianPositionRestrictedDensity n K x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2))) := by
  classical
  have heq : (fun x => ENNReal.ofReal
      (gaussianPositionRestrictedDensity n K x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2))) =
      K.indicator (fun _ => ENNReal.ofReal
        (((stdGaussian (EuclideanSpace ℝ (Fin n))) K).toReal⁻¹ *
          Real.exp ((n : ℝ) * Real.log ((Real.sqrt (2 * Real.pi))⁻¹)))) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [gaussianPositionRestrictedDensity, Set.indicator_of_mem hx]
      rw [mul_assoc, gaussianPosition_gaussian_quadratic_tilt]
    · simp [gaussianPositionRestrictedDensity, hx]
  rw [heq]
  exact gaussianPosition_logConcave_indicator_const K hK _

theorem gaussianPosition_cond_poincareConstant_le_one (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hKconv : Convex ℝ K) (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0) :
    poincareConstant n (ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) ≤ 1 := by
  let : IsProbabilityMeasure (ProbabilityTheory.cond
      (stdGaussian (EuclideanSpace ℝ (Fin n))) K) := cond_isProbabilityMeasure hKpos
  let : IsProbabilityMeasure (densityMeasure n (gaussianPositionRestrictedDensity n K)) := by
    rw [gaussianPositionRestrictedDensity_law n K hK hKpos]
    infer_instance
  have h := strongLogConcave_density_poincareConstant_le_one n
    (gaussianPositionRestrictedDensity n K)
    (gaussianPositionRestrictedDensity_measurable n K hK)
    (gaussianPositionRestrictedDensity_nonneg n K)
    (gaussianPositionRestrictedDensity_strong_logConcave n K hKconv)
  rwa [gaussianPositionRestrictedDensity_law n K hK hKpos] at h

theorem gaussianPosition_cond_second_moment_le_one (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hKconv : Convex ℝ K) (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0)
    (hneg : ∀ x, -x ∈ K ↔ x ∈ K) (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i * x i
      ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) ≤ 1 := by
  let ν := ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure hKpos
  have hf : MemLp (coordinateFunctional n i) 2 ν := by
    have he := funext (coordinateFunctional_apply n i)
    rw [he]
    exact gaussianPosition_cond_coordinate_memLp n K hKpos i
  have hg : MemLp (gradient (coordinateFunctional n i)) 2 ν := by
    rw [show gradient (coordinateFunctional n i) =
      (fun _ : EuclideanSpace ℝ (Fin n) => EuclideanSpace.basisFun (Fin n) ℝ i) from
        funext (coordinateFunctional_gradient n i)]
    exact memLp_const _
  have h := poincareConstant_le_smooth_L2 n ν 1
    (gaussianPosition_cond_poincareConstant_le_one n K hK hKconv hKpos)
    (coordinateFunctional n i) (coordinateFunctional n i).contDiff hf hg
  simp_rw [coordinateFunctional_apply, coordinateFunctional_gradient] at h
  rw [gaussianPosition_cond_coordinate_mean_zero n K hK hKpos hneg i] at h
  simpa only [sub_zero, pow_two, NNReal.coe_one, one_mul,
    (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one, mul_one, integral_const,
    probReal_univ, one_smul] using h

theorem gaussianPosition_exists_bounded_isotropic_restriction (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (hKconv : Convex ℝ K) (hneg : ∀ x, -x ∈ K ↔ x ∈ K) :
    ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ, ∃ α : ℝ,
      GaussianPositionMaximal n (gaussianPositionSLLinear n S '' K) ∧
      0 < α ∧ α ≤ 1 ∧
      poincareConstant n (ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n)))
        (gaussianPositionSLLinear n S '' K)) ≤ 1 ∧
      (∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i
        ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n)))
          (gaussianPositionSLLinear n S '' K)) = 0) ∧
      ∀ i j : Fin n, covariance (fun x : EuclideanSpace ℝ (Fin n) => x i) (fun x => x j)
        (ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n)))
          (gaussianPositionSLLinear n S '' K)) = if i = j then α else 0 := by
  obtain ⟨S, hmax, α, hαpos, hmean, hcov⟩ :=
    gaussianPosition_exists_isotropic_restriction n hn K hK hvol hneg
  let L := gaussianPositionSLLinear n S '' K
  have hLcompact : IsCompact L := hK.image (gaussianPositionSLLinear n S).continuous
  have hLconv : Convex ℝ L := by
    intro x hx y hy a b ha hb hab
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    exact ⟨a • u + b • v, hKconv hu hv ha hb hab, by simp only [map_add, map_smul]⟩
  have hLneg := gaussianPosition_even_linear_image n K hneg S
  have hLvolume : (volume : Measure (EuclideanSpace ℝ (Fin n))) L = volume K := by
    dsimp only [L]
    rw [Measure.addHaar_image_continuousLinearEquiv, gaussianPositionSLLinear_det]
    simp
  have hLpos := gaussianPosition_gaussian_pos_of_volume_pos n L (by rw [hLvolume]; exact hvol)
  let : IsProbabilityMeasure (ProbabilityTheory.cond
      (stdGaussian (EuclideanSpace ℝ (Fin n))) L) := cond_isProbabilityMeasure hLpos
  let i : Fin n := ⟨0, hn⟩
  have hbound := gaussianPosition_cond_second_moment_le_one n L hLcompact.measurableSet
    hLconv hLpos hLneg i
  have hi := hcov i i
  rw [covariance_eq_sub (gaussianPosition_cond_coordinate_memLp n L hLpos i)
    (gaussianPosition_cond_coordinate_memLp n L hLpos i), hmean i,
    zero_mul, sub_zero, if_pos rfl] at hi
  change (∫ x : EuclideanSpace ℝ (Fin n), x i * x i
    ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) L) = α at hi
  rw [hi] at hbound
  exact ⟨S, α, hmax, hαpos, hbound,
    gaussianPosition_cond_poincareConstant_le_one n L hLcompact.measurableSet hLconv hLpos,
    hmean, hcov⟩

end AffineFKProof
