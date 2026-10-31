module

public import AffineFK.GaussianPositionExistence
public import AffineFK.SteinSumLaw
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Moments.Covariance

/-!
# The actual normalized restricted Gaussian at a maximal position

The conditioning measure is Mathlib's actual restriction and scalar
normalization. Its coordinate L2 membership, reflection symmetry, zero
means and scalar covariance follow from the original set and maximality.
Absolute continuity excludes a zero covariance in positive dimension.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem gaussianPosition_gaussian_pos_of_volume_pos (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hvol : 0 < volume K) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0 := by
  have hac : (volume : Measure (EuclideanSpace ℝ (Fin n))) ≪
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    rw [stdGaussian_eq_densityMeasure, densityMeasure]
    exact withDensity_absolutelyContinuous'
      (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x =>
        (ENNReal.ofReal_pos.mpr (standardGaussianDensity_pos n x)).ne')
  intro hzero
  exact hvol.ne' (hac hzero)

theorem gaussianPosition_cond_coordinate_memLp (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0) (i : Fin n) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2
      (ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) := by
  have h := (IsGaussian.memLp_dual (stdGaussian (EuclideanSpace ℝ (Fin n)))
    (coordinateFunctional n i) 2 (by norm_num)).restrict K
  have h' := h.smul_measure (ENNReal.inv_ne_top.mpr hKpos)
  have heq : (coordinateFunctional n i : EuclideanSpace ℝ (Fin n) → ℝ) =
      (fun x : EuclideanSpace ℝ (Fin n) => x i) :=
    funext (coordinateFunctional_apply n i)
  rw [heq] at h'
  simpa only [ProbabilityTheory.cond] using h'

theorem gaussianPosition_standardGaussian_even (n : ℕ) :
    Measure.IsNegInvariant (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [stdGaussian_eq_densityMeasure, densityMeasure]
  apply even_density_neg_invariant volume _
    (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal
  intro x
  congr 1
  apply Real.log_injOn_pos (standardGaussianDensity_pos n _) (standardGaussianDensity_pos n _)
  simp only [log_standardGaussianDensity, norm_neg]

theorem gaussianPosition_cond_even (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hneg : ∀ x, -x ∈ K ↔ x ∈ K) :
    Measure.IsNegInvariant (ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) := by
  classical
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let : Measure.IsNegInvariant γ := gaussianPosition_standardGaussian_even n
  have hρ : Measurable (K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)) :=
    measurable_const.indicator hK
  have heven (x : EuclideanSpace ℝ (Fin n)) :
      K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (-x) =
      K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) x := by
    change (if -x ∈ K then (1 : ℝ≥0∞) else 0) =
      (if x ∈ K then (1 : ℝ≥0∞) else 0)
    rw [hneg x]
  have hr := even_density_neg_invariant γ _ hρ heven
  rw [withDensity_indicator_one hK] at hr
  let : Measure.IsNegInvariant (γ.restrict K) := hr
  constructor
  change (ProbabilityTheory.cond γ K).map Neg.neg = ProbabilityTheory.cond γ K
  rw [ProbabilityTheory.cond, Measure.map_smul _ measurable_neg.aemeasurable, Measure.map_neg_eq_self]

theorem gaussianPosition_cond_coordinate_mean_zero (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0)
    (hneg : ∀ x, -x ∈ K ↔ x ∈ K) (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = 0 := by
  let ν := ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure hKpos
  let : Measure.IsNegInvariant ν := gaussianPosition_cond_even n K hK hneg
  exact (odd_tensor_integral_zero ν (fun x => x i)
    (gaussianPosition_cond_coordinate_memLp n K hKpos i)
    (Filter.Eventually.of_forall fun x => by change (-x) i = -(x i); rfl)).2

theorem gaussianPosition_cond_second_moments (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hmax : GaussianPositionMaximal n K) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
        ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = if i = j then α else 0 := by
  obtain ⟨β, hβ, hm⟩ := gaussianPosition_maximal_second_moments n K hK hmax
  refine ⟨((stdGaussian (EuclideanSpace ℝ (Fin n))) K).toReal⁻¹ * β,
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) hβ, ?_⟩
  intro i j
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, hm i j]
  split_ifs <;> simp

theorem gaussianPosition_coordinate_second_moment_pos (n : ℕ) (i : Fin n)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] (hν : ν ≪ volume)
    (hi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν) :
    0 < ∫ x : EuclideanSpace ℝ (Fin n), x i * x i ∂ν := by
  have hker : (coordinateFunctional n i).toLinearMap.ker ≠ ⊤ := by
    intro h
    have hx : EuclideanSpace.basisFun (Fin n) ℝ i ∈ (coordinateFunctional n i).toLinearMap.ker := by
      rw [h]; trivial
    change coordinateFunctional n i (EuclideanSpace.basisFun (Fin n) ℝ i) = 0 at hx
    rw [coordinateFunctional_apply] at hx
    simp [EuclideanSpace.basisFun_apply] at hx
  have hset : {x : EuclideanSpace ℝ (Fin n) | x i = 0} =
      (coordinateFunctional n i).toLinearMap.ker := by
    ext x
    change x i = 0 ↔ coordinateFunctional n i x = 0
    rw [coordinateFunctional_apply]
  have hnull : ν {x : EuclideanSpace ℝ (Fin n) | x i = 0} = 0 := hν (by
    rw [hset]
    exact Measure.addHaar_submodule volume _ hker)
  have hInt := hi.integrable_mul hi
  by_contra hpos
  have hzero : (∫ x : EuclideanSpace ℝ (Fin n), x i * x i ∂ν) = 0 :=
    le_antisymm (le_of_not_gt hpos) (integral_nonneg fun _ => mul_self_nonneg _)
  have hae : ∀ᵐ x ∂ν, x i = 0 :=
    ((integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (x i)) hInt).mp hzero).mono
      (fun x hx => mul_self_eq_zero.mp hx)
  have hfull := (ae_mem_iff_measure_eq
    (show MeasurableSet {x : EuclideanSpace ℝ (Fin n) | x i = 0} from
      (show Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i) by fun_prop)
        (measurableSet_singleton 0)).nullMeasurableSet).mp hae
  rw [hnull, measure_univ] at hfull
  exact zero_ne_one hfull

theorem gaussianPosition_cond_covariance (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0)
    (hneg : ∀ x, -x ∈ K ↔ x ∈ K) (hmax : GaussianPositionMaximal n K) :
    ∃ α : ℝ, 0 < α ∧
      (∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i
        ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = 0) ∧
      ∀ i j : Fin n, covariance (fun x : EuclideanSpace ℝ (Fin n) => x i) (fun x => x j)
        (ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = if i = j then α else 0 := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let ν := ProbabilityTheory.cond γ K
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure hKpos
  have hγ : γ ≪ volume := by
    dsimp only [γ]
    rw [stdGaussian_eq_densityMeasure]
    exact withDensity_absolutelyContinuous _ _
  have hν : ν ≪ volume :=
    ((Measure.smul_absolutelyContinuous : ν ≪ γ.restrict K).trans
      Measure.absolutelyContinuous_restrict).trans hγ
  obtain ⟨α, _, hm⟩ := gaussianPosition_cond_second_moments n K hK hmax
  let i₀ : Fin n := ⟨0, hn⟩
  have hpos := gaussianPosition_coordinate_second_moment_pos n i₀ ν hν
    (gaussianPosition_cond_coordinate_memLp n K hKpos i₀)
  rw [hm i₀ i₀, ite_eq_left rfl] at hpos
  have hmean := gaussianPosition_cond_coordinate_mean_zero n K hK.measurableSet hKpos hneg
  refine ⟨α, hpos, hmean, ?_⟩
  intro i j
  rw [covariance_eq_sub (gaussianPosition_cond_coordinate_memLp n K hKpos i)
    (gaussianPosition_cond_coordinate_memLp n K hKpos j), hmean i, hmean j, zero_mul, sub_zero]
  exact hm i j

theorem gaussianPosition_even_linear_image (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hneg : ∀ x, -x ∈ K ↔ x ∈ K)
    (S : Matrix.SpecialLinearGroup (Fin n) ℝ) :
    ∀ x, -x ∈ gaussianPositionSLLinear n S '' K ↔ x ∈ gaussianPositionSLLinear n S '' K := by
  intro x
  constructor
  · rintro ⟨y, hy, heq⟩
    refine ⟨-y, (hneg y).mpr hy, ?_⟩
    rw [map_neg, heq, neg_neg]
  · rintro ⟨y, hy, heq⟩
    refine ⟨-y, (hneg y).mpr hy, ?_⟩
    rw [map_neg, heq]

theorem gaussianPosition_exists_isotropic_restriction (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (hneg : ∀ x, -x ∈ K ↔ x ∈ K) :
    ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ,
      GaussianPositionMaximal n (gaussianPositionSLLinear n S '' K) ∧
      ∃ α : ℝ, 0 < α ∧
        (∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i
          ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) (gaussianPositionSLLinear n S '' K)) = 0) ∧
        ∀ i j : Fin n, covariance (fun x : EuclideanSpace ℝ (Fin n) => x i) (fun x => x j)
          (ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) (gaussianPositionSLLinear n S '' K)) =
            if i = j then α else 0 := by
  obtain ⟨S, hmax⟩ := gaussianPosition_exists_maximal n K hK hvol
  have hSK : IsCompact (gaussianPositionSLLinear n S '' K) :=
    hK.image (gaussianPositionSLLinear n S).continuous
  have hvolume : (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (gaussianPositionSLLinear n S '' K) = volume K := by
    rw [Measure.addHaar_image_continuousLinearEquiv, gaussianPositionSLLinear_det]
    simp
  have hpos : stdGaussian (EuclideanSpace ℝ (Fin n)) (gaussianPositionSLLinear n S '' K) ≠ 0 :=
    gaussianPosition_gaussian_pos_of_volume_pos n _ (by rw [hvolume]; exact hvol)
  exact ⟨S, hmax, gaussianPosition_cond_covariance n hn _ hSK hpos
    (gaussianPosition_even_linear_image n K hneg S) hmax⟩

end AffineFKProof
