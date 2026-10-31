module

public import AffineFK.OUFisherDissipation
public import AffineFK.FisherInformationMeasureIdentity
public import AffineFK.GaussianRelativeScoreHessian
public import AffineFK.GaussianSmoothingIsotropyMoments
public import AffineFK.OrdinaryWeakScoreSobolevSmooth

/-!
# Actual numerical ordinary information and logarithmic Hessian means

The square-root Sobolev graph identifies the canonical numerical ordinary
information. The actual Gaussian conditional second-ratio representation
has mean zero, so the logarithmic Hessian mean is minus the ordinary
score covariance. All identities concern the actual smoothed density;
no integration-by-parts-at-infinity or Hessian-mean premise is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace ENNReal

theorem gaussianSmoothing_ordinaryFisherMeasure_eq_energy (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    let ρ := gaussianSmoothingDensity n ν a b
    ordinaryFisherMeasure n (densityMeasure n ρ) ≠ (∞ : ℝ≥0∞) ∧
    (ordinaryFisherMeasure n (densityMeasure n ρ)).toReal =
      ∫ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 * ρ x := by
  let ρ := gaussianSmoothingDensity n ν a b
  have hρ := gaussianSmoothingDensity_smooth n ν a b
  have hpos := gaussianSmoothingDensity_pos n ν a b hb
  have : IsProbabilityMeasure (densityMeasure n ρ) := by
    change IsProbabilityMeasure (densityMeasure n (gaussianSmoothingDensity n ν a b))
    rw [← gaussianSmoothingDensity_law n ν a b hb]
    infer_instance
  have hs : MemLp (gradient (fun x => Real.log (ρ x))) 2 (densityMeasure n ρ) :=
    (gaussianSmoothing_ordinaryScore_density_memLp_four n ν a b hb).1.mono_exponent (by norm_num)
  obtain ⟨v, hv, _hgv, he⟩ := ordinaryWeakScore_smooth_sqrt_graph n ρ hρ hpos hs
  have hEq : ordinaryFisherMeasure n (densityMeasure n ρ) =
      ENNReal.ofReal (∫ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 * ρ x) := by
    rw [ordinaryFisherMeasure_density n ρ hρ.continuous.measurable
      (Filter.Eventually.of_forall fun x => (hpos x).le), fisherInformation_eq_graph n ρ v hv, he,
      density_integral_eq n ρ hρ.continuous (fun x => (hpos x).le)]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => mul_comm _ _
  refine ⟨hEq.trans_ne ENNReal.ofReal_ne_top, ?_⟩
  rw [hEq, ENNReal.toReal_ofReal (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hpos x).le)]

theorem gaussianSmoothing_secondDensityRatio_mean_zero (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i j : Fin n) (a b : ℝ) (hb : 0 < b) :
    (∫ x, secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j x
      ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ := stdGaussian E
  let μ := ν.prod γ
  let W : E × E → E := fun p => a • p.1 + b • p.2
  let A : E × E → ℝ := fun p => p.2 i * p.2 j - if i = j then 1 else 0
  have hW : Measurable W := by dsimp [W]; fun_prop
  obtain ⟨q, hq, _hq2, hrep, heq, _⟩ := gaussianSmoothing_secondDensityRatio_conditional n ν i j a b hb
  have hA : Integrable A μ := ((stdGaussian_quadratic_memLp n i j).comp_snd ν).integrable (by norm_num)
  have hmean : (∫ p, A p ∂μ) = 0 := by
    have hG := gaussianSmoothingIsotropy_gaussian_second n i j
    have h : (∫ g : E, (g i * g j - if i = j then (1 : ℝ) else 0) ∂γ) = 0 := by
      rw [integral_sub hG.1 (integrable_const _), hG.2, integral_const]
      simp only [probReal_univ, one_smul, sub_self]
    calc
      _ = ν.real Set.univ • (∫ g : E, (g i * g j - if i = j then (1 : ℝ) else 0) ∂γ) :=
        integral_fun_snd (μ := ν) (ν := γ) (fun g : E => g i * g j - if i = j then (1 : ℝ) else 0)
      _ = 0 := by rw [h, smul_zero]
  have hm : (inferInstance : MeasurableSpace E).comap W ≤
      (inferInstance : MeasurableSpace (E × E)) := hW.comap_le
  have hvalue : (∫ x, secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j x ∂μ.map W) = 0 := by
    calc
      _ = ∫ x, q x ∂μ.map W := integral_congr_ae heq.symm
      _ = ∫ p, q (W p) ∂μ := integral_map hW.aemeasurable hq.aestronglyMeasurable
      _ = ∫ p, (b⁻¹) ^ 2 * condExp ((inferInstance : MeasurableSpace E).comap W) μ A p ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => hrep p
      _ = (b⁻¹) ^ 2 * ∫ p, A p ∂μ := by rw [integral_const_mul, integral_condExp hm]
      _ = 0 := by rw [hmean, mul_zero]
  have hlaw : μ.map W = densityMeasure n (gaussianSmoothingDensity n ν a b) :=
    gaussianSmoothingDensity_law n ν a b hb
  rw [hlaw] at hvalue
  exact hvalue

theorem gaussianSmoothing_logHessian_mean (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i j : Fin n) (a b : ℝ) (hb : 0 < b) :
    (∫ x, densityLogHessian n (gaussianSmoothingDensity n ν a b) x i j
      ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) =
      -(∫ x, gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x i *
        gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x j
        ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
  let ρ := gaussianSmoothingDensity n ν a b
  have : IsProbabilityMeasure (densityMeasure n ρ) := by
    change IsProbabilityMeasure (densityMeasure n (gaussianSmoothingDensity n ν a b))
    rw [← gaussianSmoothingDensity_law n ν a b hb]
    infer_instance
  have hs : MemLp (gradient (fun x => Real.log (ρ x))) 2 (densityMeasure n ρ) :=
    (gaussianSmoothing_ordinaryScore_density_memLp_four n ν a b hb).1.mono_exponent (by norm_num)
  have hpoint : (fun x => densityLogHessian n ρ x i j) = fun x =>
      secondDensityRatio n ρ i j x - gradient (fun y => Real.log (ρ y)) x i *
        gradient (fun y => Real.log (ρ y)) x j := funext fun x =>
    densityLogHessian_eq_secondDensityRatio_sub_score_product n ρ
      (gaussianSmoothingDensity_smooth n ν a b) (gaussianSmoothingDensity_pos n ν a b hb) x i j
  change (∫ x, densityLogHessian n ρ x i j ∂densityMeasure n ρ) = _
  rw [hpoint, integral_sub (f := secondDensityRatio n ρ i j)
    (g := fun x => gradient (fun y => Real.log (ρ y)) x i * gradient (fun y => Real.log (ρ y)) x j)
    ((gaussianSmoothing_secondDensityRatio_memLp n ν i j a b hb).1.integrable (by norm_num))
    ((hs.eval_piLp i).integrable_mul (hs.eval_piLp j)),
    gaussianSmoothing_secondDensityRatio_mean_zero n ν i j a b hb, zero_sub]

theorem probability_integral_add_twice_add_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, f x + 2 * g x + 1 ∂μ) = (∫ x, f x ∂μ) + 2 * (∫ x, g x ∂μ) + 1 := by
  rw [integral_add (f := fun x => f x + 2 * g x) (g := fun _ => 1)
    (hf.add (hg.const_mul 2)) (integrable_const 1),
    integral_add (f := f) (g := fun x => 2 * g x) hf (hg.const_mul 2), integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]

theorem gaussianSmoothing_relative_hessian_energy_identity (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    let ρ := gaussianSmoothingDensity n ν a b
    Integrable (fun x => ∑ i : Fin n, ‖gradient (fun y => gaussianRelativeScore n ρ y i) x‖ ^ 2) (densityMeasure n ρ) ∧
    (∫ x, ∑ i : Fin n, ‖gradient (fun y => gaussianRelativeScore n ρ y i) x‖ ^ 2 ∂densityMeasure n ρ) =
      (∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ x) ∂densityMeasure n ρ) -
      2 * (∫ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 ∂densityMeasure n ρ) + n := by
  let ρ := gaussianSmoothingDensity n ν a b
  let μ := densityMeasure n ρ
  let s := gradient (fun x => Real.log (ρ x))
  have : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (densityMeasure n (gaussianSmoothingDensity n ν a b))
    rw [← gaussianSmoothingDensity_law n ν a b hb]
    infer_instance
  have hρ := gaussianSmoothingDensity_smooth n ν a b
  have hpos := gaussianSmoothingDensity_pos n ν a b hb
  have hs : MemLp s 2 μ := (gaussianSmoothing_ordinaryScore_density_memLp_four n ν a b hb).1.mono_exponent (by norm_num)
  have hrow (i : Fin n) : MemLp (gradient (fun y => s y i)) 2 μ :=
    gaussianSmoothing_logHessian_row_memLp n ν a b hb i
  have hrel (i : Fin n) : Integrable (fun x => ‖gradient (fun y => gaussianRelativeScore n ρ y i) x‖ ^ 2) μ :=
    (gaussianSmoothing_relativeScore_component_gradient_memLp n ν a b hb i).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hH (i : Fin n) : Integrable (fun x => densityLogHessian n ρ x i i) μ :=
    (gaussianSmoothing_logHessian_entry_memLp n ν a b hb i i).integrable (by norm_num)
  have hpoint (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
      ‖gradient (fun y => gaussianRelativeScore n ρ y i) x‖ ^ 2 =
        ‖gradient (fun y => s y i) x‖ ^ 2 + 2 * densityLogHessian n ρ x i i + 1 := by
    rw [gaussianRelativeScore_component_gradient n ρ hρ hpos, norm_add_sq_real,
      (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one, one_pow, real_inner_comm,
      EuclideanSpace.basisFun_inner]
    rfl
  refine ⟨integrable_finsetSum Finset.univ fun i _ => hrel i, ?_⟩
  have hEqRow (i : Fin n) :
      (∫ x, ‖gradient (fun y => gaussianRelativeScore n ρ y i) x‖ ^ 2 ∂μ) =
        (∫ x, ‖gradient (fun y => s y i) x‖ ^ 2 ∂μ) - 2 * (∫ x, (s x i) ^ 2 ∂μ) + 1 := by
    have hm : (∫ x, densityLogHessian n ρ x i i ∂μ) = -(∫ x, (s x i) ^ 2 ∂μ) := by
      simpa only [pow_two] using gaussianSmoothing_logHessian_mean n ν i i a b hb
    calc
      _ = ∫ x, ‖gradient (fun y => s y i) x‖ ^ 2 + 2 * densityLogHessian n ρ x i i + 1 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hpoint x i)
      _ = (∫ x, ‖gradient (fun y => s y i) x‖ ^ 2 ∂μ) +
          2 * (∫ x, densityLogHessian n ρ x i i ∂μ) + 1 :=
        probability_integral_add_twice_add_one μ _ _ ((hrow i).integrable_norm_pow (by norm_num)) (hH i)
      _ = _ := by rw [hm]; ring
  rw [integral_finsetSum Finset.univ (fun i _ => hrel i)]
  simp only [hEqRow, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hK : (∑ i : Fin n, ∫ x, ‖gradient (fun y => s y i) x‖ ^ 2 ∂μ) =
      ∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ x) ∂μ := by
    rw [← integral_finsetSum Finset.univ (fun i _ => (hrow i).integrable_norm_pow (by norm_num))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [EuclideanSpace.real_norm_sq_eq, matrixHilbertSchmidtSq, densityLogHessian, s]
  have hJ : (∑ i : Fin n, ∫ x, (s x i) ^ 2 ∂μ) = ∫ x, ‖s x‖ ^ 2 ∂μ := by
    rw [← integral_finsetSum Finset.univ (fun i _ => (hs.eval_piLp i).integrable_sq)]
    simp only [EuclideanSpace.real_norm_sq_eq]
  rw [hK, hJ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rfl

end AffineFKProof
