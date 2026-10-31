module

public import AffineFK.ConvolutionSecondRatioField
public import AffineFK.ConditionalCovarianceMatrix

/-!
# Actual convolution Hessian and conditional covariance

The conditional score and second-ratio fields have already been
identified with actual derivatives of the true smooth output density.
Their quotient formula gives the actual Hessian as conditional mean of
the input Hessian combination plus the genuine conditional covariance.
Positive semidefiniteness is then the proved conditional-covariance
theorem, not a marginal-Hessian or covariance-sign assumption.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Matrix
open scoped Distributions ContDiff ENNReal MatrixOrder Matrix.Norms.L2Operator

def convolutionHessianCombination (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => a ^ 2 * densityLogHessian n ρ₁ p.1 i j + b ^ 2 * densityLogHessian n ρ₂ p.2 i j

theorem convolutionScoreCombination_memLp_four (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 4 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 4 (densityMeasure n ρ₂)) (a b : ℝ) :
    MemLp (convolutionScoreCombination n ρ₁ ρ₂ a b) 4 ((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)) :=
  ((hs₁.comp_fst _).const_smul a).add ((hs₂.comp_snd _).const_smul b)

theorem convolutionSecondRatioCombination_eq_hessian_add_outer (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ₁ : ContDiff ℝ ∞ ρ₁) (hpos₁ : ∀ x, 0 < ρ₁ x)
    (hρ₂ : ContDiff ℝ ∞ ρ₂) (hpos₂ : ∀ x, 0 < ρ₂ x)
    (a b : ℝ) (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    convolutionSecondRatioCombination n ρ₁ ρ₂ a b p = convolutionHessianCombination n ρ₁ ρ₂ a b p +
      euclideanOuterBilinear n (convolutionScoreCombination n ρ₁ ρ₂ a b p)
        (convolutionScoreCombination n ρ₁ ρ₂ a b p) := by
  ext i j
  simp only [Matrix.add_apply, convolutionHessianCombination, convolutionSecondRatioCombination,
    euclideanOuterBilinear_apply, convolutionScoreCombination, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [densityLogHessian_eq_secondDensityRatio_sub_score_product n ρ₁ hρ₁ hpos₁ p.1 i j,
    densityLogHessian_eq_secondDensityRatio_sub_score_product n ρ₂ hρ₂ hpos₂ p.2 i j]
  ring

theorem convolutionHessianCombination_memLp (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ₁ : ContDiff ℝ ∞ ρ₁) (hpos₁ : ∀ x, 0 < ρ₁ x)
    (hρ₂ : ContDiff ℝ ∞ ρ₂) (hpos₂ : ∀ x, 0 < ρ₂ x)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 4 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 4 (densityMeasure n ρ₂))
    (hq₁ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₁ i j) 2 (densityMeasure n ρ₁))
    (hq₂ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₂ i j) 2 (densityMeasure n ρ₂))
    (a b : ℝ) : MemLp (convolutionHessianCombination n ρ₁ ρ₂ a b) 2
      ((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)) := by
  let μ := (densityMeasure n ρ₁).prod (densityMeasure n ρ₂)
  let S := convolutionScoreCombination n ρ₁ ρ₂ a b
  let : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv,
      ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
    all_goals norm_num⟩
  have hS : MemLp S 4 μ := convolutionScoreCombination_memLp_four n ρ₁ ρ₂ hs₁ hs₂ a b
  have hO : MemLp (fun p => euclideanOuterBilinear n (S p) (S p)) 2 μ :=
    (euclideanOuterBilinear n).memLp_of_bilin 2 hS hS
  have hR : MemLp (convolutionSecondRatioCombination n ρ₁ ρ₂ a b) 2 μ :=
    convolutionSecondRatioCombination_memLp n ρ₁ ρ₂ hs₁ hs₂ hq₁ hq₂ a b
  apply (hR.sub hO).ae_eq
  exact Filter.Eventually.of_forall fun p => by
    change convolutionSecondRatioCombination n ρ₁ ρ₂ a b p - euclideanOuterBilinear n (S p) (S p) = _
    rw [convolutionSecondRatioCombination_eq_hessian_add_outer n ρ₁ ρ₂ hρ₁ hpos₁ hρ₂ hpos₂ a b p]
    exact add_sub_cancel_right _ _

theorem densityLogHessian_eq_secondRatioMatrix_sub_outer (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    (x : EuclideanSpace ℝ (Fin n)) :
    densityLogHessian n ρ x = densitySecondRatioMatrix n ρ x -
      euclideanOuterBilinear n (gradient (fun y => Real.log (ρ y)) x) (gradient (fun y => Real.log (ρ y)) x) := by
  ext i j
  exact densityLogHessian_eq_secondDensityRatio_sub_score_product n ρ hρ hpos x i j

theorem convolution_hessian_conditional_covariance_identity (n : ℕ)
    (ρ₁ ρ₂ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ₁ : ContDiff ℝ ∞ ρ₁) (hpos₁ : ∀ x, 0 < ρ₁ x)
    (hρ₂ : ContDiff ℝ ∞ ρ₂) (hpos₂ : ∀ x, 0 < ρ₂ x)
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 4 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 4 (densityMeasure n ρ₂))
    (hq₁ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₁ i j) 2 (densityMeasure n ρ₁))
    (hq₂ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₂ i j) 2 (densityMeasure n ρ₂))
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (hlaw : ((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2) = densityMeasure n ρ) :
    let μ := (densityMeasure n ρ₁).prod (densityMeasure n ρ₂)
    let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun p => a • p.1 + b • p.2
    let m := (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W
    let S := convolutionScoreCombination n ρ₁ ρ₂ a b
    ∀ᵐ p ∂μ, densityLogHessian n ρ (W p) =
      condExp m μ (convolutionHessianCombination n ρ₁ ρ₂ a b) p +
        (condExp m μ (fun z => euclideanOuterBilinear n (S z) (S z)) p -
          euclideanOuterBilinear n (condExp m μ S p) (condExp m μ S p)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let mΩ : MeasurableSpace (E × E) := inferInstance
  let μ := (densityMeasure n ρ₁).prod (densityMeasure n ρ₂)
  let W : E × E → E := fun p => a • p.1 + b • p.2
  let m := (inferInstance : MeasurableSpace E).comap W
  let : MeasurableSpace (E × E) := mΩ
  let S := convolutionScoreCombination n ρ₁ ρ₂ a b
  let R := convolutionSecondRatioCombination n ρ₁ ρ₂ a b
  let H := convolutionHessianCombination n ρ₁ ρ₂ a b
  let O : E × E → Matrix (Fin n) (Fin n) ℝ := fun p => euclideanOuterBilinear n (S p) (S p)
  obtain ⟨r, _hr, _hr2, _hrep, _heq, _hout2, hSpull⟩ :=
    convolution_score_conditional_identification n ρ₁ ρ₂ ρ hρ₁ hpos₁ hρ₂ hpos₂ hρ hpos
      (hs₁.mono_exponent (by norm_num)) (hs₂.mono_exponent (by norm_num)) a b ha hb hab hlaw
  obtain ⟨q, _hq, _hq2, _hqrep, _hqeq, _hQout2, hQpull⟩ :=
    convolution_second_ratio_conditional_identification n ρ₁ ρ₂ ρ hρ₁ hpos₁ hρ₂ hpos₂ hρ hpos
      hs₁ hs₂ hq₁ hq₂ a b ha hb hab hlaw
  have hH : MemLp H 2 μ := convolutionHessianCombination_memLp n ρ₁ ρ₂ hρ₁ hpos₁ hρ₂ hpos₂ hs₁ hs₂ hq₁ hq₂ a b
  have hS : MemLp S 2 μ := (convolutionScoreCombination_memLp_four n ρ₁ ρ₂ hs₁ hs₂ a b).mono_exponent (by norm_num)
  have hO : Integrable O μ := memLp_one_iff_integrable.mp ((euclideanOuterBilinear n).memLp_of_bilin 1 hS hS)
  have hdata : R = H + O := by
    funext p
    exact convolutionSecondRatioCombination_eq_hessian_add_outer n ρ₁ ρ₂ hρ₁ hpos₁ hρ₂ hpos₂ a b p
  have hCE : condExp m μ R =ᵐ[μ] condExp m μ H + condExp m μ O := by
    rw [hdata]
    exact condExp_add (hH.integrable (by norm_num)) hO m
  filter_upwards [hSpull, hQpull, hCE] with p hpS hpQ hpCE
  rw [densityLogHessian_eq_secondRatioMatrix_sub_outer n ρ hρ hpos (W p), hpQ, hpS, hpCE]
  change (condExp m μ H p + condExp m μ O p) -
      euclideanOuterBilinear n (condExp m μ S p) (condExp m μ S p) = _
  abel

theorem convolution_hessian_conditional_comparison (n : ℕ)
    (ρ₁ ρ₂ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ₁ : ContDiff ℝ ∞ ρ₁) (hpos₁ : ∀ x, 0 < ρ₁ x)
    (hρ₂ : ContDiff ℝ ∞ ρ₂) (hpos₂ : ∀ x, 0 < ρ₂ x)
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 4 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 4 (densityMeasure n ρ₂))
    (hq₁ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₁ i j) 2 (densityMeasure n ρ₁))
    (hq₂ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₂ i j) 2 (densityMeasure n ρ₂))
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (hlaw : ((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2) = densityMeasure n ρ) :
    let μ := (densityMeasure n ρ₁).prod (densityMeasure n ρ₂)
    let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun p => a • p.1 + b • p.2
    let m := (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W
    ∀ᵐ p ∂μ, (densityLogHessian n ρ (W p) - condExp m μ (convolutionHessianCombination n ρ₁ ρ₂ a b) p).PosSemidef := by
  let E := EuclideanSpace ℝ (Fin n)
  let mΩ : MeasurableSpace (E × E) := inferInstance
  let μ := (densityMeasure n ρ₁).prod (densityMeasure n ρ₂)
  let W : E × E → E := fun p => a • p.1 + b • p.2
  let m := (inferInstance : MeasurableSpace E).comap W
  let : MeasurableSpace (E × E) := mΩ
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hS : MemLp (convolutionScoreCombination n ρ₁ ρ₂ a b) 2 μ :=
    (convolutionScoreCombination_memLp_four n ρ₁ ρ₂ hs₁ hs₂ a b).mono_exponent (by norm_num)
  have hIdentity := convolution_hessian_conditional_covariance_identity n ρ₁ ρ₂ ρ hρ₁ hpos₁ hρ₂ hpos₂ hρ hpos
    hs₁ hs₂ hq₁ hq₂ a b ha hb hab hlaw
  have hPSD := conditional_covariance_matrix_posSemidef μ m hW.comap_le n _ hS
  filter_upwards [hIdentity, hPSD] with p hp hposp
  rw [hp]
  convert! hposp using 1
  abel

end AffineFKProof
