module

public import AffineFK.ConvolutionHessianProjection
public import AffineFK.ConditionalVectorFieldL4
public import AffineFK.LogConcaveDensityHessian
public import AffineFK.ConditionalMatrixHilbertSchmidt

/-!
# The actual Hilbert--Schmidt deficit for normalized convolution

The output score and second-ratio fields are identified before their
integrability is used. The genuine conditional covariance identity then
supplies the Hessian comparison. Log-concavity of the actual output
density supplies its negative-Hessian sign. The explicit squared
Hilbert--Schmidt energy and the conditional matrix deficit are those of
the separately proved matrix modules, as in Bizeul's Lemma 5
(DOI 10.5802/crmath.390).

The smooth output density and its true affine-image law are inputs to
this analytic convolution theorem. Neither a marginal Hessian identity,
a Loewner comparison nor output derivative integrability is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Matrix
open scoped Distributions ContDiff ENNReal MatrixOrder Matrix.Norms.L2Operator

theorem densityLogHessian_memLp_two_of_score_and_secondRatio (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hs : MemLp (gradient (fun x => Real.log (ρ x))) 4 μ)
    (hq : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ i j) 2 μ) :
    MemLp (densityLogHessian n ρ) 2 μ := by
  apply matrix_memLp_two_of_entries
  intro i j
  exact densityLogHessian_entry_memLp_of_secondRatio_and_score n ρ hρ hpos μ i j (hq i j) hs

theorem convolution_output_score_memLp_four (n : ℕ)
    (ρ₁ ρ₂ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ₁ : ContDiff ℝ ∞ ρ₁) (hpos₁ : ∀ x, 0 < ρ₁ x)
    (hρ₂ : ContDiff ℝ ∞ ρ₂) (hpos₂ : ∀ x, 0 < ρ₂ x)
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 4 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 4 (densityMeasure n ρ₂))
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (hlaw : ((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2) = densityMeasure n ρ) :
    MemLp (gradient (fun x => Real.log (ρ x))) 4 (densityMeasure n ρ) := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ := (densityMeasure n ρ₁).prod (densityMeasure n ρ₂)
  let W : E × E → E := fun p => a • p.1 + b • p.2
  have hW : Measurable W := by dsimp [W]; fun_prop
  obtain ⟨r, hr, _hr2, hrep, heq, _hs2, _hpull⟩ :=
    convolution_score_conditional_identification n ρ₁ ρ₂ ρ hρ₁ hpos₁ hρ₂ hpos₂ hρ hpos
      (hs₁.mono_exponent (by norm_num)) (hs₂.mono_exponent (by norm_num)) a b ha hb hab hlaw
  have hrep' (p : E × E) : r (W p) = (1 : ℝ) • condExp
      ((inferInstance : MeasurableSpace E).comap W) μ (convolutionScoreCombination n ρ₁ ρ₂ a b) p := by
    simpa only [one_smul] using hrep p
  have hr4 := (conditional_vector_field_memLp_four μ _
    (convolutionScoreCombination_memLp_four n ρ₁ ρ₂ hs₁ hs₂ a b) W hW 1 r hr hrep').1
  have hrρ : MemLp r 4 (densityMeasure n ρ) := by rw [← hlaw]; exact hr4
  exact hrρ.ae_eq heq

theorem convolution_output_hessian_memLp_two (n : ℕ)
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
    MemLp (densityLogHessian n ρ) 2 (densityMeasure n ρ) := by
  obtain ⟨q, _hq, _hq2, _hrep, _heq, hQ2, _hpull⟩ :=
    convolution_second_ratio_conditional_identification n ρ₁ ρ₂ ρ hρ₁ hpos₁ hρ₂ hpos₂ hρ hpos
      hs₁ hs₂ hq₁ hq₂ a b ha hb hab hlaw
  have hscore := convolution_output_score_memLp_four n ρ₁ ρ₂ ρ hρ₁ hpos₁ hρ₂ hpos₂ hρ hpos hs₁ hs₂ a b ha hb hab hlaw
  apply densityLogHessian_memLp_two_of_score_and_secondRatio n ρ hρ hpos _ hscore
  intro i j
  exact (matrixEntryContinuousLinear n i j).comp_memLp' hQ2

theorem convolution_hessian_hilbertSchmidt_deficit (n : ℕ)
    (ρ₁ ρ₂ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ₁ : ContDiff ℝ ∞ ρ₁) (hpos₁ : ∀ x, 0 < ρ₁ x)
    (hρ₂ : ContDiff ℝ ∞ ρ₂) (hpos₂ : ∀ x, 0 < ρ₂ x)
    (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (ρ x)))
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 4 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 4 (densityMeasure n ρ₂))
    (hq₁ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₁ i j) 2 (densityMeasure n ρ₁))
    (hq₂ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₂ i j) 2 (densityMeasure n ρ₂))
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (hlaw : ((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + b • p.2) = densityMeasure n ρ) :
    let μ := (densityMeasure n ρ₁).prod (densityMeasure n ρ₂)
    a ^ 2 * (∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ₁ x) ∂densityMeasure n ρ₁) +
      b ^ 2 * (∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ₂ x) ∂densityMeasure n ρ₂) -
      (∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ x) ∂densityMeasure n ρ) ≥
      a ^ 2 * b ^ 2 * ∫ p, matrixHilbertSchmidtSq
        (densityLogHessian n ρ₁ p.1 - densityLogHessian n ρ₂ p.2) ∂μ := by
  let E := EuclideanSpace ℝ (Fin n)
  let mΩ : MeasurableSpace (E × E) := inferInstance
  let ν := densityMeasure n ρ₁
  let η := densityMeasure n ρ₂
  let μ := ν.prod η
  let W : E × E → E := fun p => a • p.1 + b • p.2
  let m := (inferInstance : MeasurableSpace E).comap W
  let : MeasurableSpace (E × E) := mΩ
  let A : E × E → Matrix (Fin n) (Fin n) ℝ := fun p => -densityLogHessian n ρ₁ p.1
  let B : E × E → Matrix (Fin n) (Fin n) ℝ := fun p => -densityLogHessian n ρ₂ p.2
  let C : E × E → Matrix (Fin n) (Fin n) ℝ := fun p => -densityLogHessian n ρ (W p)
  let H := convolutionHessianCombination n ρ₁ ρ₂ a b
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hH₁ := densityLogHessian_memLp_two_of_score_and_secondRatio n ρ₁ hρ₁ hpos₁ ν hs₁ hq₁
  have hH₂ := densityLogHessian_memLp_two_of_score_and_secondRatio n ρ₂ hρ₂ hpos₂ η hs₂ hq₂
  have hHout := convolution_output_hessian_memLp_two n ρ₁ ρ₂ ρ hρ₁ hpos₁ hρ₂ hpos₂ hρ hpos
    hs₁ hs₂ hq₁ hq₂ a b ha hb hab hlaw
  have hA : MemLp A 2 μ := (hH₁.comp_fst η).neg
  have hB : MemLp B 2 μ := (hH₂.comp_snd ν).neg
  have hHmap : MemLp (densityLogHessian n ρ) 2 (μ.map W) := by rw [hlaw]; exact hHout
  have hC : MemLp C 2 μ :=
    ((memLp_map_measure_iff hHmap.aestronglyMeasurable hW.aemeasurable).mp hHmap).neg
  have hposC : ∀ᵐ p ∂μ, (C p).PosSemidef := Filter.Eventually.of_forall fun p =>
    logConcaveDensity_densityLogHessian_neg_posSemidef n ρ hρ hpos hlc (W p)
  have hweights : 1 - b ^ 2 = a ^ 2 := by linarith
  have hmix : (fun p => (1 - b ^ 2) • A p + b ^ 2 • B p) = -H := by
    funext p
    ext i j
    change (1 - b ^ 2) * (-densityLogHessian n ρ₁ p.1 i j) + b ^ 2 * (-densityLogHessian n ρ₂ p.2 i j) =
      -(a ^ 2 * densityLogHessian n ρ₁ p.1 i j + b ^ 2 * densityLogHessian n ρ₂ p.2 i j)
    rw [hweights]
    ring
  have hcomparison := convolution_hessian_conditional_comparison n ρ₁ ρ₂ ρ hρ₁ hpos₁ hρ₂ hpos₂ hρ hpos
    hs₁ hs₂ hq₁ hq₂ a b ha hb hab hlaw
  have hCEneg := condExp_neg (μ := μ) H m
  have hcomp : ∀ᵐ p ∂μ,
      (condExp m μ (fun z => (1 - b ^ 2) • A z + b ^ 2 • B z) p - C p).PosSemidef := by
    rw [hmix]
    filter_upwards [hcomparison, hCEneg] with p hp hn
    change (densityLogHessian n ρ (W p) - condExp m μ H p).PosSemidef at hp
    change condExp m μ (-H) p = -condExp m μ H p at hn
    rw [hn]
    change (-condExp m μ H p - (-densityLogHessian n ρ (W p))).PosSemidef
    have heq : -condExp m μ H p - (-densityLogHessian n ρ (W p)) =
        densityLogHessian n ρ (W p) - condExp m μ H p := by abel
    rw [heq]
    exact hp
  have hdef := conditional_matrix_hilbertSchmidt_deficit μ m hW.comap_le n A B C hA hB hC (b ^ 2) hposC hcomp
  have hneg (M : Matrix (Fin n) (Fin n) ℝ) : matrixHilbertSchmidtSq (-M) = matrixHilbertSchmidtSq M := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (-M i j) ^ 2 = (M i j) ^ 2
    exact neg_sq _
  have hdiff (p : E × E) : matrixHilbertSchmidtSq (A p - B p) =
      matrixHilbertSchmidtSq (densityLogHessian n ρ₁ p.1 - densityLogHessian n ρ₂ p.2) := by
    have heq : A p - B p = -(densityLogHessian n ρ₁ p.1 - densityLogHessian n ρ₂ p.2) := by
      dsimp only [A, B]
      abel
    rw [heq, hneg]
  have hAi : (∫ p, matrixHilbertSchmidtSq (A p) ∂μ) =
      ∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ₁ x) ∂ν := by
    simp only [A, hneg]
    simpa only [probReal_univ, one_smul] using
      integral_fun_fst (μ := ν) (ν := η) (fun x => matrixHilbertSchmidtSq (densityLogHessian n ρ₁ x))
  have hBi : (∫ p, matrixHilbertSchmidtSq (B p) ∂μ) =
      ∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ₂ x) ∂η := by
    simp only [B, hneg]
    simpa only [probReal_univ, one_smul] using
      integral_fun_snd (μ := ν) (ν := η) (fun x => matrixHilbertSchmidtSq (densityLogHessian n ρ₂ x))
  have hCi : (∫ p, matrixHilbertSchmidtSq (C p) ∂μ) =
      ∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ x) ∂densityMeasure n ρ := by
    simp only [C, hneg]
    rw [← hlaw]
    exact (integral_map hW.aemeasurable
      (matrix_hilbertSchmidt_integrable_of_memLp (μ.map W) n _ hHmap).aestronglyMeasurable).symm
  rw [hweights, hAi, hBi, hCi] at hdef
  simp_rw [hdiff] at hdef
  convert! hdef using 1
  all_goals ring

end AffineFKProof
