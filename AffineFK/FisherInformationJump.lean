module

public import AffineFK.OUInformationJump
public import AffineFK.NormalizedConvolutionDensity
public import AffineFK.OUFisherRelativeEndpoint

/-!
# Canonical Sobolev Fisher information jump for normalized copies

The positive-time jump and actual original-law OU contraction give a
uniform output bound. The proved density-L1/square-root-H1 endpoint closure
passes that bound to the original normalized convolution law. Its absolute
continuity is derived from the genuine convolution/Jacobian density law.
No initial smoothness, log-score premise or lower-semicontinuity axiom is
introduced. The extended inequality also includes infinite input Fisher
information by its actual extended-real meaning.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem normalized_copies_finite_information_jump (n : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂densityMeasure n f) = 0)
    (hcov : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂densityMeasure n f) =
      if i = j then (1 : ℝ) else 0)
    (P : ℝ≥0) (hP : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞))
    (hI : relativeFisherMeasure n (densityMeasure n f) ≠ (∞ : ℝ≥0∞)) :
    let ν := densityMeasure n f
    let a := (Real.sqrt 2)⁻¹
    let ξ := (ν.prod ν).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + a • p.2)
    relativeFisherMeasure n ξ ≠ (∞ : ℝ≥0∞) ∧
      relativeFisherMeasure n ξ ≤ ENNReal.ofReal
        ((1 - 1 / (8 * (P : ℝ))) * (relativeFisherMeasure n ν).toReal) ∧
      (relativeFisherMeasure n ν).toReal - (relativeFisherMeasure n ξ).toReal ≥
        (relativeFisherMeasure n ν).toReal / (8 * (P : ℝ)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let ν := densityMeasure n f
  let a : ℝ := (Real.sqrt 2)⁻¹
  let W : E × E → E := fun p => a • p.1 + a • p.2
  have hW : Measurable W := by dsimp [W]; fun_prop
  let ξ := (ν.prod ν).map W
  let : IsProbabilityMeasure ξ := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  have haSq : a ^ 2 = (1 / 2 : ℝ) := by
    dsimp only [a]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hab : a ^ 2 + a ^ 2 = 1 := by rw [haSq]; norm_num
  have hξ := normalizedConvolution_isotropy n ν ν hmean hmean hcov hcov a a hab
  have hmeanξ : ∀ i : Fin n, (∫ x : E, x i ∂ξ) = 0 := hξ.2.1
  have hcovξ : ∀ i j : Fin n, (∫ x : E, x i * x j ∂ξ) = if i = j then (1 : ℝ) else 0 := hξ.2.2
  have hac : ξ ≪ volume := normalized_copies_absolutelyContinuous n f hf a ha.ne'
  have hPone : (1 : ℝ) ≤ (P : ℝ) := isotropic_poincare_bound_ge_one n hn ν hmean hcov P hP
  have hq : 0 ≤ 1 - 1 / (8 * (P : ℝ)) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < 8 * (P : ℝ))).mpr
    linarith
  let q : ℝ := 1 - 1 / (8 * (P : ℝ))
  let M : ℝ := q * (relativeFisherMeasure n ν).toReal
  have hM : 0 ≤ M := mul_nonneg hq ENNReal.toReal_nonneg
  have hbound (t : ℝ) (ht : 0 < t) : relativeFisherMeasure n (ouInitialLaw n ξ t) ≤ ENNReal.ofReal M := by
    have hj := ou_normalized_copies_information_jump n hn f hf hlc hmean hcov P hP t ht
    have hc := fisherMeasure_OU_contraction n ν hI t ht.le
    have hval : (relativeFisherMeasure n (ouInitialLaw n ν t)).toReal ≤ (relativeFisherMeasure n ν).toReal := by
      have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc.2
      have hn0 : 0 ≤ Real.exp (-2 * t) * (relativeFisherMeasure n ν).toReal :=
        mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
      rw [ENNReal.toReal_ofReal hn0] at hmono
      have he : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hmul := mul_le_mul_of_nonneg_right he (show 0 ≤ (relativeFisherMeasure n ν).toReal from ENNReal.toReal_nonneg)
      simpa only [one_mul] using hmono.trans hmul
    have hout : (relativeFisherMeasure n (ouInitialLaw n ξ t)).toReal ≤ M :=
      hj.2.2.trans (mul_le_mul_of_nonneg_left hval hq)
    calc
      _ = ENNReal.ofReal (relativeFisherMeasure n (ouInitialLaw n ξ t)).toReal := (ENNReal.ofReal_toReal hj.2.1).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hout
  have hout := ou_relativeFisher_initial_le_of_positive_bound n ξ hac hmeanξ hcovξ M hM hbound
  have hfin : relativeFisherMeasure n ξ ≠ (∞ : ℝ≥0∞) := by
    intro htop
    rw [htop] at hout
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hout)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hout
  rw [ENNReal.toReal_ofReal hM] at hreal
  refine ⟨hfin, hout, ?_⟩
  change (relativeFisherMeasure n ν).toReal - (relativeFisherMeasure n ξ).toReal ≥
    (relativeFisherMeasure n ν).toReal / (8 * (P : ℝ))
  dsimp only [M, q] at hreal
  have heq : (1 - 1 / (8 * (P : ℝ))) * (relativeFisherMeasure n ν).toReal =
      (relativeFisherMeasure n ν).toReal - (relativeFisherMeasure n ν).toReal / (8 * (P : ℝ)) := by ring
  rw [heq] at hreal
  linarith

theorem normalized_copies_information_contraction (n : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂densityMeasure n f) = 0)
    (hcov : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂densityMeasure n f) =
      if i = j then (1 : ℝ) else 0)
    (P : ℝ≥0) (hP : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞)) :
    let ν := densityMeasure n f
    let a := (Real.sqrt 2)⁻¹
    relativeFisherMeasure n ((ν.prod ν).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + a • p.2)) ≤
      ENNReal.ofReal (1 - 1 / (8 * (P : ℝ))) * relativeFisherMeasure n ν := by
  classical
  let ν := densityMeasure n f
  have hPone := isotropic_poincare_bound_ge_one n hn ν hmean hcov P hP
  have hq : 0 < 1 - 1 / (8 * (P : ℝ)) := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < 8 * (P : ℝ))).mpr
    linarith
  by_cases hI : relativeFisherMeasure n ν = (∞ : ℝ≥0∞)
  · dsimp only
    rw [hI, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hq))]
    exact le_top
  · have h := (normalized_copies_finite_information_jump n hn f hf hlc hmean hcov P hP hI).2.1
    rw [ENNReal.ofReal_mul hq.le, ENNReal.ofReal_toReal hI] at h
    exact h

end AffineFKProof
