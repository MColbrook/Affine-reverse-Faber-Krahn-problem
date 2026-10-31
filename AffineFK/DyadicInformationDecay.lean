module

public import AffineFK.DyadicNormalizedSumLaw
public import AffineFK.NormalizedConvolutionLogConcavity
public import AffineFK.FisherInformationJump
public import AffineFK.Exponents

/-!
# Information decay for actual dyadic normalized sums

Every intermediate density, its log-concavity, isotropy and Poincare bound
are derived for the recursive probability law. The information jump is
therefore applied to its original hypotheses at each step.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal Distributions RealInnerProductSpace

theorem dyadicNormalizedLaw_logConcave_density (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x))) (r : ℕ) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      Measurable g ∧ LogConcaveDensity (fun x => ENNReal.ofReal (g x)) ∧
      dyadicNormalizedLaw n (densityMeasure n f) r = densityMeasure n g := by
  induction r with
  | zero => exact ⟨f, hf, hlc, rfl⟩
  | succ r hr =>
    obtain ⟨g, hg, hglc, hglaw⟩ := hr
    let : IsProbabilityMeasure (densityMeasure n g) := by rw [← hglaw]; infer_instance
    obtain ⟨k, hk, _, hklc, hklaw⟩ := normalized_copies_logConcave_density n g hg hglc
      (Real.sqrt 2)⁻¹ (inv_ne_zero (Real.sqrt_pos.mpr (by norm_num)).ne')
    exact ⟨k, hk, hklc, by rw [dyadicNormalizedLaw, hglaw, hklaw]⟩

theorem dyadicNormalizedLaw_isotropy (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x, x i ∂ν) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0)
    (r : ℕ) :
    (∀ i : Fin n, (∫ x, x i ∂dyadicNormalizedLaw n ν r) = 0) ∧
    (∀ i j : Fin n, (∫ x, x i * x j ∂dyadicNormalizedLaw n ν r) =
      if i = j then 1 else 0) := by
  have ha : (Real.sqrt 2)⁻¹ ^ 2 + (Real.sqrt 2)⁻¹ ^ 2 = (1 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  induction r with
  | zero => exact ⟨hmean, hcov⟩
  | succ r hr =>
    exact (normalizedConvolution_isotropy n (dyadicNormalizedLaw n ν r)
      (dyadicNormalizedLaw n ν r) hr.1 hr.1 hr.2 hr.2 _ _ ha).2

theorem dyadicNormalizedLaw_poincare_le (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ≥0) (hP : poincareConstant n ν ≤ (P : ℝ≥0∞)) (r : ℕ) :
    poincareConstant n (dyadicNormalizedLaw n ν r) ≤ (P : ℝ≥0∞) := by
  have ha : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  induction r with
  | zero => exact hP
  | succ r hr =>
    apply poincareConstant_le_of_admissible n _ P
    intro φ
    have h := poincareConvolution_scaled n (dyadicNormalizedLaw n ν r)
      (dyadicNormalizedLaw n ν r) P P P.coe_nonneg P.coe_nonneg
      (admissiblePoincareConstant_of_poincareConstant_le n _ P hr)
      (admissiblePoincareConstant_of_poincareConstant_le n _ P hr)
      (Real.sqrt 2)⁻¹ (Real.sqrt 2)⁻¹ φ
    have hc : (Real.sqrt 2)⁻¹ ^ 2 * (P : ℝ) + (Real.sqrt 2)⁻¹ ^ 2 * (P : ℝ) = P := by
      rw [ha]; ring
    simpa only [dyadicNormalizedLaw, hc] using h

theorem dyadicNormalizedLaw_information_decay (n : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x, x i ∂densityMeasure n f) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂densityMeasure n f) =
      if i = j then 1 else 0)
    (P : ℝ≥0) (hP : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞)) (r : ℕ) :
    relativeFisherMeasure n (dyadicNormalizedLaw n (densityMeasure n f) r) ≤
      ENNReal.ofReal (1 - 1 / (8 * (P : ℝ))) ^ r * relativeFisherMeasure n (densityMeasure n f) := by
  induction r with
  | zero => simp only [dyadicNormalizedLaw, pow_zero, one_mul]; exact le_rfl
  | succ r hr =>
    obtain ⟨g, hg, hglc, hglaw⟩ := dyadicNormalizedLaw_logConcave_density n f hf hlc r
    let : IsProbabilityMeasure (densityMeasure n g) := by rw [← hglaw]; infer_instance
    have hi := dyadicNormalizedLaw_isotropy n (densityMeasure n f) hmean hcov r
    have hp := dyadicNormalizedLaw_poincare_le n (densityMeasure n f) P hP r
    rw [hglaw] at hi hp
    have hj := normalized_copies_information_contraction n hn g hg hglc hi.1 hi.2 P hp
    change relativeFisherMeasure n
      (((dyadicNormalizedLaw n (densityMeasure n f) r).prod
        (dyadicNormalizedLaw n (densityMeasure n f) r)).map _) ≤ _
    calc
      _ ≤ ENNReal.ofReal (1 - 1 / (8 * (P : ℝ))) *
          relativeFisherMeasure n (dyadicNormalizedLaw n (densityMeasure n f) r) := by
        simpa only [hglaw] using hj
      _ ≤ _ := by
        exact (mul_le_mul_of_nonneg_left hr zero_le).trans_eq (by rw [pow_succ', mul_assoc])

theorem dyadicNormalizedLaw_finite_information_decay (n : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x, x i ∂densityMeasure n f) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂densityMeasure n f) =
      if i = j then 1 else 0)
    (P : ℝ≥0) (hP : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞))
    (hI : relativeFisherMeasure n (densityMeasure n f) ≠ ∞) (r : ℕ) :
    relativeFisherMeasure n (dyadicNormalizedLaw n (densityMeasure n f) r) ≠ ∞ ∧
    (relativeFisherMeasure n (dyadicNormalizedLaw n (densityMeasure n f) r)).toReal ≤
      (1 - 1 / (8 * (P : ℝ))) ^ r * (relativeFisherMeasure n (densityMeasure n f)).toReal := by
  have hq : 0 ≤ 1 - 1 / (8 * (P : ℝ)) := by
    have hPone := isotropic_poincare_bound_ge_one n hn (densityMeasure n f) hmean hcov P hP
    have hp : (1 : ℝ) ≤ P := by exact_mod_cast hPone
    have hdiv : 1 / (8 * (P : ℝ)) ≤ 1 :=
      (div_le_iff₀ (by linarith : (0 : ℝ) < 8 * (P : ℝ))).mpr (by linarith)
    linarith
  have hb := dyadicNormalizedLaw_information_decay n hn f hf hlc hmean hcov P hP r
  have hright : ENNReal.ofReal (1 - 1 / (8 * (P : ℝ))) ^ r *
      relativeFisherMeasure n (densityMeasure n f) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hI
  refine ⟨ne_top_of_le_ne_top hright hb, ?_⟩
  have h := ENNReal.toReal_mono hright hb
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hq] using h

theorem dyadic_normalized_sum_information_decay
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n r : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x, x i ∂densityMeasure n f) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂densityMeasure n f) =
      if i = j then 1 else 0)
    (P : ℝ≥0) (hP : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞))
    (hPtwo : (2 : ℝ) ≤ P)
    (hI : relativeFisherMeasure n (densityMeasure n f) ≠ ∞)
    (U : Fin (2 ^ r) → Ω → EuclideanSpace ℝ (Fin n))
    (hU : ∀ i, HasLaw (U i) (densityMeasure n f) μ) (hind : iIndepFun U μ) :
    relativeFisherMeasure n (μ.map (normalizedSum n (2 ^ r) U)) ≠ ∞ ∧
    (relativeFisherMeasure n (μ.map (normalizedSum n (2 ^ r) U))).toReal ≤
      (((2 ^ r : ℕ) : ℝ) ^ (-(-Real.log (1 - 1 / (8 * (P : ℝ))) / Real.log 2))) *
        (relativeFisherMeasure n (densityMeasure n f)).toReal := by
  rw [← dyadicNormalizedLaw_eq_normalizedSum μ n r (densityMeasure n f) U hU hind]
  have h := dyadicNormalizedLaw_finite_information_decay n hn f hf hlc hmean hcov P hP hI r
  rw [information_decay_dyadic_identity (P : ℝ) hPtwo r] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

end AffineFKProof
