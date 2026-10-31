module

public import AffineFK.DyadicInformationDecay
public import AffineFK.FisherInformationMeasureHSI
public import AffineFK.VectorSteinIdentity
public import AffineFK.NormalizedSumSteinTheorem

/-!
# Second-order Stein entropy decay for actual dyadic sums

The original even probability law supplies its Stein tensor by the proved
Poisson construction. The actual normalized-sum theorem supplies a single
tensor with energy P(P-1)n/m², and the numerical measure HSI inequality
combines this with the derived information decay.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace
open scoped ENNReal NNReal Distributions RealInnerProductSpace

theorem dyadic_entropy_rate_coefficient (P I : ℝ) (hP : 2 ≤ P)
    (n r : ℕ) :
    Real.sqrt 2 * Real.sqrt (P * (P - 1) * (n : ℝ) / (((2 ^ r : ℕ) : ℝ) ^ 2)) *
        Real.sqrt ((1 - 1 / (8 * P)) ^ r * I) =
      Real.sqrt (2 * P * (P - 1) * (n : ℝ) * I) *
        (((2 ^ r : ℕ) : ℝ) ^ (-1 - (-Real.log (1 - 1 / (8 * P)) / Real.log 2) / 2)) := by
  let m : ℝ := ((2 ^ r : ℕ) : ℝ)
  let δ : ℝ := -Real.log (1 - 1 / (8 * P)) / Real.log 2
  have hm : 0 < m := Nat.cast_pos.mpr (pow_pos (by norm_num) _)
  have hP0 : 0 ≤ P := by linarith
  have hP1 : 0 ≤ P - 1 := by linarith
  have hB : 0 ≤ P * (P - 1) * (n : ℝ) := by positivity
  have hq : 0 ≤ (1 - 1 / (8 * P)) ^ r := by
    have h := (information_jump_ratio_bounds P hP).1
    exact pow_nonneg (by linarith) _
  have hdecay : (1 - 1 / (8 * P)) ^ r = m ^ (-δ) := by
    simpa only [m, δ, Nat.cast_pow, Nat.cast_ofNat] using information_decay_dyadic_identity P hP r
  have hsqrt : Real.sqrt ((1 - 1 / (8 * P)) ^ r) = m ^ (-δ / 2) := by
    rw [hdecay, Real.sqrt_eq_rpow, ← Real.rpow_mul hm.le]
    congr 1
    ring
  have hscale : m⁻¹ * m ^ (-δ / 2) = m ^ (-1 - δ / 2) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hm]
    congr 1
    ring
  change Real.sqrt 2 * Real.sqrt (P * (P - 1) * (n : ℝ) / m ^ 2) *
      Real.sqrt ((1 - 1 / (8 * P)) ^ r * I) =
    Real.sqrt (2 * P * (P - 1) * (n : ℝ) * I) * m ^ (-1 - δ / 2)
  rw [Real.sqrt_div hB, Real.sqrt_sq hm.le, Real.sqrt_mul hq, hsqrt]
  have hconst : Real.sqrt (2 * P * (P - 1) * (n : ℝ) * I) =
      Real.sqrt 2 * Real.sqrt (P * (P - 1) * (n : ℝ)) * Real.sqrt I := by
    rw [show 2 * P * (P - 1) * (n : ℝ) * I =
      2 * (P * (P - 1) * (n : ℝ)) * I by ring,
      Real.sqrt_mul (mul_nonneg (by norm_num) hB), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hconst, ← hscale]
  ring

theorem dyadic_normalized_sum_entropy_rate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n r : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)] [Measure.IsNegInvariant (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x, x i ∂densityMeasure n f) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂densityMeasure n f) =
      if i = j then 1 else 0)
    (P : ℝ≥0) (hP : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞))
    (hPtwo : (2 : ℝ) ≤ P)
    (hI : relativeFisherMeasure n (densityMeasure n f) ≠ ∞)
    (U : Fin (2 ^ r) → Ω → EuclideanSpace ℝ (Fin n))
    (hU : ∀ i, HasLaw (U i) (densityMeasure n f) μ)
    (hUmeas : ∀ i, Measurable (U i)) (hind : iIndepFun U μ) :
    klDiv (μ.map (normalizedSum n (2 ^ r) U)) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
    (klDiv (μ.map (normalizedSum n (2 ^ r) U)) (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal ≤
      Real.sqrt (2 * (P : ℝ) * ((P : ℝ) - 1) * (n : ℝ) *
        (relativeFisherMeasure n (densityMeasure n f)).toReal) *
      (((2 ^ r : ℕ) : ℝ) ^
        (-1 - (-Real.log (1 - 1 / (8 * (P : ℝ))) / Real.log 2) / 2)) := by
  classical
  let ν := densityMeasure n f
  let ξ := μ.map (normalizedSum n (2 ^ r) U)
  let : IsProbabilityMeasure ξ := inferInstance
  obtain ⟨T, hT, _, hTmean, _, hTbound, hTidentity⟩ := second_stein_exists_odd_tensor n ν
    P P.coe_nonneg (admissiblePoincareConstant_of_poincareConstant_le n ν P hP) hmean hcov
  obtain ⟨Tm, _, hTm, _, hTmbound, _, hTmidentity⟩ := normalized_sum_stein_tensor_of_vector_identity
    μ n (2 ^ r) (pow_pos (by norm_num) _) ν U hU hUmeas hind hcov T hT hTmean
    (fun F => (hTidentity F).2.2) P hTbound
  have hdecay := dyadicNormalizedLaw_finite_information_decay n hn f hf hlc hmean hcov P hP hI r
  rw [dyadicNormalizedLaw_eq_normalizedSum μ n r ν U hU hind] at hdecay
  have hHSI := second_order_entropy_stein_information_measure n ξ hdecay.1 Tm hTm
    (fun F => (hTmidentity F).2.2)
  refine ⟨hHSI.1, ?_⟩
  have hR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hHSI.2
  rw [ENNReal.toReal_ofReal (by positivity)] at hR
  calc
    _ ≤ Real.sqrt 2 * Real.sqrt (∫ x, ‖Tm x‖ ^ 2 ∂ξ) *
        Real.sqrt (relativeFisherMeasure n ξ).toReal := hR
    _ ≤ Real.sqrt 2 * Real.sqrt ((P : ℝ) * ((P : ℝ) - 1) * (n : ℝ) /
          (((2 ^ r : ℕ) : ℝ) ^ 2)) *
        Real.sqrt ((1 - 1 / (8 * (P : ℝ))) ^ r *
          (relativeFisherMeasure n ν).toReal) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTmbound)
        (Real.sqrt_nonneg _)) (Real.sqrt_le_sqrt hdecay.2) (Real.sqrt_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := dyadic_entropy_rate_coefficient (P : ℝ) (relativeFisherMeasure n ν).toReal
      hPtwo n r

theorem dyadicNormalizedLaw_entropy_rate (n r : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)] [Measure.IsNegInvariant (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x, x i ∂densityMeasure n f) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂densityMeasure n f) =
      if i = j then 1 else 0)
    (P : ℝ≥0) (hP : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞))
    (hPtwo : (2 : ℝ) ≤ P)
    (hI : relativeFisherMeasure n (densityMeasure n f) ≠ ∞) :
    klDiv (dyadicNormalizedLaw n (densityMeasure n f) r)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
    (klDiv (dyadicNormalizedLaw n (densityMeasure n f) r)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal ≤
      Real.sqrt (2 * (P : ℝ) * ((P : ℝ) - 1) * (n : ℝ) *
        (relativeFisherMeasure n (densityMeasure n f)).toReal) *
      (((2 ^ r : ℕ) : ℝ) ^
        (-1 - (-Real.log (1 - 1 / (8 * (P : ℝ))) / Real.log 2) / 2)) := by
  let ν := densityMeasure n f
  let μ : Measure (Fin (2 ^ r) → EuclideanSpace ℝ (Fin n)) := Measure.pi (fun _ => ν)
  let U : Fin (2 ^ r) → (Fin (2 ^ r) → EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin n) := fun i ω => ω i
  have hU (i) : HasLaw (U i) ν μ := (measurePreserving_eval (fun _ : Fin (2 ^ r) => ν) i).hasLaw
  have hind : iIndepFun U μ := iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h := dyadic_normalized_sum_entropy_rate μ n r hn f hf hlc hmean hcov P hP hPtwo hI
    U hU (fun i => measurable_pi_apply i) hind
  rwa [← dyadicNormalizedLaw_eq_normalizedSum μ n r ν U hU hind] at h

end AffineFKProof
