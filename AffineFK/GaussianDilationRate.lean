module

public import AffineFK.DyadicEntropyRate
public import AffineFK.ProbabilitySupport
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The Gaussian dilation profile from the actual dyadic laws

The probability laws below are the true normalized sums of independent
copies. Their support follows from convexity, their entropy bound follows
from the constructed second-order Stein tensors and information jump,
and the passage to every dilation uses the largest dyadic integer below
the squared dilation parameter.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal Pointwise

theorem dyadicNormalizedLaw_support (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D) (hD : Convex ℝ D)
    (hsupp : ∀ᵐ x ∂ν, x ∈ D) (r : ℕ) :
    ∀ᵐ x ∂dyadicNormalizedLaw n ν r, x ∈ Real.sqrt (((2 ^ r : ℕ) : ℝ)) • D := by
  let μ : Measure (Fin (2 ^ r) → EuclideanSpace ℝ (Fin n)) := Measure.pi (fun _ => ν)
  let U : Fin (2 ^ r) → (Fin (2 ^ r) → EuclideanSpace ℝ (Fin n)) →
      EuclideanSpace ℝ (Fin n) := fun i ω => ω i
  have hU (i) : HasLaw (U i) ν μ := (measurePreserving_eval (fun _ : Fin (2 ^ r) => ν) i).hasLaw
  have hind : iIndepFun U μ := iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  rw [dyadicNormalizedLaw_eq_normalizedSum μ n r ν U hU hind]
  exact (normalized_sum_law_support μ D hcompact hD (2 ^ r) (pow_pos (by norm_num) _) U
    (fun i => (measurable_pi_apply i).aemeasurable)
    (fun i => (measurePreserving_eval (fun _ : Fin (2 ^ r) => ν) i).quasiMeasurePreserving.ae hsupp)).2

theorem gaussian_dyadic_support_entropy_rate (n r : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)] [Measure.IsNegInvariant (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x, x i ∂densityMeasure n f) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂densityMeasure n f) =
      if i = j then 1 else 0)
    (P : ℝ≥0) (hP : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞))
    (hPtwo : (2 : ℝ) ≤ P)
    (hI : relativeFisherMeasure n (densityMeasure n f) ≠ ∞)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D) (hD : Convex ℝ D)
    (hsupp : ∀ᵐ x ∂densityMeasure n f, x ∈ D) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) (Real.sqrt (((2 ^ r : ℕ) : ℝ)) • D) ≠ 0 ∧
    -Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))).real
      (Real.sqrt (((2 ^ r : ℕ) : ℝ)) • D)) ≤
      Real.sqrt (2 * (P : ℝ) * ((P : ℝ) - 1) * (n : ℝ) *
        (relativeFisherMeasure n (densityMeasure n f)).toReal) *
      (((2 ^ r : ℕ) : ℝ) ^
        (-1 - (-Real.log (1 - 1 / (8 * (P : ℝ))) / Real.log 2) / 2)) := by
  let ξ := dyadicNormalizedLaw n (densityMeasure n f) r
  have hentropy := dyadicNormalizedLaw_entropy_rate n r hn f hf hlc hmean hcov P hP hPtwo hI
  have hs := dyadicNormalizedLaw_support n (densityMeasure n f) D hcompact hD hsupp r
  have hm : MeasurableSet (Real.sqrt (((2 ^ r : ℕ) : ℝ)) • D) :=
    (hcompact.image (continuous_const_smul _)).measurableSet
  refine ⟨?_, (entropy_support_finite ξ (stdGaussian _) _ hm hs hentropy.1).trans hentropy.2⟩
  intro hzero
  exact hentropy.1 (entropy_support_null ξ (stdGaussian _) _ hm hs hzero)

theorem convex_dilate_mono (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n)))
    (hD : Convex ℝ D) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ D)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) : a • D ⊆ b • D := by
  rintro z ⟨x, hx, rfl⟩
  refine ⟨(a / b) • x, hD.smul_mem_of_zero_mem hzero hx
    ⟨div_nonneg ha hb.le, (div_le_one hb).mpr hab⟩, ?_⟩
  change b • ((a / b) • x) = a • x
  rw [smul_smul]
  congr 1
  field_simp

theorem dyadic_rounding_power_bound (p t : ℝ) (hp : 0 ≤ p) (ht : 1 ≤ t) :
    ∃ r : ℕ, (((2 ^ r : ℕ) : ℝ) ≤ t ^ 2) ∧
      (((2 ^ r : ℕ) : ℝ) ^ (-p / 2)) ≤ (2 : ℝ) ^ (p / 2) * t ^ (-p) := by
  obtain ⟨r, hr, hrnext⟩ := exists_nat_pow_near
    (show (1 : ℝ) ≤ t ^ 2 by nlinarith) (by norm_num : (1 : ℝ) < 2)
  have hm : 0 < (((2 ^ r : ℕ) : ℝ)) := Nat.cast_pos.mpr (pow_pos (by norm_num) _)
  have htpos : 0 < t := by linarith
  have hr' : (((2 ^ r : ℕ) : ℝ)) ≤ t ^ 2 := by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hr
  have hlow : t ^ 2 / 2 ≤ (((2 ^ r : ℕ) : ℝ)) := by
    have hnext : t ^ 2 < (((2 ^ r : ℕ) : ℝ)) * 2 := by
      simpa only [pow_succ, Nat.cast_pow, Nat.cast_ofNat] using hrnext
    linarith
  have hpowt : (t ^ 2) ^ (-p / 2) = t ^ (-p) := by
    rw [← Real.rpow_natCast_mul htpos.le]
    congr 1
    ring
  have hpowtwo : (2 : ℝ) ^ (-p / 2) = ((2 : ℝ) ^ (p / 2))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  refine ⟨r, hr', ?_⟩
  calc
    _ ≤ (t ^ 2 / 2) ^ (-p / 2) := Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
    _ = _ := by
      rw [Real.div_rpow (sq_nonneg t) (by norm_num : (0 : ℝ) ≤ 2),
        hpowt, hpowtwo, div_inv_eq_mul, mul_comm]

theorem zero_mem_convex_of_even_probability_support (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [Measure.IsNegInvariant ν]
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : Convex ℝ D)
    (hsupp : ∀ᵐ x ∂ν, x ∈ D) : (0 : EuclideanSpace ℝ (Fin n)) ∈ D := by
  have hneg : ∀ᵐ x ∂ν, -x ∈ D := (Measure.measurePreserving_neg ν).quasiMeasurePreserving.ae hsupp
  obtain ⟨x, hx, hnx⟩ := (hsupp.and hneg).exists
  have h := hD hx hnx (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simpa only [smul_neg, add_neg_cancel] using h

theorem gaussian_dilation_profile_of_finite_information (n : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)] [Measure.IsNegInvariant (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x, x i ∂densityMeasure n f) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂densityMeasure n f) =
      if i = j then 1 else 0)
    (P : ℝ≥0) (hP : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞))
    (hPtwo : (2 : ℝ) ≤ P)
    (hI : relativeFisherMeasure n (densityMeasure n f) ≠ ∞)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D) (hD : Convex ℝ D)
    (hsupp : ∀ᵐ x ∂densityMeasure n f, x ∈ D) :
    let δ := -Real.log (1 - 1 / (8 * (P : ℝ))) / Real.log 2
    let p := 2 + δ
    2 < p ∧ ∀ t : ℝ, 1 ≤ t →
      stdGaussian (EuclideanSpace ℝ (Fin n)) (t • D) ≠ 0 ∧
      -Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))).real (t • D)) ≤
        (2 : ℝ) ^ (p / 2) *
          Real.sqrt (2 * (P : ℝ) * ((P : ℝ) - 1) * (n : ℝ) *
            (relativeFisherMeasure n (densityMeasure n f)).toReal) * t ^ (-p) := by
  classical
  let δ := -Real.log (1 - 1 / (8 * (P : ℝ))) / Real.log 2
  let p := 2 + δ
  have hp : 2 < p := gaussian_dilation_exponent_gt_two (P : ℝ) hPtwo
  refine ⟨hp, ?_⟩
  intro t ht
  have htpos : 0 < t := by linarith
  obtain ⟨r, hlow, hround⟩ := dyadic_rounding_power_bound p t (by linarith) ht
  have hdyad := gaussian_dyadic_support_entropy_rate n r hn f hf hlc hmean hcov P hP hPtwo hI
    D hcompact hD hsupp
  have hzero := zero_mem_convex_of_even_probability_support n (densityMeasure n f) D hD hsupp
  have hsub : Real.sqrt (((2 ^ r : ℕ) : ℝ)) • D ⊆ t • D :=
    convex_dilate_mono n D hD hzero _ _ (Real.sqrt_nonneg _)
      (Real.sqrt_le_iff.mpr ⟨htpos.le, hlow⟩) htpos
  have hγ : stdGaussian (EuclideanSpace ℝ (Fin n)) (t • D) ≠ 0 := by
    intro h
    exact hdyad.1 (measure_mono_null hsub h)
  refine ⟨hγ, ?_⟩
  have hreal : 0 < (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      (Real.sqrt (((2 ^ r : ℕ) : ℝ)) • D) :=
    ENNReal.toReal_pos hdyad.1 (measure_ne_top _ _)
  have hexp : -1 - (-Real.log (1 - 1 / (8 * (P : ℝ))) / Real.log 2) / 2 = -p / 2 := by
    dsimp only [p, δ]
    ring
  rw [hexp] at hdyad
  calc
    _ ≤ -Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))).real
        (Real.sqrt (((2 ^ r : ℕ) : ℝ)) • D)) :=
      neg_le_neg (Real.log_le_log hreal (measureReal_mono hsub))
    _ ≤ _ := hdyad.2
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hround
        (Real.sqrt_nonneg (2 * (P : ℝ) * ((P : ℝ) - 1) * (n : ℝ) *
          (relativeFisherMeasure n (densityMeasure n f)).toReal))
      convert h using 1
      all_goals ring

end AffineFKProof
