module

public import AffineFK.OUConvolutionCommutation
public import AffineFK.NormalizedSumSteinIdentity

/-!
# Dyadic normalized sums as actual probability laws

The recursive law doubles the number of independent copies at each step.
Characteristic-function uniqueness identifies it with the normalized sum
of any genuine independent family having the original common law.
Mathlib's characteristic-function and independence proofs are due to
Etienne Marion and contributors, under Apache-2.0.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

def dyadicNormalizedLaw (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) :
    ℕ → Measure (EuclideanSpace ℝ (Fin n))
  | 0 => ν
  | r + 1 => ((dyadicNormalizedLaw n ν r).prod (dyadicNormalizedLaw n ν r)).map
      (fun p => (Real.sqrt 2)⁻¹ • p.1 + (Real.sqrt 2)⁻¹ • p.2)

instance dyadicNormalizedLaw_isProbabilityMeasure (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] (r : ℕ) :
    IsProbabilityMeasure (dyadicNormalizedLaw n ν r) := by
  induction r with
  | zero => exact inferInstanceAs (IsProbabilityMeasure ν)
  | succ r hr =>
    let : IsProbabilityMeasure (dyadicNormalizedLaw n ν r) := hr
    exact inferInstanceAs (IsProbabilityMeasure
      (((dyadicNormalizedLaw n ν r).prod (dyadicNormalizedLaw n ν r)).map
        (fun p => (Real.sqrt 2)⁻¹ • p.1 + (Real.sqrt 2)⁻¹ • p.2)))

theorem charFun_dyadicNormalizedLaw (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (r : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    charFun (dyadicNormalizedLaw n ν r) v =
      (charFun ν (((Real.sqrt 2)⁻¹ ^ r) • v)) ^ (2 ^ r) := by
  induction r generalizing v with
  | zero => simp [dyadicNormalizedLaw]
  | succ r hr =>
    rw [dyadicNormalizedLaw, charFun_affine_product, hr]
    simp only [smul_smul, ← pow_succ]
    rw [← pow_two, ← pow_mul, pow_succ 2]

theorem dyadic_inverse_sqrt_coefficient (r : ℕ) :
    (Real.sqrt ((2 ^ r : ℕ) : ℝ))⁻¹ = (Real.sqrt 2)⁻¹ ^ r := by
  have heq : Real.sqrt ((2 ^ r : ℕ) : ℝ) = Real.sqrt 2 ^ r := by
    apply (Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)).mpr
    symm
    rw [← pow_mul, mul_comm r 2, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_cast
  rw [heq, inv_pow]

theorem normalizedSum_charFun
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n m : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (U : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hU : ∀ i, HasLaw (U i) ν μ) (hind : iIndepFun U μ)
    (v : EuclideanSpace ℝ (Fin n)) :
    charFun (μ.map (normalizedSum n m U)) v =
      (charFun ν ((Real.sqrt (m : ℝ))⁻¹ • v)) ^ m := by
  change charFun (μ.map (fun ω => (Real.sqrt (m : ℝ))⁻¹ • ∑ i, U i ω)) v = _
  rw [charFun_map_smul_comp
    (Finset.univ.aemeasurable_fun_sum (fun i _ => (hU i).aemeasurable))]
  have h := congrFun (hind.charFun_map_fun_sum_eq_prod (fun i => (hU i).aemeasurable))
    ((Real.sqrt (m : ℝ))⁻¹ • v)
  rw [h]
  simp only [Finset.prod_apply, (hU _).map_eq]
  simp

theorem dyadicNormalizedLaw_eq_normalizedSum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n r : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (U : Fin (2 ^ r) → Ω → EuclideanSpace ℝ (Fin n))
    (hU : ∀ i, HasLaw (U i) ν μ) (hind : iIndepFun U μ) :
    dyadicNormalizedLaw n ν r = μ.map (normalizedSum n (2 ^ r) U) := by
  have hW : AEMeasurable (normalizedSum n (2 ^ r) U) μ := by
    exact (Finset.univ.aemeasurable_fun_sum (fun i _ => (hU i).aemeasurable)).const_smul
      ((Real.sqrt ((2 ^ r : ℕ) : ℝ))⁻¹)
  let : IsProbabilityMeasure (μ.map (normalizedSum n (2 ^ r) U)) :=
    (Measure.isProbabilityMeasure_map_iff hW).mpr inferInstance
  apply Measure.ext_of_charFun
  funext v
  rw [charFun_dyadicNormalizedLaw, normalizedSum_charFun μ n (2 ^ r) ν U hU hind v,
    dyadic_inverse_sqrt_coefficient]

end AffineFKProof
