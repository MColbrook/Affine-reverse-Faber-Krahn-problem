module

public import AffineFK.SumInputSteinIdentity
public import AffineFK.SteinSumLaw

/-!
# The raw differential Stein identity for a normalized sum

The individually justified input identities are summed and multiplied by the
outer inverse square root. The coefficient is exactly m^{-3/2}. This identity
is on the original probability space; the conditional tensor representation
under the sum's law is a subsequent step.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

def normalizedSum
    {Ω : Type*} (n m : ℕ) (U : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  (Real.sqrt (m : ℝ))⁻¹ • ∑ ℓ, U ℓ ω

theorem inverse_sqrt_square (m : ℕ) :
    (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ = (m : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg m)]

theorem normalized_sum_raw_stein_identity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n m : ℕ) (hm : 0 < m) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (U : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (hU : ∀ ℓ, HasLaw (U ℓ) ν μ)
    (hind : iIndepFun U μ)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hidentity : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, x i * ψ x ∂ν) - (∫ x, partialTest n i ψ x ∂ν) =
        ∫ x, tensorPartialContraction n T i ψ x ∂ν)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun ω => normalizedSum n m U ω i * φ (normalizedSum n m U ω)) μ ∧
    Integrable (fun ω => partialTest n i φ (normalizedSum n m U ω)) μ ∧
    Integrable (fun ω => ∑ ℓ : Fin m, ∑ j : Fin n, ∑ k : Fin n,
      T (U ℓ ω) (i, j, k) * partialTest n k (partialTest n j φ) (normalizedSum n m U ω)) μ ∧
    (∫ ω, normalizedSum n m U ω i * φ (normalizedSum n m U ω) ∂μ) -
      (∫ ω, partialTest n i φ (normalizedSum n m U ω) ∂μ) =
      (m : ℝ) ^ (-(3 : ℝ) / 2) * (∫ ω, ∑ ℓ : Fin m, ∑ j : Fin n, ∑ k : Fin n,
        T (U ℓ ω) (i, j, k) * partialTest n k (partialTest n j φ) (normalizedSum n m U ω) ∂μ) := by
  let a := (Real.sqrt (m : ℝ))⁻¹
  let W := normalizedSum n m U
  let A : Fin m → Ω → ℝ := fun ℓ ω => U ℓ ω i * φ (W ω)
  let D : Ω → ℝ := fun ω => partialTest n i φ (W ω)
  let C : Fin m → Ω → ℝ := fun ℓ ω => ∑ j : Fin n, ∑ k : Fin n,
    T (U ℓ ω) (i, j, k) * partialTest n k (partialTest n j φ) (W ω)
  have hr : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne'
  have hinput (ℓ : Fin m) : Integrable (A ℓ) μ ∧ Integrable D μ ∧ Integrable (C ℓ) μ ∧
      (∫ ω, A ℓ ω ∂μ) - a * (∫ ω, D ω ∂μ) = (a * a) * (∫ ω, C ℓ ω ∂μ) := by
    exact sum_input_stein_component_identity μ n m ν U hU hind T hT i hxi hidentity
      ℓ (Real.sqrt (m : ℝ)) hr φ
  have hA (ℓ : Fin m) := (hinput ℓ).1
  have hD := (hinput ⟨0, hm⟩).2.1
  have hC (ℓ : Fin m) := (hinput ℓ).2.2.1
  have hcoord (ω : Ω) : (∑ ℓ, U ℓ ω) i = ∑ ℓ, U ℓ ω i := by
    simpa only [coordinateFunctional_apply] using
      map_sum (coordinateFunctional n i) (fun ℓ : Fin m => U ℓ ω) Finset.univ
  have hpoint (ω : Ω) : W ω i * φ (W ω) = a * ∑ ℓ, A ℓ ω := by
    change (a • ∑ ℓ, U ℓ ω) i * φ (W ω) = a * ∑ ℓ, U ℓ ω i * φ (W ω)
    rw [PiLp.smul_apply, smul_eq_mul, hcoord, mul_assoc, Finset.sum_mul]
  have hfirst : Integrable (fun ω => W ω i * φ (W ω)) μ :=
    ((integrable_finsetSum Finset.univ (fun ℓ _hℓ => hA ℓ)).const_mul a).congr
      (Filter.Eventually.of_forall fun ω => (hpoint ω).symm)
  have hfirst_int : (∫ ω, W ω i * φ (W ω) ∂μ) = a * ∑ ℓ, ∫ ω, A ℓ ω ∂μ := by
    calc
      _ = ∫ ω, a * ∑ ℓ, A ℓ ω ∂μ := integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = _ := by rw [integral_const_mul, integral_finsetSum Finset.univ (fun ℓ _hℓ => hA ℓ)]
  have hCsum : Integrable (fun ω => ∑ ℓ, C ℓ ω) μ :=
    integrable_finsetSum Finset.univ (fun ℓ _hℓ => hC ℓ)
  have hsum : (∑ ℓ, ∫ ω, A ℓ ω ∂μ) - (m : ℝ) * (a * ∫ ω, D ω ∂μ) =
      (a * a) * (∑ ℓ, ∫ ω, C ℓ ω ∂μ) := by
    have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun ℓ _hℓ => (hinput ℓ).2.2.2)
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] using h
  have hnorm : (m : ℝ) * (a * a) = 1 := by
    change (m : ℝ) * ((Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹) = 1
    rw [inverse_sqrt_square]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))
  have hscale : a * (a * a) = (m : ℝ) ^ (-(3 : ℝ) / 2) := by
    change (Real.sqrt (m : ℝ))⁻¹ *
      ((Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹) = _
    rw [inverse_sqrt_square, neg_three_halves_eq_inv_sqrt m hm]
    exact mul_comm _ _
  refine ⟨hfirst, hD, hCsum, ?_⟩
  change (∫ ω, W ω i * φ (W ω) ∂μ) - (∫ ω, D ω ∂μ) =
    (m : ℝ) ^ (-(3 : ℝ) / 2) * (∫ ω, ∑ ℓ, C ℓ ω ∂μ)
  rw [hfirst_int, integral_finsetSum Finset.univ (fun ℓ _hℓ => hC ℓ)]
  calc
    _ = a * (∑ ℓ, ∫ ω, A ℓ ω ∂μ) - ((m : ℝ) * (a * a)) * (∫ ω, D ω ∂μ) := by rw [hnorm, one_mul]
    _ = a * ((∑ ℓ, ∫ ω, A ℓ ω ∂μ) - (m : ℝ) * (a * ∫ ω, D ω ∂μ)) := by ring
    _ = a * ((a * a) * (∑ ℓ, ∫ ω, C ℓ ω ∂μ)) := congrArg (fun x : ℝ => a * x) hsum
    _ = _ := by rw [← mul_assoc, hscale]

end AffineFKProof
