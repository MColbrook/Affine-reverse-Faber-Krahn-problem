module

public import AffineFK.NormalizedSumTensorBridge

/-!
# The second-order Stein tensor for normalized sums

The field is constructed by the already proved conditional factorization and
variance bound. The differential identity is then obtained from the original
Stein tensor, not assumed for the sum. The exact pointwise representation and
both forms of the Hilbert--Schmidt energy bound use the same field.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem normalized_sum_stein_tensor
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n m : ℕ) (hm : 0 < m) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (U : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (hU : ∀ ℓ, HasLaw (U ℓ) ν μ)
    (hUmeas : ∀ ℓ, Measurable (U ℓ)) (hind : iIndepFun U μ)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (hTmean : (∫ x, T x ∂ν) = 0)
    (hidentity : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν) =
        ∫ x, tensorPartialContraction n T i φ x ∂ν)
    (P : ℝ) (hbound : (∫ x, ‖T x‖ ^ 2 ∂ν) ≤ P * (P - 1) * (n : ℝ)) :
    ∃ Tm : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n),
      StronglyMeasurable Tm ∧ MemLp Tm 2 (μ.map (normalizedSum n m U)) ∧
      (∀ ω, Tm (normalizedSum n m U ω) = (m : ℝ) ^ (-(3 : ℝ) / 2) •
        condExp ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap (normalizedSum n m U)) μ
          (fun ω => ∑ ℓ, T (U ℓ ω)) ω) ∧
      (∫ z, ‖Tm z‖ ^ 2 ∂μ.map (normalizedSum n m U)) ≤ P * (P - 1) * (n : ℝ) / (m : ℝ) ^ 2 ∧
      (∫ ω, ‖Tm (normalizedSum n m U ω)‖ ^ 2 ∂μ) ≤ P * (P - 1) * (n : ℝ) / (m : ℝ) ^ 2 ∧
      (∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
        Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x) (μ.map (normalizedSum n m U)) ∧
        Integrable (vectorHessianContraction n Tm F) (μ.map (normalizedSum n m U)) ∧
        (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂μ.map (normalizedSum n m U)) =
          ∫ x, vectorHessianContraction n Tm F x ∂μ.map (normalizedSum n m U)) := by
  let W := normalizedSum n m U
  have hW : Measurable W := normalizedSum_measurable n m U hUmeas
  obtain ⟨Tm, hmeas, hLp, hrep, hsize⟩ := normalized_tensor_copies_law_second_moment μ ν m hm U hU hUmeas
    (fun _i _j hij => hind.indepFun hij) T hT hTmean (P * (P - 1) * (n : ℝ)) hbound
  have hrep' (ω : Ω) : Tm (W ω) = (m : ℝ) ^ (-(3 : ℝ) / 2) •
      condExp ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap W) μ
        (fun ω => ∑ ℓ, T (U ℓ ω)) ω := by
    rw [neg_three_halves_eq_inv_sqrt m hm]
    exact hrep ω
  have hvector := (normalized_sum_tensor_identity_of_representation μ n m hm ν U hU hUmeas hind T hT
    (isotropic_coordinate_memLp n ν hcov) hidentity Tm hLp hrep').2
  have hmoment : (∫ ω, ‖Tm (W ω)‖ ^ 2 ∂μ) = ∫ z, ‖Tm z‖ ^ 2 ∂μ.map W := by
    simpa only [Function.comp_def, Pi.pow_apply] using
      (hasLaw_map hW.aemeasurable).integral_comp (hmeas.aestronglyMeasurable.norm.pow 2)
  exact ⟨Tm, hmeas, hLp, hrep', hsize, hmoment.trans_le hsize, hvector⟩

end AffineFKProof
