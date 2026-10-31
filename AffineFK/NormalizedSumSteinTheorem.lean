module

public import AffineFK.NormalizedSumSteinTensor
public import AffineFK.SteinIdentityComponents

/-!
# Normalized sums from the manuscript's vector Stein identity

The original vector identity supplies the component identity through genuine
one-coordinate vector tests. The conditional field is constructed once and
works for every compact smooth vector test, with the exact coefficient and
energy bound in the manuscript.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem normalized_sum_stein_tensor_of_vector_identity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n m : ℕ) (hm : 0 < m) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (U : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (hU : ∀ ℓ, HasLaw (U ℓ) ν μ)
    (hUmeas : ∀ ℓ, Measurable (U ℓ)) (hind : iIndepFun U μ)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (hTmean : (∫ x, T x ∂ν) = 0)
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) = ∫ x, vectorHessianContraction n T F x ∂ν)
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
  exact normalized_sum_stein_tensor μ n m hm ν U hU hUmeas hind hcov T hT hTmean
    (vector_identity_implies_component_identity n ν (isotropic_coordinate_memLp n ν hcov) T hidentity) P hbound

end AffineFKProof
