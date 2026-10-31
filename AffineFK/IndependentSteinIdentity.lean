module

public import AffineFK.ProductSteinIdentity
public import Mathlib.Probability.HasLaw

/-!
# The affine Stein identity for an independent second input

The actual joint law is the product law. Mathlib's HasLaw change of variables
transports the proved product integrability and each actual Bochner integral.
No differential identity for the sum or conditional expectation is assumed.
This reuses Etienne Marion's HasLaw development and Mathlib independence.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem independent_affine_stein_component_identity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (ν η : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (U V : Ω → EuclideanSpace ℝ (Fin n)) (hU : HasLaw U ν μ) (hV : HasLaw V η μ)
    (hUV : IndepFun U V μ)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hidentity : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, x i * ψ x ∂ν) - (∫ x, partialTest n i ψ x ∂ν) =
        ∫ x, tensorPartialContraction n T i ψ x ∂ν)
    (r : ℝ) (hr : r ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun ω => U ω i * φ (r⁻¹ • (U ω + V ω))) μ ∧
    Integrable (fun ω => partialTest n i φ (r⁻¹ • (U ω + V ω))) μ ∧
    Integrable (fun ω => ∑ j : Fin n, ∑ k : Fin n,
      T (U ω) (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (U ω + V ω))) μ ∧
    (∫ ω, U ω i * φ (r⁻¹ • (U ω + V ω)) ∂μ) -
      r⁻¹ * (∫ ω, partialTest n i φ (r⁻¹ • (U ω + V ω)) ∂μ) =
      (r⁻¹ * r⁻¹) * (∫ ω, ∑ j : Fin n, ∑ k : Fin n,
        T (U ω) (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (U ω + V ω)) ∂μ) := by
  obtain ⟨ha, hb, hc, hi⟩ := product_affine_stein_component_identity n ν η T hT i hxi hidentity r hr φ
  have hpair : HasLaw (fun ω => (U ω, V ω)) (ν.prod η) μ := hUV.hasLaw_prod hU hV
  refine ⟨hpair.integrable_fun_comp ha, hpair.integrable_fun_comp hb,
    hpair.integrable_fun_comp hc, ?_⟩
  have hleft : (∫ ω, U ω i * φ (r⁻¹ • (U ω + V ω)) ∂μ) =
      ∫ p, p.1 i * φ (r⁻¹ • (p.1 + p.2)) ∂ν.prod η := by
    simpa only [Function.comp_def] using hpair.integral_comp ha.aestronglyMeasurable
  have hderiv : (∫ ω, partialTest n i φ (r⁻¹ • (U ω + V ω)) ∂μ) =
      ∫ p, partialTest n i φ (r⁻¹ • (p.1 + p.2)) ∂ν.prod η := by
    simpa only [Function.comp_def] using hpair.integral_comp hb.aestronglyMeasurable
  have hright : (∫ ω, ∑ j : Fin n, ∑ k : Fin n,
      T (U ω) (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (U ω + V ω)) ∂μ) =
      ∫ p, ∑ j : Fin n, ∑ k : Fin n,
        T p.1 (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • (p.1 + p.2)) ∂ν.prod η := by
    simpa only [Function.comp_def] using hpair.integral_comp hc.aestronglyMeasurable
  rw [hleft, hderiv, hright]
  exact hi

end AffineFKProof
