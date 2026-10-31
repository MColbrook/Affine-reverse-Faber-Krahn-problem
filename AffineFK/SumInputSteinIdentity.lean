module

public import AffineFK.IndependentSteinIdentity

/-!
# Applying the Stein identity to one summand

Independence makes each input independent of the actual sum of the remaining
inputs. Its law is used as the translation law in the proved product identity.
The affine image is the full sum, not a freely supplied conditioning map.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem sum_input_stein_component_identity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n m : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (U : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (hU : ∀ ℓ, HasLaw (U ℓ) ν μ)
    (hind : iIndepFun U μ)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hidentity : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, x i * ψ x ∂ν) - (∫ x, partialTest n i ψ x ∂ν) =
        ∫ x, tensorPartialContraction n T i ψ x ∂ν)
    (ℓ : Fin m) (r : ℝ) (hr : r ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun ω => U ℓ ω i * φ (r⁻¹ • ∑ q, U q ω)) μ ∧
    Integrable (fun ω => partialTest n i φ (r⁻¹ • ∑ q, U q ω)) μ ∧
    Integrable (fun ω => ∑ j : Fin n, ∑ k : Fin n,
      T (U ℓ ω) (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • ∑ q, U q ω)) μ ∧
    (∫ ω, U ℓ ω i * φ (r⁻¹ • ∑ q, U q ω) ∂μ) -
      r⁻¹ * (∫ ω, partialTest n i φ (r⁻¹ • ∑ q, U q ω) ∂μ) =
      (r⁻¹ * r⁻¹) * (∫ ω, ∑ j : Fin n, ∑ k : Fin n,
        T (U ℓ ω) (i, j, k) * partialTest n k (partialTest n j φ) (r⁻¹ • ∑ q, U q ω) ∂μ) := by
  let V : Ω → EuclideanSpace ℝ (Fin n) := fun ω => ∑ q ∈ Finset.univ.erase ℓ, U q ω
  have hV : AEMeasurable V μ :=
    (Finset.univ.erase ℓ).aemeasurable_fun_sum (fun q _hq => (hU q).aemeasurable)
  let η := μ.map V
  have hVlaw : HasLaw V η μ := hasLaw_map hV
  let : IsProbabilityMeasure η := hVlaw.isProbabilityMeasure_iff.mp inferInstance
  have hUV : IndepFun (U ℓ) V μ := by
    have h := (hind.indepFun_finsetSum_of_notMem₀ (fun q => (hU q).aemeasurable)
      (s := Finset.univ.erase ℓ) (i := ℓ) (by simp)).symm
    have heq : (∑ q ∈ Finset.univ.erase ℓ, U q) = V := by
      funext ω
      simp only [Finset.sum_apply, V]
    rw [heq] at h
    exact h
  have hsplit (ω : Ω) : U ℓ ω + V ω = ∑ q, U q ω :=
    Finset.add_sum_erase Finset.univ (fun q => U q ω) (Finset.mem_univ ℓ)
  have h := independent_affine_stein_component_identity μ n ν η (U ℓ) V (hU ℓ) hVlaw hUV
    T hT i hxi hidentity r hr φ
  simpa only [hsplit] using h

end AffineFKProof
