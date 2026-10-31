module

public import AffineFK.SteinIdentityComponents
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Uniqueness from compact smooth vector tests

A continuous candidate field need not be assumed globally square
integrable. Equality of its compact-test functional with an L2 field
identifies the fields almost everywhere and supplies that L2 membership.
The scalar distributional uniqueness theorem is due to Sebastien Gouezel
in Mathlib's AEEqOfIntegralContDiff development (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem singleComponentTest_inner_at
    (n : ℕ) (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (v x : EuclideanSpace ℝ (Fin n)) :
    ⟪v, singleComponentTest n i φ x⟫ = v i * φ x := by
  rw [singleComponentTest_apply, inner_smul_right, real_inner_comm, EuclideanSpace.basisFun_inner]
  exact mul_comm _ _

theorem vector_field_ae_eq_of_test_pairings
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (r s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : MemLp r 2 ν) (hs : Continuous s)
    (hpair : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪r x, F x⟫ ∂ν) = ∫ x, ⟪s x, F x⟫ ∂ν) :
    r =ᵐ[ν] s := by
  have hcoord (i : Fin n) : ∀ᵐ x ∂ν, r x i = s x i := by
    apply ae_eq_of_integral_contDiff_smul_eq
      ((hr.eval_piLp i).integrable (by norm_num)).locallyIntegrable
      (show Continuous (fun x => s x i) by fun_prop).locallyIntegrable
    intro ψ hψ hcompact
    let φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
      ⟨ψ, hψ, hcompact, Set.subset_univ _⟩
    have h := hpair (singleComponentTest n i φ)
    simp_rw [singleComponentTest_inner_at] at h
    change (∫ x, r x i * ψ x ∂ν) = ∫ x, s x i * ψ x ∂ν at h
    simpa only [smul_eq_mul, mul_comm] using h
  have hall : ∀ᵐ x ∂ν, ∀ i : Fin n, r x i = s x i := ae_all_iff.mpr hcoord
  filter_upwards [hall] with x hx
  ext i
  exact hx i

theorem continuous_vector_field_L2_of_test_pairings
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (r s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : MemLp r 2 ν) (hs : Continuous s)
    (hpair : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪r x, F x⟫ ∂ν) = ∫ x, ⟪s x, F x⟫ ∂ν) :
    r =ᵐ[ν] s ∧ MemLp s 2 ν ∧ (∫ x, ‖s x‖ ^ 2 ∂ν) = ∫ x, ‖r x‖ ^ 2 ∂ν := by
  have h := vector_field_ae_eq_of_test_pairings n ν r s hr hs hpair
  refine ⟨h, hr.ae_eq h, ?_⟩
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

end AffineFKProof
