module

public import AffineFK.DirichletRellichGraph
public import AffineFK.BenensonRellich.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich

/-!
# Genuine compactness of the Dirichlet value map on bounded open sets

The supported-space compactness theorem is Adam Benenson's attributed
Rellich proof. Compact tests supported in U have their actual L2 values in
the closed range of extension by zero from any compact K containing U.
Closure preserves this support property. The previous graph identification
then transfers the compact operator to our genuine H0^1(U) value map.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

theorem dirichletRellich_test_supported (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKm : MeasurableSet K)
    (hUK : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ K) (φ : 𝓓(U, ℝ)) :
    unweightedValue n (dirichletTestToH1 n U φ) ∈
      (Lp.extendByZeroₗᵢ (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (E := ℝ) (p := 2) hKm).toLinearMap.range := by
  let hφK : MemLp φ 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  let f := hφK.toLp φ
  refine ⟨f, ?_⟩
  apply Lp.ext
  have hright := unweightedTestToL2_coe n (dirichletTestToTop n U φ)
  have hleft := Lp.extendByZeroₗᵢ_ae_eq (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hKm f
  have hlocal := (ae_restrict_iff' hKm).mp hφK.coeFn_toLp
  filter_upwards [hleft, hright, hlocal] with x hx hy hz
  change ((Lp.extendByZeroₗᵢ (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (E := ℝ) (p := 2) hKm) f) x =
      (unweightedTestToL2 n (dirichletTestToTop n U φ)) x
  rw [hx, hy]
  by_cases hxK : x ∈ K
  · simpa only [Set.indicator_of_mem hxK, f, dirichletTestToTop_apply] using! hz hxK
  · rw [Set.indicator_of_notMem hxK]
    symm
    apply image_eq_zero_of_notMem_tsupport
    intro hxSupp
    exact hxK (hUK (φ.tsupport_subset hxSupp))

theorem dirichletRellich_value_supported (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKm : MeasurableSet K)
    (hUK : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ K) (v : dirichletSobolev n U) :
    dirichletValue n U v ∈
      (Lp.extendByZeroₗᵢ (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (E := ℝ) (p := 2) hKm).toLinearMap.range := by
  let e := Lp.extendByZeroₗᵢ (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (E := ℝ) (p := 2) hKm
  have hclosed : IsClosed ((unweightedValue n) ⁻¹'
      (e.toLinearMap.range : Set _)) := by
    exact (isClosed_range_extendByZero K hKm).preimage (unweightedValue n).continuous
  apply closure_minimal _ hclosed v.property
  rintro _ ⟨φ, rfl⟩
  exact dirichletRellich_test_supported n U K hKm hUK φ

def dirichletRellichOn (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKm : MeasurableSet K)
    (hUK : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ K) :
    dirichletSobolev n U →L[ℝ] h1On K hKm :=
  ((dirichletRellichGraph n).comp (dirichletSobolev n U).subtypeL).codRestrict _
    (dirichletRellich_value_supported n U K hKm hUK)

theorem dirichletValue_isCompact_of_compact_container (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hUK : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ K) :
    IsCompactOperator (dirichletValue n U) := by
  have h := (isCompactOperator_h1OnToL2 hK hK.measurableSet).comp_clm
    (dirichletRellichOn n U K hK.measurableSet hUK)
  exact h

theorem dirichletValue_isCompact_of_bounded (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n)))) :
    IsCompactOperator (dirichletValue n U) :=
  dirichletValue_isCompact_of_compact_container n U _ hU.isCompact_closure subset_closure

end AffineFKProof
