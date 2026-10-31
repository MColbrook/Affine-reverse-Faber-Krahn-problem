module

public import AffineFK.DirichletSupportCompact
public import AffineFK.OrdinaryFisherLinearMapH1
public import Mathlib.Analysis.Convex.Topology

/-!
# Actual inward H1 dilations have zero boundary values on a convex open set

Convexity places a strict contraction of the compact closure inside the
open set. The genuine linear H1 transport has support there, so the
proved compact-support cutoff theorem supplies actual H0 membership.
Strong convergence of these inward dilations is a separate next step.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Set
open scoped RealInnerProductSpace Pointwise

theorem convex_inward_dilate_closure_subset (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set (EuclideanSpace ℝ (Fin n))))
    (a : ℝ) (ha : 0 ≤ a) (haone : a < 1) :
    a • closure (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ (U : Set (EuclideanSpace ℝ (Fin n))) := by
  rintro x ⟨y, hy, rfl⟩
  have hzero' : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior (U : Set (EuclideanSpace ℝ (Fin n))) := by
    rwa [U.isOpen.interior_eq]
  have h := hconv.combo_closure_interior_mem_interior hy hzero' ha
    (sub_pos.mpr haone) (show a + (1 - a) = 1 by ring)
  simpa only [smul_zero, add_zero, U.isOpen.interior_eq] using h

theorem unweighted_linear_graph_supported (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (K : Set (EuclideanSpace ℝ (Fin n))) (v : unweightedSobolevGraph n)
    (hsupp : ∀ᵐ x ∂volume, x ∉ K → unweightedValue n v x = 0) :
    ∃ w : unweightedSobolevGraph n,
      ((unweightedValue n w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        fun z => Real.sqrt (ordinaryFisherLinearJacobian n A) * unweightedValue n v (A.symm z)) ∧
      ((unweightedGradient n w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
        fun z => Real.sqrt (ordinaryFisherLinearJacobian n A) •
          A.symm.toContinuousLinearMap.adjoint (unweightedGradient n v (A.symm z))) ∧
      (∀ᵐ z ∂volume, z ∉ A '' K → unweightedValue n w z = 0) := by
  obtain ⟨w, hwv, hwg⟩ := ordinaryFisher_linear_graph_representatives n A v
  refine ⟨w, hwv, hwg, ?_⟩
  have hA := ordinaryFisherLinearMap_quasiMeasurePreserving n A.symm
  filter_upwards [hwv, hA.ae hsupp] with z hz hs
  intro hzK
  have hinv : A.symm z ∉ K := by
    intro hx
    exact hzK ⟨A.symm z, hx, A.apply_symm_apply z⟩
  rw [hz, hs hinv, mul_zero]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem unweighted_inward_dilation_mem_dirichlet (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))))
    (v : unweightedSobolevGraph n)
    (hsupp : ∀ᵐ x ∂volume, x ∉ closure (U : Set (EuclideanSpace ℝ (Fin n))) → unweightedValue n v x = 0)
    (a : ℝ) (ha : 0 < a) (haone : a < 1) :
    let A := (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) a ha.ne').toContinuousLinearEquiv
    ∃ w : dirichletSobolev n U,
      ((dirichletValue n U w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        fun z => Real.sqrt (ordinaryFisherLinearJacobian n A) * unweightedValue n v (A.symm z)) ∧
      ((dirichletGradient n U w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
        fun z => Real.sqrt (ordinaryFisherLinearJacobian n A) •
          A.symm.toContinuousLinearMap.adjoint (unweightedGradient n v (A.symm z))) := by
  let A := (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) a ha.ne').toContinuousLinearEquiv
  obtain ⟨w, hwv, hwg, hwsupp⟩ := unweighted_linear_graph_supported n A
    (closure (U : Set (EuclideanSpace ℝ (Fin n)))) v hsupp
  have hcompact : IsCompact (A '' closure (U : Set (EuclideanSpace ℝ (Fin n)))) :=
    hbounded.isCompact_closure.image A.continuous
  have hsub : A '' closure (U : Set (EuclideanSpace ℝ (Fin n))) ⊆
      (U : Set (EuclideanSpace ℝ (Fin n))) := by
    exact convex_inward_dilate_closure_subset n U hconv hzero a ha.le haone
  have hmem := unweighted_mem_dirichlet_of_compact_support n U _ hcompact hsub w hwsupp
  exact ⟨⟨w, hmem⟩, hwv, hwg⟩

end AffineFKProof
