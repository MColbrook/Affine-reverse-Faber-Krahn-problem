module

public import AffineFK.DirichletRayleigh
public import AffineFK.OrdinaryFisherLinearMapEnergy

/-!
# Invertible linear transport of the actual zero-boundary Sobolev domain

The square-root Jacobian normalizes the value norm. Compact smooth tests
are transported inside the actual image open set, and their H1 limit
belongs to its genuine H0 closure. This reuses the proved ordinary-Fisher
linear L2 transport and Mathlib's compact-test and change-of-variables
proofs; no boundary trace or smooth boundary is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology

def dirichletLinearImage (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) : Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨A.symm ⁻¹' (U : Set (EuclideanSpace ℝ (Fin n))), U.isOpen.preimage A.symm.continuous⟩

theorem dirichletLinearImage_coe (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) :
    (dirichletLinearImage n A U : Set (EuclideanSpace ℝ (Fin n))) = A '' (U : Set _) := by
  ext x
  change A.symm x ∈ (U : Set (EuclideanSpace ℝ (Fin n))) ↔ x ∈ A '' (U : Set _)
  constructor
  · intro hx
    exact ⟨A.symm x, hx, A.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [A.symm_apply_apply] using hy

def dirichletLinearTest (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) (φ : 𝓓(U, ℝ)) :
    𝓓(dirichletLinearImage n A U, ℝ) :=
  ⟨φ ∘ A.symm, φ.contDiff.comp A.symm.contDiff,
    φ.hasCompactSupport.comp_homeomorph A.symm.toHomeomorph,
    (tsupport_comp_subset_preimage φ A.symm.continuous).trans
      (Set.preimage_mono φ.tsupport_subset)⟩

theorem dirichlet_approximating_tests (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (v : dirichletSobolev n U) :
    ∃ φ : ℕ → 𝓓(U, ℝ),
      Tendsto (fun k => dirichletTestToH1 n U (φ k)) atTop (𝓝 v.val) := by
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.mp v.property
  choose φ hφ using hw
  exact ⟨φ, by simpa only [hφ] using hlim⟩

set_option maxHeartbeats 1000000 in
theorem dirichlet_linear_graph_transport (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) (v : dirichletSobolev n U) :
    ∃ w : dirichletSobolev n (dirichletLinearImage n A U),
      dirichletValue n _ w = Real.sqrt (ordinaryFisherLinearJacobian n A) •
        ordinaryFisherLinearPullbackLp n A ℝ (dirichletValue n U v) ∧
      dirichletGradient n _ w = Real.sqrt (ordinaryFisherLinearJacobian n A) •
        A.symm.toContinuousLinearMap.adjoint.compLp
          (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n)) (dirichletGradient n U v)) := by
  let V := dirichletLinearImage n A U
  let c := Real.sqrt (ordinaryFisherLinearJacobian n A)
  let Lv := c • ordinaryFisherLinearPullbackLp n A ℝ
  let Lg : Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    c • ((A.symm.toContinuousLinearMap.adjoint.compLpL (p := 2)
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))).comp
      (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n))))
  obtain ⟨w, hwv, hwg⟩ := ordinaryFisher_linear_graph_transport n A v.val
  obtain ⟨φ, hφ⟩ := dirichlet_approximating_tests n U v
  let ψ : ℕ → 𝓓(V, ℝ) := fun k => c • dirichletLinearTest n A U (φ k)
  have htop (k) : dirichletTestToTop n V (ψ k) =
      c • ordinaryFisherLinearTest n A.symm (dirichletTestToTop n U (φ k)) := by
    ext x
    rfl
  have hvEq (k) : unweightedTestToL2 n (dirichletTestToTop n V (ψ k)) =
      Lv (unweightedTestToL2 n (dirichletTestToTop n U (φ k))) := by
    rw [htop]
    change unweightedTestToL2 n (c • ordinaryFisherLinearTest n A.symm _) =
      c • ordinaryFisherLinearPullbackLp n A ℝ _
    rw [map_smul, ordinaryFisherLinearPullbackLp_test]
  have hgEq (k) : unweightedTestToL2 n (testFunctionGradient (dirichletTestToTop n V (ψ k))) =
      Lg (unweightedTestToL2 n (testFunctionGradient (dirichletTestToTop n U (φ k)))) := by
    rw [htop]
    change unweightedTestToL2 n (testFunctionGradient (c • ordinaryFisherLinearTest n A.symm _)) =
      c • A.symm.toContinuousLinearMap.adjoint.compLp (ordinaryFisherLinearPullbackLp n A _ _)
    rw [map_smul, map_smul, ordinaryFisherLinearPullbackLp_gradient_test]
  have hvLim : Tendsto (fun k => unweightedTestToL2 n (dirichletTestToTop n V (ψ k))) atTop
      (𝓝 (unweightedValue n w)) := by
    rw [hwv]
    exact (((Lv.continuous.tendsto _).comp
      (((unweightedValue n).continuous.tendsto v.val).comp hφ))).congr'
        (Eventually.of_forall fun k => (hvEq k).symm)
  have hgLim : Tendsto (fun k => unweightedTestToL2 n (testFunctionGradient (dirichletTestToTop n V (ψ k)))) atTop
      (𝓝 (unweightedGradient n w)) := by
    rw [hwg]
    exact (((Lg.continuous.tendsto _).comp
      (((unweightedGradient n).continuous.tendsto v.val).comp hφ))).congr'
        (Eventually.of_forall fun k => (hgEq k).symm)
  have hpair : Tendsto (fun k => unweightedSmoothPair n (dirichletTestToTop n V (ψ k))) atTop
      (𝓝 w.val) := by
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ
      (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))).symm.continuous.tendsto _).comp
        (hvLim.prodMk_nhds hgLim)
  have hH1 : Tendsto (fun k => dirichletTestToH1 n V (ψ k)) atTop (𝓝 w) :=
    tendsto_subtype_rng.mpr hpair
  have hmem : w ∈ dirichletSobolev n V :=
    (dirichletSobolev_isClosed n V).mem_of_tendsto hH1
      (Eventually.of_forall fun k => dirichlet_test_mem n V (ψ k))
  exact ⟨⟨w, hmem⟩, hwv, hwg⟩

end AffineFKProof
