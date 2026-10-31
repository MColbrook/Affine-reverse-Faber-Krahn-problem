module

public import AffineFK.OrdinaryFisherLinearMapLp

/-!
# Direct invertible-linear transport of the genuine unweighted H1 graph

Compact smooth tests are transformed with the exact square-root Jacobian
factor. The proved continuous L2 pullback transports both limits of an
actual approximating sequence. Closedness of the original unweighted
graph then constructs the output H1 value and its inverse-adjoint weak
gradient, without a weak-score-to-Sobolev converse.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology

theorem ordinaryFisher_linear_graph_transport (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : unweightedSobolevGraph n) :
    ∃ w : unweightedSobolevGraph n,
      unweightedValue n w = Real.sqrt (ordinaryFisherLinearJacobian n A) •
        ordinaryFisherLinearPullbackLp n A ℝ (unweightedValue n v) ∧
      unweightedGradient n w = Real.sqrt (ordinaryFisherLinearJacobian n A) •
        A.symm.toContinuousLinearMap.adjoint.compLp
          (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n)) (unweightedGradient n v)) := by
  let c := Real.sqrt (ordinaryFisherLinearJacobian n A)
  let Lv := c • ordinaryFisherLinearPullbackLp n A ℝ
  let Lg : Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    c • ((A.symm.toContinuousLinearMap.adjoint.compLpL (p := 2)
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))).comp
      (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n))))
  obtain ⟨φ, hφ, hgφ⟩ := unweighted_approximating_tests n v
  let ψ : ℕ → 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
    fun k => c • ordinaryFisherLinearTest n A.symm (φ k)
  have hvEq (k : ℕ) : unweightedTestToL2 n (ψ k) = Lv (unweightedTestToL2 n (φ k)) := by
    change unweightedTestToL2 n (c • ordinaryFisherLinearTest n A.symm (φ k)) =
      c • ordinaryFisherLinearPullbackLp n A ℝ (unweightedTestToL2 n (φ k))
    rw [map_smul, ordinaryFisherLinearPullbackLp_test]
  have hgEq (k : ℕ) : unweightedTestToL2 n (testFunctionGradient (ψ k)) =
      Lg (unweightedTestToL2 n (testFunctionGradient (φ k))) := by
    change unweightedTestToL2 n (testFunctionGradient
      (c • ordinaryFisherLinearTest n A.symm (φ k))) = c •
        A.symm.toContinuousLinearMap.adjoint.compLp
          (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n))
            (unweightedTestToL2 n (testFunctionGradient (φ k))))
    rw [map_smul, map_smul, ordinaryFisherLinearPullbackLp_gradient_test]
  have hvLim : Tendsto (fun k => unweightedTestToL2 n (ψ k)) atTop
      (𝓝 (Lv (unweightedValue n v))) := by
    apply ((Lv.continuous.tendsto _).comp hφ).congr'
    exact Eventually.of_forall fun k => (hvEq k).symm
  have hgLim : Tendsto (fun k => unweightedTestToL2 n (testFunctionGradient (ψ k))) atTop
      (𝓝 (Lg (unweightedGradient n v))) := by
    apply ((Lg.continuous.tendsto _).comp hgφ).congr'
    exact Eventually.of_forall fun k => (hgEq k).symm
  have hpair : Tendsto (fun k => unweightedSmoothPair n (ψ k)) atTop
      (𝓝 (WithLp.toLp 2 (Lv (unweightedValue n v), Lg (unweightedGradient n v)))) := by
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ
      (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))).symm.continuous.tendsto _).comp
        (hvLim.prodMk_nhds hgLim)
  have hmem : WithLp.toLp 2 (Lv (unweightedValue n v), Lg (unweightedGradient n v)) ∈
      unweightedSobolevGraph n :=
    (unweightedSobolevGraph_isClosed n).mem_of_tendsto hpair
      (Eventually.of_forall fun k => unweighted_smooth_pair_mem n (ψ k))
  exact ⟨⟨_, hmem⟩, rfl, rfl⟩

theorem ordinaryFisher_linear_graph_representatives (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : unweightedSobolevGraph n) :
    ∃ w : unweightedSobolevGraph n,
      (unweightedValue n w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        (fun z => Real.sqrt (ordinaryFisherLinearJacobian n A) * unweightedValue n v (A.symm z)) ∧
      (unweightedGradient n w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
        fun z => Real.sqrt (ordinaryFisherLinearJacobian n A) •
          A.symm.toContinuousLinearMap.adjoint (unweightedGradient n v (A.symm z)) := by
  obtain ⟨w, hwv, hwg⟩ := ordinaryFisher_linear_graph_transport n A v
  refine ⟨w, ?_, ?_⟩
  · rw [hwv]
    filter_upwards [Lp.coeFn_smul (Real.sqrt (ordinaryFisherLinearJacobian n A))
        (ordinaryFisherLinearPullbackLp n A ℝ (unweightedValue n v)),
      ordinaryFisherLinearPullbackLp_coe n A (unweightedValue n v)] with z hs hp
    rw [hs]
    change Real.sqrt (ordinaryFisherLinearJacobian n A) *
      ordinaryFisherLinearPullbackLp n A ℝ (unweightedValue n v) z = _
    rw [hp]
  · rw [hwg]
    filter_upwards [Lp.coeFn_smul (Real.sqrt (ordinaryFisherLinearJacobian n A))
        (A.symm.toContinuousLinearMap.adjoint.compLp
          (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n)) (unweightedGradient n v))),
      A.symm.toContinuousLinearMap.adjoint.coeFn_compLp'
        (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n)) (unweightedGradient n v)),
      ordinaryFisherLinearPullbackLp_coe n A (unweightedGradient n v)] with z hs hc hp
    rw [hs]
    change Real.sqrt (ordinaryFisherLinearJacobian n A) •
      A.symm.toContinuousLinearMap.adjoint.compLp
        (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n)) (unweightedGradient n v)) z = _
    rw [hc, hp]

theorem ordinaryFisher_linear_sqrt_graph (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x)) :
    ∃ w : unweightedSobolevGraph n,
      (unweightedValue n w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        (fun z => Real.sqrt (ordinaryFisherLinearDensity n A ρ z)) ∧
      (unweightedGradient n w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
        fun z => Real.sqrt (ordinaryFisherLinearJacobian n A) •
          A.symm.toContinuousLinearMap.adjoint (unweightedGradient n v (A.symm z)) := by
  obtain ⟨w, hwv, hwg⟩ := ordinaryFisher_linear_graph_representatives n A v
  refine ⟨w, hwv.trans ?_, hwg⟩
  have hA := ordinaryFisherLinearMap_quasiMeasurePreserving n A.symm
  filter_upwards [hA.ae_eq_comp hv] with z hz
  change unweightedValue n v (A.symm z) = Real.sqrt (ρ (A.symm z)) at hz
  rw [hz, ordinaryFisherLinearDensity, Real.sqrt_mul (ordinaryFisherLinearJacobian_pos n A).le]

end AffineFKProof
