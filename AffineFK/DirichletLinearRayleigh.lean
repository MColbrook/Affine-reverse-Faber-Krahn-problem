module

public import AffineFK.DirichletLinearTransport

/-!
# The exact operator-norm factor in actual Dirichlet Rayleigh transport

The transformed function belongs to the true H0 domain. Its scalar value
norm is unchanged by the square-root Jacobian, and its actual gradient
energy is bounded by the squared inverse operator norm. The resulting
quotient comparison uses the actual variational Rayleigh quotient.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology ENNReal

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000 in
theorem dirichlet_linear_graph_energy (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) (v : dirichletSobolev n U) :
    ∃ w : dirichletSobolev n (dirichletLinearImage n A U),
      ‖dirichletValue n (dirichletLinearImage n A U) w‖ ^ 2 = ‖dirichletValue n U v‖ ^ 2 ∧
      ‖dirichletGradient n (dirichletLinearImage n A U) w‖ ^ 2 ≤
        ‖A.symm.toContinuousLinearMap‖ ^ 2 * ‖dirichletGradient n U v‖ ^ 2 := by
  obtain ⟨w, hwv, hwg⟩ := dirichlet_linear_graph_transport n A U v
  let c := Real.sqrt (ordinaryFisherLinearJacobian n A)
  let g := dirichletGradient n U v
  let q := A.symm.toContinuousLinearMap.adjoint.compLp g
  have hq := A.symm.toContinuousLinearMap.adjoint.coeFn_compLp' g
  have hA := ordinaryFisherLinearMap_quasiMeasurePreserving n A.symm
  have hv : (fun z => ‖dirichletValue n (dirichletLinearImage n A U) w z‖ ^ 2) =ᵐ[volume]
      fun z => ‖c • dirichletValue n U v (A.symm z)‖ ^ 2 := by
    rw [hwv]
    filter_upwards [Lp.coeFn_smul c (ordinaryFisherLinearPullbackLp n A ℝ (dirichletValue n U v)),
      ordinaryFisherLinearPullbackLp_coe n A (dirichletValue n U v)] with z hs hp
    rw [hs]
    change ‖c • ordinaryFisherLinearPullbackLp n A ℝ (dirichletValue n U v) z‖ ^ 2 = _
    rw [hp]
  have hg : (fun z => ‖dirichletGradient n (dirichletLinearImage n A U) w z‖ ^ 2) =ᵐ[volume]
      fun z => ‖c • q (A.symm z)‖ ^ 2 := by
    rw [hwg]
    filter_upwards [Lp.coeFn_smul c (A.symm.toContinuousLinearMap.adjoint.compLp
        (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n)) g)),
      A.symm.toContinuousLinearMap.adjoint.coeFn_compLp'
        (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n)) g),
      ordinaryFisherLinearPullbackLp_coe n A g, hA.ae_eq_comp hq] with z hs hc hp hqq
    rw [hs]
    change ‖c • A.symm.toContinuousLinearMap.adjoint.compLp
      (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n)) g) z‖ ^ 2 = _
    change q (A.symm z) = A.symm.toContinuousLinearMap.adjoint (g (A.symm z)) at hqq
    rw [hc, hp, hqq]
  refine ⟨w, ?_, ?_⟩
  · rw [l2_norm_sq_integral, l2_norm_sq_integral, integral_congr_ae hv]
    simpa only [c] using (ordinaryFisherLinear_scaled_pullback_energy n A (dirichletValue n U v)).2
  · have he : (∫ x, ‖q x‖ ^ 2) = ∫ x, ‖A.symm.toContinuousLinearMap.adjoint (g x)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hq] with x hx
      rw [hx]
    calc
      _ = ∫ z, ‖dirichletGradient n (dirichletLinearImage n A U) w z‖ ^ 2 :=
        l2_norm_sq_integral volume (dirichletGradient n (dirichletLinearImage n A U) w)
      _ = ∫ z, ‖c • q (A.symm z)‖ ^ 2 := integral_congr_ae hg
      _ = ∫ x, ‖q x‖ ^ 2 := (ordinaryFisherLinear_scaled_pullback_energy n A q).2
      _ = ∫ x, ‖A.symm.toContinuousLinearMap.adjoint (g x)‖ ^ 2 := he
      _ ≤ ‖A.symm.toContinuousLinearMap‖ ^ 2 * ∫ x, ‖g x‖ ^ 2 :=
        ordinaryFisherLinear_adjoint_energy_bound n A g
      _ = _ := congrArg (fun d : ℝ => ‖A.symm.toContinuousLinearMap‖ ^ 2 * d)
        (l2_norm_sq_integral volume (dirichletGradient n U v)).symm

theorem dirichlet_linear_rayleigh_transport (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Opens (EuclideanSpace ℝ (Fin n))) (v : dirichletSobolev n U)
    (hv : dirichletValue n U v ≠ 0) :
    ∃ w : dirichletSobolev n (dirichletLinearImage n A U),
      dirichletValue n (dirichletLinearImage n A U) w ≠ 0 ∧
      dirichletRayleigh n (dirichletLinearImage n A U) w ≤ ‖A.symm.toContinuousLinearMap‖ ^ 2 * dirichletRayleigh n U v := by
  obtain ⟨w, hwv, hwg⟩ := dirichlet_linear_graph_energy n A U v
  refine ⟨w, ?_, ?_⟩
  · intro hw
    have hz : ‖dirichletValue n U v‖ ^ 2 = 0 := by
      rw [← hwv, hw, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact hv (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · unfold dirichletRayleigh
    calc
      _ = ‖dirichletGradient n (dirichletLinearImage n A U) w‖ ^ 2 / ‖dirichletValue n U v‖ ^ 2 :=
        congrArg (fun d : ℝ => ‖dirichletGradient n (dirichletLinearImage n A U) w‖ ^ 2 / d) hwv
      _ ≤ (‖A.symm.toContinuousLinearMap‖ ^ 2 * ‖dirichletGradient n U v‖ ^ 2) /
          ‖dirichletValue n U v‖ ^ 2 :=
        div_le_div_of_nonneg_right hwg (sq_nonneg ‖dirichletValue n U v‖)
      _ = _ := mul_div_assoc _ _ _

end AffineFKProof
