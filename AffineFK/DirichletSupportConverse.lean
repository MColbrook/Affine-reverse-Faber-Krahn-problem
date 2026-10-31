module

public import AffineFK.DirichletSupportDilation
public import AffineFK.DirichletSupportDilationLimit
public import AffineFK.DirichletGroundstateHilbert
public import AffineFK.DirichletGroundstateSequence
public import AffineFK.OrdinaryWeakScoreSobolevCompactness

/-!
# Zero exterior values imply genuine H0 membership on a bounded convex domain

The actual inward H0 dilations converge in scalar L2 and have uniformly
bounded H1 norm. Proved Hilbert bounded-preimage compactness and actual
value-map injectivity identify the limit with the original H1 element.
No trace, boundary regularity, or weak-gradient converse is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter Set
open scoped RealInnerProductSpace Topology

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem unweighted_linear_gradient_energy_bound (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (v w : unweightedSobolevGraph n)
    (hwg : (unweightedGradient n w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
      fun z => Real.sqrt (ordinaryFisherLinearJacobian n A) •
        A.symm.toContinuousLinearMap.adjoint (unweightedGradient n v (A.symm z))) :
    ‖unweightedGradient n w‖ ^ 2 ≤
      ‖A.symm.toContinuousLinearMap‖ ^ 2 * ‖unweightedGradient n v‖ ^ 2 := by
  let g := unweightedGradient n v
  let q := A.symm.toContinuousLinearMap.adjoint.compLp g
  have hq := A.symm.toContinuousLinearMap.adjoint.coeFn_compLp' g
  have hA := ordinaryFisherLinearMap_quasiMeasurePreserving n A.symm
  have heq : (fun z => ‖unweightedGradient n w z‖ ^ 2) =ᵐ[volume]
      fun z => ‖Real.sqrt (ordinaryFisherLinearJacobian n A) • q (A.symm z)‖ ^ 2 := by
    filter_upwards [hwg, hA.ae_eq_comp hq] with z hw hqq
    change q (A.symm z) = A.symm.toContinuousLinearMap.adjoint (g (A.symm z)) at hqq
    rw [hw, hqq]
  calc
    _ = ∫ z, ‖unweightedGradient n w z‖ ^ 2 := l2_norm_sq_integral volume _
    _ = ∫ z, ‖Real.sqrt (ordinaryFisherLinearJacobian n A) • q (A.symm z)‖ ^ 2 := integral_congr_ae heq
    _ = ∫ x, ‖q x‖ ^ 2 := (ordinaryFisherLinear_scaled_pullback_energy n A q).2
    _ = ∫ x, ‖A.symm.toContinuousLinearMap.adjoint (g x)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hq] with x hx
      rw [hx]
    _ ≤ ‖A.symm.toContinuousLinearMap‖ ^ 2 * ∫ x, ‖g x‖ ^ 2 :=
      ordinaryFisherLinear_adjoint_energy_bound n A g
    _ = _ := congrArg (fun d : ℝ => ‖A.symm.toContinuousLinearMap‖ ^ 2 * d)
      (l2_norm_sq_integral volume (unweightedGradient n v)).symm

theorem supportDilation_inverse_norm_bound (n : ℕ) (a : ℝ) (ha : (1 / 2 : ℝ) ≤ a) :
    ‖(supportDilationLinearEquiv n a (by linarith)).symm.toContinuousLinearMap‖ ≤ 2 := by
  have ha0 : 0 < a := by linarith
  change ‖a⁻¹ • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))‖ ≤ 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)]
  have hi : a⁻¹ ≤ (2 : ℝ) := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ ha0).mpr (by linarith)
  calc
    _ ≤ 2 * 1 := mul_le_mul hi (ContinuousLinearMap.norm_id_le)
      (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

theorem unweighted_mem_dirichlet_of_zero_exterior (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hconv : Convex ℝ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ (U : Set (EuclideanSpace ℝ (Fin n))))
    (hbounded : Bornology.IsBounded (U : Set (EuclideanSpace ℝ (Fin n))))
    (v : unweightedSobolevGraph n)
    (hsupp : ∀ᵐ x ∂volume, x ∉ closure (U : Set (EuclideanSpace ℝ (Fin n))) → unweightedValue n v x = 0) :
    v ∈ dirichletSobolev n U := by
  let a : ℕ → ℝ := fun k => 1 - ((k : ℝ) + 2)⁻¹
  have ha (k) : (1 / 2 : ℝ) ≤ a k := by
    have hk : 0 < (k : ℝ) + 2 := by positivity
    have hi : ((k : ℝ) + 2)⁻¹ ≤ (1 / 2 : ℝ) := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ hk).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    dsimp only [a]
    linarith
  have ha0 (k) : 0 < a k := by have := ha k; linarith
  have haone (k) : a k < 1 := by
    dsimp only [a]
    have hi : 0 < ((k : ℝ) + 2)⁻¹ := by positivity
    linarith
  have halim : Tendsto a atTop (𝓝 1) := by
    have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
        tendsto_inverse_succ.comp (tendsto_add_atTop_nat 1)
    simpa only [a, sub_zero] using tendsto_const_nhds.sub hinv
  choose w hwv hwg using fun k => unweighted_inward_dilation_mem_dirichlet
    n U hconv hzero hbounded v hsupp (a k) (ha0 k) (haone k)
  have hv (k) : dirichletValue n U (w k) = supportDilationL2 n (a k) (ha0 k).ne' (unweightedValue n v) := by
    apply Lp.ext
    exact (hwv k).trans (supportDilationL2_coe n (a k) (ha0 k).ne' (unweightedValue n v)).symm
  have hvalue : Tendsto (fun k => dirichletValue n U (w k)) atTop (𝓝 (unweightedValue n v)) := by
    simpa only [hv] using supportDilationL2_tendsto n a ha (fun k => (haone k).le) halim (unweightedValue n v)
  have hgrad (k) : ‖dirichletGradient n U (w k)‖ ^ 2 ≤ 4 * ‖unweightedGradient n v‖ ^ 2 := by
    have h := unweighted_linear_gradient_energy_bound n
      (supportDilationLinearEquiv n (a k) (ha0 k).ne') v (w k) (hwg k)
    have hop := supportDilation_inverse_norm_bound n (a k) (ha k)
    have hs : ‖(supportDilationLinearEquiv n (a k) (ha0 k).ne').symm.toContinuousLinearMap‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg (supportDilationLinearEquiv n (a k) (ha0 k).ne').symm.toContinuousLinearMap]
    exact h.trans (mul_le_mul_of_nonneg_right hs (sq_nonneg ‖unweightedGradient n v‖))
  let R := Real.sqrt (‖unweightedValue n v‖ ^ 2 + 4 * ‖unweightedGradient n v‖ ^ 2)
  have hbound (k) : ‖w k‖ ≤ R := by
    have hs : ‖w k‖ ^ 2 ≤ ‖unweightedValue n v‖ ^ 2 + 4 * ‖unweightedGradient n v‖ ^ 2 := by
      rw [dirichletGroundstate_graph_norm_sq, hv, supportDilationL2_norm]
      exact add_le_add le_rfl (hgrad k)
    exact (Real.sqrt_sq (norm_nonneg _)).symm.trans_le (Real.sqrt_le_sqrt hs)
  letI := dirichletGroundstateInnerProductSpace n U
  obtain ⟨z, hz, _⟩ := ordinaryWeakScore_hilbert_bounded_preimage_limit
    (dirichletValue n U) w (unweightedValue n v) R hbound hvalue
  have heq : (z : unweightedSobolevGraph n) = v := unweighted_sobolev_value_injective n hz
  exact heq ▸ z.property

end AffineFKProof
