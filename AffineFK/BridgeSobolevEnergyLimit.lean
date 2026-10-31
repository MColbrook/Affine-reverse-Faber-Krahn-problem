module

public import AffineFK.BridgeHilbertGraphLimit
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Actual H1 limits with converging energy bounds

Strong L2 convergence of the values and a converging upper bound for
gradient energy yield a genuine completed-graph element. Riesz weak
compactness and scalar Cauchy--Schwarz prove the energy bound itself.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter InnerProductSpace
open scoped Topology RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false in
theorem bridge_unweighted_graph_limit_energy (n : ℕ)
    (v : ℕ → unweightedSobolevGraph n)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (b : ℕ → ℝ) (B : ℝ)
    (hG : ∀ k, ‖unweightedGradient n (v k)‖^2 ≤ b k)
    (hb : Tendsto b atTop (𝓝 B))
    (hlimit : Tendsto (fun k => unweightedValue n (v k)) atTop (𝓝 f)) :
    ∃ w : unweightedSobolevGraph n,
      unweightedValue n w = f ∧ ‖unweightedGradient n w‖^2 ≤ B := by
  have hB : 0 ≤ B := le_of_tendsto_of_tendsto' tendsto_const_nhds hb
    (fun k => (sq_nonneg _).trans (hG k))
  have hE := (hlimit.norm.pow 2).add hb
  obtain ⟨C, hC⟩ := hE.bddAbove_range
  have hbound (k : ℕ) : ‖v k‖ ≤ Real.sqrt (max C 0) := by
    have hk : ‖v k‖^2 ≤ max C 0 := by
      rw [unweighted_graph_norm_sq]
      have hc : ‖unweightedValue n (v k)‖^2 + b k ≤ C := hC ⟨k, rfl⟩
      have hg := hG k
      nlinarith [le_max_left C 0]
    exact (Real.le_sqrt (norm_nonneg _) (le_max_right _ _)).mpr hk
  obtain ⟨w, _, hc⟩ := bridge_hilbert_scalar_cluster v (Real.sqrt (max C 0)) hbound
  have hw : unweightedValue n w = f := by
    let z := unweightedValue n w - f
    let ℓ := (innerSL ℝ z).comp (unweightedValue n)
    have hs : Tendsto (fun k => ℓ (v k)) atTop (𝓝 ((innerSL ℝ z) f)) :=
      ((innerSL ℝ z).continuous.tendsto f).comp hlimit
    obtain ⟨ns, hns, hsub⟩ := (hc ℓ).tendsto_subseq
    have he : ℓ w = (innerSL ℝ z) f := tendsto_nhds_unique hsub (hs.comp hns.tendsto_atTop)
    have hz : ⟪z,z⟫ = 0 := by
      change ⟪z, unweightedValue n w - f⟫ = 0
      rw [inner_sub_right]
      exact sub_eq_zero.mpr he
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  refine ⟨w, hw, ?_⟩
  let z := unweightedGradient n w
  let ℓ := (innerSL ℝ z).comp (unweightedGradient n)
  have he : ℓ w = ‖z‖^2 := real_inner_self_eq_norm_sq z
  have hcauchy (k : ℕ) : (ℓ (v k))^2 ≤ ‖z‖^2 * b k := by
    have h := (sq_le_sq₀ (norm_nonneg ⟪z, unweightedGradient n (v k)⟫)
      (mul_nonneg (norm_nonneg z) (norm_nonneg _))).mpr
        (norm_inner_le_norm z (unweightedGradient n (v k)))
    have h' : (ℓ (v k))^2 ≤ ‖z‖^2 * ‖unweightedGradient n (v k)‖^2 := by
      change ⟪z, unweightedGradient n (v k)⟫^2 ≤ _
      simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (hG k) (sq_nonneg _))
  obtain ⟨ns, hns, hsub⟩ := (hc ℓ).tendsto_subseq
  have hfinal := le_of_tendsto_of_tendsto' (hsub.pow 2)
    (tendsto_const_nhds.mul (hb.comp hns.tendsto_atTop)) (fun k => hcauchy (ns k))
  rw [he] at hfinal
  by_cases hz : ‖z‖ = 0
  · simpa only [show unweightedGradient n w = z from rfl, hz, zero_pow (by norm_num : 2 ≠ 0)] using hB
  · have hp : 0 < ‖z‖^2 := sq_pos_of_ne_zero hz
    change ‖z‖^2 ≤ B
    apply (mul_le_mul_iff_right₀ hp).mp
    simpa only [pow_two] using hfinal

end AffineFKProof
