module

public import AffineFK.OrdinaryWeakScoreSobolevCompactness

/-!
# A genuine Hilbert graph limit preserving a second operator bound

This extends the actual Riesz/Banach--Alaoglu bounded-preimage argument
from OrdinaryWeakScoreSobolevCompactness. Scalar evaluations also preserve
a prescribed bound on a second continuous linear map. The weak compactness
is proved by Mathlib's WeakDual closed-ball theorem, not assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

theorem bridge_hilbert_scalar_cluster
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (v : ℕ → V) (R : ℝ) (hbound : ∀ k, ‖v k‖ ≤ R) :
    ∃ w : V, ‖w‖ ≤ R ∧ ∀ ℓ : V →L[ℝ] ℝ,
      MapClusterPt (ℓ w) atTop (fun k => ℓ (v k)) := by
  let K : Set (WeakDual ℝ V) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R
  let Φ : ℕ → WeakDual ℝ V := fun k => StrongDual.toWeakDual ((toDual ℝ V) (v k))
  have hΦ (k : ℕ) : Φ k ∈ K := by
    simpa [K, Φ, Metric.mem_closedBall, (toDual ℝ V).norm_map] using hbound k
  have hmap : Filter.map Φ atTop ≤ 𝓟 K := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ k in atTop, Φ k ∈ K
    exact Eventually.of_forall hΦ
  obtain ⟨Φ₀, hΦ₀, hcluster⟩ :=
    (WeakDual.isCompact_closedBall (0 : StrongDual ℝ V) R).exists_mapClusterPt hmap
  let w : V := (toDual ℝ V).symm (WeakDual.toStrongDual Φ₀)
  have hw : ‖w‖ ≤ R := by
    change ‖(toDual ℝ V).symm (WeakDual.toStrongDual Φ₀)‖ ≤ R
    rw [(toDual ℝ V).symm.norm_map]
    simpa only [K, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hΦ₀
  refine ⟨w, hw, ?_⟩
  intro ℓ
  let y : V := (toDual ℝ V).symm ℓ
  have heval (k : ℕ) : Φ k y = ℓ (v k) := by
    change ⟪v k, y⟫ = ℓ (v k)
    rw [real_inner_comm]
    exact toDual_symm_apply
  have hweval : Φ₀ y = ℓ w := by
    calc
      _ = ⟪w, y⟫ := toDual_symm_apply.symm
      _ = ⟪y, w⟫ := real_inner_comm _ _
      _ = _ := toDual_symm_apply
  have he := MapClusterPt.continuousAt_comp (WeakDual.eval_continuous y).continuousAt hcluster
  simpa only [Function.comp_def, heval, hweval] using he

theorem bridge_hilbert_graph_limit_norm_bound
    {V F H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : V →L[ℝ] F) (G : V →L[ℝ] H) (v : ℕ → V) (f : F) (R S : ℝ)
    (hS : 0 ≤ S) (hbound : ∀ k, ‖v k‖ ≤ R) (hG : ∀ k, ‖G (v k)‖ ≤ S)
    (hlimit : Tendsto (fun k => J (v k)) atTop (𝓝 f)) :
    ∃ w : V, J w = f ∧ ‖G w‖ ≤ S := by
  obtain ⟨w, _, hc⟩ := bridge_hilbert_scalar_cluster v R hbound
  have hw : J w = f := by
    let z := J w - f
    let ℓ : V →L[ℝ] ℝ := (innerSL ℝ z).comp J
    have hscalar : Tendsto (fun k => ℓ (v k)) atTop (𝓝 ((innerSL ℝ z) f)) :=
      ((innerSL ℝ z).continuous.tendsto f).comp hlimit
    obtain ⟨ns, hns, hsub⟩ := (hc ℓ).tendsto_subseq
    have heq : ℓ w = (innerSL ℝ z) f :=
      tendsto_nhds_unique hsub (hscalar.comp hns.tendsto_atTop)
    have hz : ⟪z, z⟫ = 0 := by
      change ⟪z, J w - f⟫ = 0
      rw [inner_sub_right]
      exact sub_eq_zero.mpr heq
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  refine ⟨w, hw, ?_⟩
  let z := G w
  let ℓ : V →L[ℝ] ℝ := (innerSL ℝ z).comp G
  have he : ∀ k, ℓ (v k) ≤ ‖z‖ * S := by
    intro k
    exact (real_inner_le_norm z (G (v k))).trans
      (mul_le_mul_of_nonneg_left (hG k) (norm_nonneg z))
  have hz : ℓ w ≤ ‖z‖ * S :=
    isClosed_Iic.mem_of_mapClusterPt (hc ℓ) (Eventually.of_forall he)
  change ⟪z, z⟫ ≤ ‖z‖ * S at hz
  rw [real_inner_self_eq_norm_sq] at hz
  by_cases hzero : ‖z‖ = 0
  · simpa only [show G w = z from rfl, hzero] using hS
  · have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hzero)
    change ‖z‖ ≤ S
    nlinarith

end AffineFKProof
