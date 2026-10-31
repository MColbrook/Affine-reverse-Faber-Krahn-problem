module

public import AffineFK.UnweightedSobolevGraph
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.Sequences

/-!
# A genuine Hilbert bounded-preimage limit

Riesz representation maps a bounded sequence in a complete Hilbert space
to a compact weak-star dual ball. Scalar evaluations identify the value
of a cluster point under a continuous linear map. No separability,
assumed weak compactness, or reflexivity axiom is used.

Mathlib's Banach--Alaoglu development and Frechet--Riesz equivalence retain
their Apache-2.0 contributor attribution in the imported primary sources.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

theorem ordinaryWeakScore_hilbert_bounded_preimage_limit
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (J : V →L[ℝ] F) (v : ℕ → V) (f : F) (R : ℝ)
    (hbound : ∀ k, ‖v k‖ ≤ R) (hlimit : Tendsto (fun k => J (v k)) atTop (𝓝 f)) :
    ∃ w : V, J w = f ∧ ‖w‖ ≤ R := by
  let K : Set (WeakDual ℝ V) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R
  let Φ : ℕ → WeakDual ℝ V := fun k => StrongDual.toWeakDual ((toDual ℝ V) (v k))
  have hΦ (k : ℕ) : Φ k ∈ K := by
    simpa [K, Φ, Metric.mem_closedBall, (toDual ℝ V).norm_map] using hbound k
  have hmap : Filter.map Φ atTop ≤ 𝓟 K := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ k in atTop, Φ k ∈ K
    exact Eventually.of_forall hΦ
  obtain ⟨Φ₀, hΦ₀, hcluster⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ V) R).exists_mapClusterPt hmap
  let w : V := (toDual ℝ V).symm (WeakDual.toStrongDual Φ₀)
  have hwbound : ‖w‖ ≤ R := by
    change ‖(toDual ℝ V).symm (WeakDual.toStrongDual Φ₀)‖ ≤ R
    rw [(toDual ℝ V).symm.norm_map]
    simpa only [K, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hΦ₀
  refine ⟨w, ?_, hwbound⟩
  let z := J w - f
  let ℓ : V →L[ℝ] ℝ := (innerSL ℝ z).comp J
  let y : V := (toDual ℝ V).symm ℓ
  have heval (k : ℕ) : Φ k y = ℓ (v k) := by
    change ⟪v k, y⟫ = ℓ (v k)
    rw [real_inner_comm]
    exact toDual_symm_apply
  have hscalar : Tendsto (fun k => Φ k y) atTop (𝓝 ((innerSL ℝ z) f)) := by
    simpa only [heval, ℓ, ContinuousLinearMap.comp_apply, Function.comp_def] using
      ((innerSL ℝ z).continuous.tendsto f).comp hlimit
  have hscalarCluster : MapClusterPt (Φ₀ y) atTop (fun k => Φ k y) :=
    MapClusterPt.continuousAt_comp (WeakDual.eval_continuous y).continuousAt hcluster
  obtain ⟨ns, hns, hsub⟩ := hscalarCluster.tendsto_subseq
  have hscalarEq : Φ₀ y = (innerSL ℝ z) f :=
    tendsto_nhds_unique hsub (hscalar.comp hns.tendsto_atTop)
  have hwEval : Φ₀ y = ℓ w := by
    calc
      _ = ⟪w, y⟫ := toDual_symm_apply.symm
      _ = ⟪y, w⟫ := real_inner_comm _ _
      _ = _ := toDual_symm_apply
  have hinner : ⟪z, J w⟫ = ⟪z, f⟫ := by
    rw [hwEval] at hscalarEq
    exact hscalarEq
  apply sub_eq_zero.mp
  have hz : ⟪z, z⟫ = 0 := by
    change ⟪z, J w - f⟫ = 0
    rw [inner_sub_right, hinner, sub_self]
  exact inner_self_eq_zero.mp hz

end AffineFKProof
