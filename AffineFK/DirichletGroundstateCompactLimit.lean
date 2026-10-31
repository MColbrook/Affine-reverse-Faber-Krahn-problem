module

public import AffineFK.OrdinaryWeakScoreSobolevCompactness
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith

/-!
# A compact value map preserves the optimal gradient-energy limit

This abstract Hilbert lemma separates functional analysis from the
implementation of H0^1. Its premises include an actual normalized
minimizing sequence, not the desired limit or a spectral proxy.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open Filter Topology

theorem dirichletGroundstate_compact_minimizing_limit
    {V F G : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (J : V →L[ℝ] F) (D : V →L[ℝ] G) (hJ : Function.Injective J)
    (hnorm : ∀ w, ‖w‖ ^ 2 = ‖J w‖ ^ 2 + ‖D w‖ ^ 2)
    (ell R : ℝ) (hell : 0 ≤ ell) (v : ℕ → V)
    (hv : ∀ k, ‖J (v k)‖ ^ 2 = 1)
    (hE : Tendsto (fun k => ‖D (v k)‖ ^ 2) atTop (𝓝 ell))
    (hbound : ∀ k, ‖v k‖ ≤ R) (hcompact : IsCompactOperator J) :
    ∃ w : V, ‖J w‖ ^ 2 = 1 ∧ ‖D w‖ ^ 2 ≤ ell := by
  have hK := hcompact.isCompact_closure_image_closedBall (f := J.toLinearMap) R
  obtain ⟨f, _hfK, ns, hns, hconv⟩ := hK.tendsto_subseq (fun k =>
    subset_closure ⟨v k, mem_closedBall_zero_iff.mpr (hbound k), rfl⟩)
  have hf : ‖f‖ ^ 2 = 1 := by
    have hnormlimit := hconv.norm.pow 2
    have hone : Tendsto (fun k => ‖J (v (ns k))‖ ^ 2) atTop (𝓝 (1 : ℝ)) := by
      simpa only [hv] using tendsto_const_nhds
    exact tendsto_nhds_unique hnormlimit hone
  obtain ⟨w, hw, _hwbound⟩ := ordinaryWeakScore_hilbert_bounded_preimage_limit
    J (fun k => v (ns k)) f R (fun k => hbound (ns k)) hconv
  have hwone : ‖J w‖ ^ 2 = 1 := by rw [hw, hf]
  refine ⟨w, hwone, ?_⟩
  have hEsub := hE.comp hns.tendsto_atTop
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hEsub.eventually (gt_mem_nhds (by linarith : ell < ell + ε)))
  have hsmall (k : ℕ) : ‖v (ns (k + N))‖ ≤ Real.sqrt (1 + ell + ε) := by
    have hs : ‖v (ns (k + N))‖ ^ 2 ≤ 1 + ell + ε := by
      rw [hnorm, hv]
      have he : ‖D (v (ns (k + N)))‖ ^ 2 < ell + ε :=
        hN (k + N) (Nat.le_add_left N k)
      linarith only [he]
    exact (Real.sqrt_sq (norm_nonneg _)).symm.trans_le (Real.sqrt_le_sqrt hs)
  obtain ⟨wε, hwε, hbε⟩ := ordinaryWeakScore_hilbert_bounded_preimage_limit
    J (fun k => v (ns (k + N))) f (Real.sqrt (1 + ell + ε)) hsmall
    (hconv.comp (tendsto_add_atTop_nat N))
  have hweq : wε = w := hJ (hwε.trans hw.symm)
  subst wε
  have hnonneg : 0 ≤ 1 + ell + ε := by linarith
  have hsq : ‖w‖ ^ 2 ≤ 1 + ell + ε := by
    have hs := (sq_le_sq₀ (norm_nonneg w) (Real.sqrt_nonneg (1 + ell + ε))).mpr hbε
    rwa [Real.sq_sqrt hnonneg] at hs
  rw [hnorm, hwone] at hsq
  linarith

end AffineFKProof
