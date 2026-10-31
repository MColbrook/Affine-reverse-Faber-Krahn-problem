module

public import AffineFK.BridgeMiddleAffinePaths

/-!
# Pointwise survival decomposition for the actual split affine bridge

The complete closed interval is covered, including both outer endpoints
and the middle point. This is a deterministic identity before any product
measure integration or Gaussian density calculation.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

theorem bridgePostUnitTime_surjective (s t : ℝ) (ht : 0 < t) :
    Function.Surjective (bridgePostUnitTime s t ht) := by
  intro u
  refine ⟨⟨s+t*(u:ℝ), ?_, ?_⟩, ?_⟩
  · have h := mul_nonneg ht.le u.2.1
    linarith
  · have h := mul_le_mul_of_nonneg_left u.2.2 ht.le
    linarith
  · apply Subtype.ext
    change (s+t*(u:ℝ)-s)/t = u
    field_simp
    ring

theorem bridgeMiddleAffinePath_survival_iff (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x z : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (p : BridgeMiddleSample n) :
    (∀ r : Icc (0 : ℝ) (s+t),
      bridgeAffineCenteredPath n (s+t) x z (bridgeSplitCenteredPath n s t hs ht p) r ∈ Ω) ↔
    (∀ u : Icc (0 : ℝ) 1,
      bridgeEndpointBridgePath n s x (bridgeSplitMiddlePoint n s t x z p.2)
        (bridgeContinuousSeries n p.1.1) u ∈ Ω) ∧
    (∀ u : Icc (0 : ℝ) 1,
      bridgeEndpointBridgePath n t (bridgeSplitMiddlePoint n s t x z p.2) z
        (bridgeContinuousSeries n p.1.2) u ∈ Ω) := by
  constructor
  · intro h
    constructor
    · intro u
      obtain ⟨r,hr⟩ := bridgeUnitTime_surjective s hs u
      let R : Icc (0 : ℝ) (s+t) := ⟨r,r.2.1,r.2.2.trans (le_add_of_nonneg_right ht.le)⟩
      have hh := h R
      rw [bridgeMiddleAffinePath_left n s t hs ht x z p R r.2.2] at hh
      change bridgeEndpointBridgePath n s x (bridgeSplitMiddlePoint n s t x z p.2)
        (bridgeContinuousSeries n p.1.1) (bridgeUnitTime s hs r) ∈ Ω at hh
      rwa [hr] at hh
    · intro u
      obtain ⟨r,hr⟩ := bridgePostUnitTime_surjective s t ht u
      let R : Icc (0 : ℝ) (s+t) := ⟨r,hs.le.trans r.2.1,r.2.2⟩
      have hh := h R
      rw [bridgeMiddleAffinePath_right n s t hs ht x z p R r.2.1] at hh
      change bridgeEndpointBridgePath n t (bridgeSplitMiddlePoint n s t x z p.2) z
        (bridgeContinuousSeries n p.1.2) (bridgePostUnitTime s t ht r) ∈ Ω at hh
      rwa [hr] at hh
  · rintro ⟨hleft,hright⟩ r
    by_cases hr : (r:ℝ) ≤ s
    · rw [bridgeMiddleAffinePath_left n s t hs ht x z p r hr]
      exact hleft _
    · rw [bridgeMiddleAffinePath_right n s t hs ht x z p r (le_of_not_ge hr)]
      exact hright _

end AffineFKProof
