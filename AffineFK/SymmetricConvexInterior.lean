module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.NormNum

/-! Origin symmetry and nonempty interior put the origin in the interior.
The actual homeomorphism under negation and convex midpoint are used;
origin membership is not added to the symmetric-body assumptions. -/

@[expose] public noncomputable section
namespace AffineFKProof
open Set

theorem symmetric_convex_zero_mem_interior (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : Convex ℝ D)
    (hinterior : (interior D).Nonempty) (hsym : ∀ x, -x ∈ D ↔ x ∈ D) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ interior D := by
  have himage : Neg.neg '' D = D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hsym y).mpr hy
    · intro hx
      exact ⟨-x, (hsym x).mpr hx, neg_neg x⟩
  obtain ⟨x, hx⟩ := hinterior
  have hnx : -x ∈ interior D := by
    have h := (Homeomorph.neg (EuclideanSpace ℝ (Fin n))).isOpenMap.image_interior_subset D
      (show -x ∈ Neg.neg '' interior D from ⟨x, hx, rfl⟩)
    change -x ∈ interior (Neg.neg '' D) at h
    rwa [himage] at h
  have h := hD.interior hx hnx (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simpa only [← smul_add, add_neg_cancel, smul_zero] using h

end AffineFKProof
