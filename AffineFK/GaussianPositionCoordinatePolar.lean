module

public import AffineFK.GaussianPositionPolarGeometry

/-!
# The literal coordinate polar and Euclidean absolute polar

The coordinate set expression is exactly the one-sided finite-sum polar
in the separately pinned upstream specification. Symmetry of K supplies
both signs. These proofs do not import any upstream theorem or source.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set TopologicalSpace
open scoped RealInnerProductSpace

theorem gaussianPosition_coordinate_inner (n : ℕ) (p x : Fin n → ℝ) :
    (∑ i, p i * x i) =
      ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)), WithLp.toLp 2 p⟫ := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial]
  rfl

theorem gaussianPosition_coordinatePolar_iff (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hsym : ∀ x ∈ K, -x ∈ K)
    (p : Fin n → ℝ) :
    (∀ v ∈ (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K,
      (∑ i, p i * v i) ≤ (1 : ℝ)) ↔
      (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin n)) ∈
        (innerₗ (EuclideanSpace ℝ (Fin n))).polar K := by
  have hpair (x : EuclideanSpace ℝ (Fin n)) :
      (∑ i, p i * (WithLp.ofLp x) i) = ⟪x, WithLp.toLp 2 p⟫ :=
    gaussianPosition_coordinate_inner n p (WithLp.ofLp x)
  constructor
  · intro h x hx
    change ‖⟪x, (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin n))⟫‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_le]
    have hpos := h (WithLp.ofLp x) ⟨x, hx, rfl⟩
    have hneg := h (WithLp.ofLp (-x)) ⟨-x, hsym x hx, rfl⟩
    rw [hpair x] at hpos
    rw [hpair (-x), inner_neg_left] at hneg
    exact ⟨by linarith, hpos⟩
  · intro h v hv
    rcases hv with ⟨x, hx, rfl⟩
    have hbound := h x hx
    change ‖⟪x, (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin n))⟫‖ ≤ (1 : ℝ) at hbound
    exact (hpair x).trans_le ((le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using hbound))

theorem gaussianPosition_coordinatePolar_image (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hsym : ∀ x ∈ K, -x ∈ K) :
    (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ''
      {p : Fin n → ℝ | ∀ v ∈
        (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K,
          (∑ i, p i * v i) ≤ (1 : ℝ)} =
      (innerₗ (EuclideanSpace ℝ (Fin n))).polar K := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (gaussianPosition_coordinatePolar_iff n K hsym p).mp hp
  · intro hy
    exact ⟨WithLp.ofLp y, (gaussianPosition_coordinatePolar_iff n K hsym _).mpr hy, rfl⟩

theorem gaussianPosition_coordinate_body (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (hinterior : (interior K).Nonempty) :
    IsCompact ((WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K) ∧
      Convex ℝ ((WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K) ∧
      (∀ v ∈ (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K,
        -v ∈ (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K) ∧
      (interior ((WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) '' K)).Nonempty := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  change IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧
    (∀ v ∈ e '' K, -v ∈ e '' K) ∧ (interior (e '' K)).Nonempty
  refine ⟨hcompact.image e.continuous, hconvex.linear_image e.toLinearMap, ?_, ?_⟩
  · rintro v ⟨x, hx, rfl⟩
    exact ⟨-x, hsym x hx, e.map_neg x⟩
  · change (interior (e.toHomeomorph '' K)).Nonempty
    rw [← e.toHomeomorph.image_interior K]
    exact hinterior.image e

end AffineFKProof
