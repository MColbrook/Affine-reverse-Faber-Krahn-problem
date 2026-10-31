module

public import AffineFK.DirichletBodyInvariances
public import AffineFK.GaussianPositionAction

/-!
# Actual body-interior transport for the affine reduction

The homeomorphism, special-linear volume law and actual H0 Rayleigh
monotonicity identify the literal domains used in the manuscript.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Set
open scoped ENNReal Pointwise

theorem dirichlet_linear_interior_image (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (EuclideanSpace ℝ (Fin n))) :
    dirichletLinearImage n A ⟨interior D,isOpen_interior⟩ =
      ⟨interior (A '' D),isOpen_interior⟩ := by
  apply SetLike.coe_injective
  rw [dirichletLinearImage_coe]
  exact A.toHomeomorph.image_interior D

theorem affineBody_linear_smul_image (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ) :
    A '' (r • D) = r • (A '' D) := by
  ext x
  constructor
  · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨A y,⟨y,hy,rfl⟩,(A.map_smul r y).symm⟩
  · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨r • y,⟨y,hy,rfl⟩,A.map_smul r y⟩

theorem affineBody_linear_translate_image (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    A '' ((fun x => x+z) '' D) = (fun x => x+A z) '' (A '' D) := by
  rw [image_image,image_image]
  congr 1
  funext x
  exact A.map_add x z

theorem affineBody_linear_even (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (EuclideanSpace ℝ (Fin n))) (heven : ∀ x, -x ∈ D ↔ x ∈ D) :
    ∀ x, -x ∈ A '' D ↔ x ∈ A '' D := by
  intro x
  constructor
  · rintro ⟨y,hy,hyx⟩
    refine ⟨-y,(heven y).mpr hy,?_⟩
    rw [map_neg,hyx,neg_neg]
  · rintro ⟨y,hy,rfl⟩
    exact ⟨-y,(heven y).mpr hy,A.map_neg y⟩

theorem affineBody_linear_interior_nonempty (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : (interior D).Nonempty) :
    (interior (A '' D)).Nonempty := by
  change (interior (A.toHomeomorph '' D)).Nonempty
  rw [← A.toHomeomorph.image_interior D]
  exact hD.image A

theorem affineBody_SL_volume (n : ℕ) (S : Matrix.SpecialLinearGroup (Fin n) ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) :
    volume (gaussianPositionSLLinear n S '' D) = volume D := by
  have h := (gaussianPositionSLLinear_preserves_volume n S).measure_preimage_emb
    (gaussianPositionSLLinear n S).toHomeomorph.measurableEmbedding
    (gaussianPositionSLLinear n S '' D)
  rw [Set.preimage_image_eq _ (gaussianPositionSLLinear n S).injective] at h
  exact h.symm

theorem dirichletEigenvalue_linear_translated_body (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    dirichletEigenvalue n ⟨interior (A '' ((fun x => x+z) '' D)),isOpen_interior⟩ =
      dirichletEigenvalue n ⟨interior (A '' D),isOpen_interior⟩ := by
  rw [affineBody_linear_translate_image]
  exact dirichletEigenvalue_interior_translated n (A '' D) (A z)

theorem dirichletEigenvalue_linear_body_antitone (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (L K : Set (EuclideanSpace ℝ (Fin n))) (hLK : L ⊆ K) :
    dirichletEigenvalue n ⟨interior (A '' K),isOpen_interior⟩ ≤
      dirichletEigenvalue n ⟨interior (A '' L),isOpen_interior⟩ := by
  apply dirichletEigenvalue_antitone
  exact interior_mono (image_mono hLK)

end AffineFKProof
