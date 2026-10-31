module

public import AffineFK.DirichletTranslationTransport
public import AffineFK.DirichletScalarEigenvalue
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Literal body-interior forms of Dirichlet translation and dilation

The eigenvalue remains the genuine H0 Rayleigh infimum. These corollaries
apply the proved open-domain identities to the literal interior of the
translated or dilated set, using the actual homeomorphism theorem for
interiors. No convexity, boundedness or boundary hypothesis is necessary.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Set
open scoped ENNReal Pointwise

theorem dirichletEigenvalue_interior_translated (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    dirichletEigenvalue n ⟨interior ((fun x => x+z) '' D),isOpen_interior⟩ =
      dirichletEigenvalue n ⟨interior D,isOpen_interior⟩ := by
  have hU : (⟨interior ((fun x => x+z) '' D),isOpen_interior⟩ :
      Opens (EuclideanSpace ℝ (Fin n))) =
      dirichletTranslatedOpen n ⟨interior D,isOpen_interior⟩ z := by
    apply SetLike.coe_injective
    change interior ((fun x => x+z) '' D) =
      (dirichletTranslatedOpen n ⟨interior D,isOpen_interior⟩ z : Set _)
    rw [dirichletTranslatedOpen_coe]
    exact ((Homeomorph.addRight z).image_interior D).symm
  rw [hU]
  exact dirichletEigenvalue_translated n ⟨interior D,isOpen_interior⟩ z

theorem dirichletEigenvalue_interior_scalar (n : ℕ) (hn : 0 < n)
    (D : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ) (hr : 0 < r) :
    dirichletEigenvalue n ⟨interior (r • D),isOpen_interior⟩ =
      ENNReal.ofReal ((r^2)⁻¹) * dirichletEigenvalue n ⟨interior D,isOpen_interior⟩ := by
  have hU : (⟨interior (r • D),isOpen_interior⟩ :
      Opens (EuclideanSpace ℝ (Fin n))) =
      dirichletScalarImage n r hr ⟨interior D,isOpen_interior⟩ := by
    apply SetLike.coe_injective
    change interior (r • D) =
      (dirichletScalarImage n r hr ⟨interior D,isOpen_interior⟩ : Set _)
    rw [dirichletScalarImage_coe]
    exact interior_smul₀ hr.ne' D
  rw [hU]
  exact dirichletEigenvalue_scalar_image n hn ⟨interior D,isOpen_interior⟩ r hr

end AffineFKProof
