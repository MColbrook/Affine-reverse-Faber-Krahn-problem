module

public import AffineFK.GaussianPositionMilman

/-!
# The two main affine reverse Faber--Krahn theorems

The proved dimension-uniform ellipsoid intersection theorem supplies the
symmetric maximal-Gaussian-position estimate. The genuine affine
reduction gives the unrestricted convex-body conclusion. Both constants
precede all dimensions and bodies; no geometric or spectral result is
an additional hypothesis. The eigenvalue throughout is the actual H0
Rayleigh infimum, and the affine map is literally special-linear.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Set
open scoped ENNReal

theorem gaussian_reverse_faber_krahn :
    ∃ C : ℝ, 0 < C ∧ UniformSymmetricGaussianDirichletBound C := by
  obtain ⟨a,ha,hEllipsoid⟩ := gaussianPosition_uniform_volume_one_ellipsoid_intersection
  exact symmetric_gaussian_spectral_bound_of_ellipsoid_intersections a ha hEllipsoid

theorem affine_reverse_faber_krahn_main_theorems :
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → Convex ℝ K →
      (interior K).Nonempty → ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ,
        dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩ ≠ ∞ ∧
        (dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩).toReal *
          (volume K).toReal ^ ((2 : ℝ) / (n : ℝ)) ≤ C * (n : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ UniformSymmetricGaussianDirichletBound C) :=
  ⟨affine_reverse_faber_krahn,gaussian_reverse_faber_krahn⟩

end AffineFKProof
