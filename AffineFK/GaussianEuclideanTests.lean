module

public import AffineFK.GaussianCoordinateTests
public import AffineFK.SteinTestIdentities

/-!
# Euclidean tests in coordinate-product form

The inverse of PiLp.continuousLinearEquiv transports actual Euclidean
test functions to the coordinate product. Its coordinate derivative is
exactly partialTest; no change of inner product or derivative scale occurs.
The finite-dimensional equivalence is Mathlib's PiLp construction.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions

def euclideanToPiTest (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (Fin n → ℝ)), ℝ) :=
  ⟨fun x => φ (WithLp.toLp 2 x),
    φ.contDiff.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff,
    φ.hasCompactSupport.comp_homeomorph (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm,
    Set.subset_univ _⟩

theorem piPartialTest_euclideanToPiTest (n : ℕ) (j : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (x : Fin n → ℝ) :
    piPartialTest n j (euclideanToPiTest n φ) x =
      partialTest n j φ (WithLp.toLp 2 x) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have hd := ((φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x e.hasFDerivAt
  rw [piPartialTest_fderiv, partialTest_fderiv]
  change fderiv ℝ (φ ∘ e) x (Pi.single j 1) = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  congr 1
  exact (EuclideanSpace.basisFun_apply (Fin n) ℝ j).symm

end AffineFKProof
