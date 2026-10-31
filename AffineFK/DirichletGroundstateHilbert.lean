module

public import AffineFK.DirichletSobolev
public import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# The inherited Dirichlet Hilbert structure with its existing scalar action

The inner product is the ambient H1 inner product restricted to H0^1.
Keeping the existing NormedSpace field explicit avoids comparing two
deeply expanded induced scalar structures when applying Hilbert lemmas.
Every compatibility field is a proved ambient inner-product identity.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open TopologicalSpace InnerProductSpace
open scoped RealInnerProductSpace

def dirichletGroundstateInnerProductSpace (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) : InnerProductSpace ℝ (dirichletSobolev n U) where
  toNormedSpace := inferInstance
  inner x y := ⟪(x : unweightedSobolevGraph n), (y : unweightedSobolevGraph n)⟫
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (x : unweightedSobolevGraph n)
  conj_inner_symm x y := inner_conj_symm (x : unweightedSobolevGraph n) (y : unweightedSobolevGraph n)
  add_left x y z := inner_add_left (x : unweightedSobolevGraph n)
    (y : unweightedSobolevGraph n) (z : unweightedSobolevGraph n)
  smul_left x y r := inner_smul_left (x : unweightedSobolevGraph n)
    (y : unweightedSobolevGraph n) r

end AffineFKProof
