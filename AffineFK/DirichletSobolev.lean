module

public import AffineFK.UnweightedSobolevIntegration

/-!
# The actual zero-boundary Sobolev space on an open set

H0^1(U) is the closure of genuine compact smooth tests supported inside U,
in the already proved unweighted value-gradient H1 Hilbert space over
Lebesgue volume. Thus its functions and gradients are actual L2 classes;
the value map is injective. This is the variational domain in the paper,
with zero extension already built into its global compact-test closure.

Mathlib's compact test functions are due to Luigi Massacci and Anatole
Dedecker; its Lp, submodule and closure results retain their Apache-2.0
contributor attribution through the imported modules.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions

def dirichletTestToTop (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    𝓓(U, ℝ) →ₗ[ℝ] 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) where
  toFun φ := ⟨φ, φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

theorem dirichletTestToTop_apply (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (φ : 𝓓(U, ℝ)) (x : EuclideanSpace ℝ (Fin n)) : dirichletTestToTop n U φ x = φ x := rfl

def dirichletTestToH1 (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    𝓓(U, ℝ) →ₗ[ℝ] unweightedSobolevGraph n :=
  (((unweightedSmoothPair n).comp (dirichletTestToTop n U)).codRestrict
    (unweightedSobolevGraph n) (fun _φ => unweighted_smooth_pair_mem n _))

/-- The genuine compact-smooth closure defining H0^1(U), as a closed subspace of H1. -/
def dirichletSobolev (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (unweightedSobolevGraph n) := (dirichletTestToH1 n U).range.topologicalClosure

theorem dirichletSobolev_isClosed (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    IsClosed (dirichletSobolev n U : Set (unweightedSobolevGraph n)) :=
  Submodule.isClosed_topologicalClosure _

instance dirichletSobolev_completeSpace (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    CompleteSpace (dirichletSobolev n U) := (dirichletSobolev_isClosed n U).completeSpace_coe

def dirichletValue (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    dirichletSobolev n U →L[ℝ] Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (unweightedValue n).comp (dirichletSobolev n U).subtypeL

def dirichletGradient (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    dirichletSobolev n U →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (unweightedGradient n).comp (dirichletSobolev n U).subtypeL

theorem dirichletValue_injective (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    Function.Injective (dirichletValue n U) := by
  intro v w h
  exact Subtype.ext (unweighted_sobolev_value_injective n h)

theorem dirichlet_test_mem (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (φ : 𝓓(U, ℝ)) : dirichletTestToH1 n U φ ∈ dirichletSobolev n U :=
  (dirichletTestToH1 n U).range.le_topologicalClosure ⟨φ, rfl⟩

theorem dirichletSobolev_mono (n : ℕ) (U V : Opens (EuclideanSpace ℝ (Fin n)))
    (hUV : U ≤ V) : dirichletSobolev n U ≤ dirichletSobolev n V := by
  apply Submodule.topologicalClosure_mono
  rintro _ ⟨φ, rfl⟩
  let ψ : 𝓓(V, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hUV⟩
  exact ⟨ψ, rfl⟩

def dirichletInclusion (n : ℕ) (U V : Opens (EuclideanSpace ℝ (Fin n)))
    (hUV : U ≤ V) : dirichletSobolev n U →L[ℝ] dirichletSobolev n V :=
  (Submodule.inclusion (dirichletSobolev_mono n U V hUV)).mkContinuous 1 (fun v => by
    change ‖v‖ ≤ 1 * ‖v‖
    simp)

theorem dirichletInclusion_value (n : ℕ) (U V : Opens (EuclideanSpace ℝ (Fin n)))
    (hUV : U ≤ V) (v : dirichletSobolev n U) :
    dirichletValue n V (dirichletInclusion n U V hUV v) = dirichletValue n U v := rfl

theorem dirichletInclusion_gradient (n : ℕ) (U V : Opens (EuclideanSpace ℝ (Fin n)))
    (hUV : U ≤ V) (v : dirichletSobolev n U) :
    dirichletGradient n V (dirichletInclusion n U V hUV v) = dirichletGradient n U v := rfl

end AffineFKProof
