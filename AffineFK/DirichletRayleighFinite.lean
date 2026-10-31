module

public import AffineFK.DirichletRayleigh
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Genuine nonzero Dirichlet tests and finite variational eigenvalue

Every nonempty open set has a compact smooth bump with value one at a
chosen point. Its actual L2 class is nonzero by continuity and full support
of Lebesgue volume. The resulting finite Rayleigh quotient bounds the true
H0^1 infimum. No eigenfunction or finiteness premise is assumed.

The finite-dimensional bump construction and positive-open-set measure
arguments are reused from Mathlib with their Apache-2.0 attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff ENNReal

def dirichletTestElement (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (φ : 𝓓(U, ℝ)) : dirichletSobolev n U := ⟨dirichletTestToH1 n U φ, dirichlet_test_mem n U φ⟩

theorem dirichletTestElement_value (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (φ : 𝓓(U, ℝ)) :
    (dirichletValue n U (dirichletTestElement n U φ) : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] φ := by
  change unweightedTestToL2 n (dirichletTestToTop n U φ) =ᵐ[volume] φ
  exact unweightedTestToL2_coe n _

theorem dirichletTestElement_gradient (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (φ : 𝓓(U, ℝ)) :
    (dirichletGradient n U (dirichletTestElement n U φ) :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume] gradient φ := by
  change unweightedTestToL2 n (testFunctionGradient (dirichletTestToTop n U φ)) =ᵐ[volume] gradient φ
  exact (unweightedTestToL2_coe n _).trans
    (Filter.Eventually.of_forall fun x => testFunctionGradient_apply _ x)

theorem dirichletTestElement_value_ne_zero (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (φ : 𝓓(U, ℝ)) (x : EuclideanSpace ℝ (Fin n)) (hx : φ x ≠ 0) :
    dirichletValue n U (dirichletTestElement n U φ) ≠ 0 := by
  intro hzero
  have hAE := dirichletTestElement_value n U φ
  have hz : (φ : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] (fun _ => 0) := by
    have hc := (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))))
    rw [hzero] at hAE
    exact hAE.symm.trans hc
  have hf : (φ : EuclideanSpace ℝ (Fin n) → ℝ) = fun _ => 0 :=
    (φ.continuous.ae_eq_iff_eq (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) continuous_const).mp hz
  exact hx (congrFun hf x)

theorem dirichlet_exists_nonzero_test (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))).Nonempty) :
    ∃ φ : 𝓓(U, ℝ), dirichletValue n U (dirichletTestElement n U φ) ≠ 0 := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨f, hs, hcompact, hf, _hrange, hfx⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (U.isOpen.mem_nhds hx)
  let φ : 𝓓(U, ℝ) := ⟨f, hf, hcompact, hs⟩
  exact ⟨φ, dirichletTestElement_value_ne_zero n U φ x
    (by change f x ≠ 0; rw [hfx]; exact one_ne_zero)⟩

theorem dirichletEigenvalue_ne_top (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))).Nonempty) : dirichletEigenvalue n U ≠ ⊤ := by
  obtain ⟨φ, hφ⟩ := dirichlet_exists_nonzero_test n U hU
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (dirichletEigenvalue_le_rayleigh n U (dirichletTestElement n U φ) hφ)

end AffineFKProof
