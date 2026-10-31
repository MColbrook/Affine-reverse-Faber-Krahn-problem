module

public import AffineFK.GaussianIntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Coordinate slices of compact smooth tests

The coordinate product space carries its usual finite product norm. A
coordinate slice is a genuine compact smooth real test: compact support
follows from the closed embedding of the coordinate line. This is the
test-function step used in finite-product Gaussian integration by parts.
The underlying coordinate derivative lemmas are due to Floris van Doorn
and Heather Macbeth in Mathlib.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions

def piPartialTest (n : ℕ) (j : Fin n)
    (φ : 𝓓((⊤ : Opens (Fin n → ℝ)), ℝ)) : 𝓓((⊤ : Opens (Fin n → ℝ)), ℝ) :=
  TestFunction.lineDerivCLM ℝ (Pi.single j (1 : ℝ)) φ

theorem piPartialTest_fderiv (n : ℕ) (j : Fin n)
    (φ : 𝓓((⊤ : Opens (Fin n → ℝ)), ℝ)) (x : Fin n → ℝ) :
    piPartialTest n j φ x = fderiv ℝ φ x (Pi.single j (1 : ℝ)) := by
  change (TestFunction.fderivCLM ℝ ⊤ ⊤ φ) x (Pi.single j (1 : ℝ)) = _
  rw [TestFunction.fderivCLM_apply_of_le φ (by simp)]

def coordinateSliceTest (n : ℕ) (j : Fin n) (x : Fin n → ℝ)
    (φ : 𝓓((⊤ : Opens (Fin n → ℝ)), ℝ)) : 𝓓((⊤ : Opens ℝ), ℝ) :=
  ⟨fun s => φ (Function.update x j s),
    φ.contDiff.comp (contDiff_update _ x j),
    φ.hasCompactSupport.comp_isClosedEmbedding (isClosedEmbedding_update x j),
    Set.subset_univ _⟩

theorem realDerivativeTest_coordinateSlice (n : ℕ) (j : Fin n) (x : Fin n → ℝ)
    (φ : 𝓓((⊤ : Opens (Fin n → ℝ)), ℝ)) (s : ℝ) :
    realDerivativeTest (coordinateSliceTest n j x φ) s =
      piPartialTest n j φ (Function.update x j s) := by
  have hd := ((φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt
    s (hasDerivAt_update x j s)
  have hfd := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hd.hasFDerivAt.fderiv
  have hcomp : (φ : (Fin n → ℝ) → ℝ) ∘ Function.update x j =
      (coordinateSliceTest n j x φ : ℝ → ℝ) := by
    funext t
    rfl
  rw [hcomp] at hfd
  rw [realDerivativeTest_fderiv, piPartialTest_fderiv]
  simpa only [ContinuousLinearMap.toSpanSingleton_apply_one] using hfd

end AffineFKProof
