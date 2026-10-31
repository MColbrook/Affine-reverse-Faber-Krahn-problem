module

public import AffineFK.WeightedSobolev
public import AffineFK.WeakPoisson
public import Mathlib.Probability.Moments.Variance

/-!
# Weak Poisson equations in the weighted Sobolev completion

The Poincare premise is the actual centred-square integral inequality for
compactly supported smooth test functions. It is extended to the genuine
closed mean-zero H1 graph, whose completeness has been proved, before applying
Lax--Milgram. Constants and coordinates in H1 and weak-derivative identification
remain separate assertions.

The variance identities are reused from Mathlib's probability moments library;
Lax--Milgram and the Hilbert graph construction are credited in the imported
proof modules.
-/

public section
namespace AffineFKProof
open MeasureTheory TopologicalSpace ProbabilityTheory
open scoped Distributions RealInnerProductSpace

/-- The usual integral Poincare premise gives exactly the graph-norm
inequality used in the H1 completion, with the same constant. -/
theorem test_poincare_graph_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsProbabilityMeasure ν] (P : ℝ)
    (hP : ∀ f : 𝓓((⊤ : Opens E), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν)) :
    ∀ f : 𝓓((⊤ : Opens E), ℝ),
      ‖testFunctionToL2 ν f‖ ^ 2 - (l2Mean ν (testFunctionToL2 ν f)) ^ 2 ≤
        P * ‖testFunctionToL2 ν (testFunctionGradient f)‖ ^ 2 := by
  intro f
  have hf : MemLp (f : E → ℝ) 2 ν :=
    (memLp_congr_ae (testFunctionToL2_coe ν f)).mp (Lp.memLp _)
  have hcenter : (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) =
      (∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 :=
    (variance_eq_integral hf.aemeasurable).symm.trans (variance_eq_sub hf)
  simp_rw [testFunctionToL2_norm_sq, testFunctionToL2_mean,
    testFunctionGradient_apply, Real.norm_eq_abs, sq_abs]
  rw [← hcenter]
  exact hP f

/-- The actual mean-zero weighted H1 completion has a unique weak Poisson
solution for every L2 source, and the exact energy bound P times its squared
L2 norm. No Sobolev-space completeness or solution-existence premise is assumed. -/
theorem weighted_poisson_solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsProbabilityMeasure ν] (P : ℝ) (hPnonneg : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens E), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (g : Lp ℝ 2 ν) :
    ∃! u : weightedSobolevMeanZero ν,
      (∀ v : weightedSobolevMeanZero ν,
        ⟪meanZeroGradient ν u, meanZeroGradient ν v⟫ = ⟪g, meanZeroValue ν v⟫) ∧
      ‖meanZeroGradient ν u‖ ^ 2 ≤ P * ‖g‖ ^ 2 := by
  have htest := test_poincare_graph_bound ν P hP
  exact weak_gradient_solution_nested_submodule (weightedSobolevGraph ν) (weightedSobolevMeanZero ν)
    (meanZeroValue ν) (meanZeroGradient ν) P hPnonneg (meanZero_graph_norm_sq ν)
    (meanZero_poincare ν P htest) g

end AffineFKProof
