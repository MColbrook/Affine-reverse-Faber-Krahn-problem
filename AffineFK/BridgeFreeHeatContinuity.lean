module

public import AffineFK.BridgeFreeHeatSobolev
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong zero-time continuity of the actual free Gaussian heat kernel

On compact smooth inputs, dominated convergence gives pointwise heat
convergence and convergence of the actual L2 self-pairing. The genuine
L2 contraction turns this into strong convergence. Compact smooth L2
density then removes all regularity assumptions on the input.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology Distributions RealInnerProductSpace

theorem bridgeFreeHeatAverage_test_tendsto (n : ℕ)
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (𝓝 0))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => bridgeFreeHeatAverage n (τ k) φ x) atTop (𝓝 (φ x)) := by
  obtain ⟨C, _, hC⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff 0
  have hb (y) : ‖φ y‖ ≤ C := by simpa only [norm_iteratedFDeriv_zero] using hC 0 le_rfl y
  have hs : Tendsto (fun k => Real.sqrt (τ k)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.tendsto 0 |>.comp hτ
  have h := tendsto_integral_filter_of_dominated_convergence (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))
    (bound := fun _ => C) (F := fun k u => φ (x + Real.sqrt (τ k) • u)) (f := fun _ => φ x)
    (Eventually.of_forall fun k => (φ.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun k => Eventually.of_forall fun u => hb _)
    (integrable_const _)
    (Eventually.of_forall fun u => by
      have ha : Tendsto (fun k => x + Real.sqrt (τ k) • u) atTop (𝓝 x) := by
        simpa only [zero_smul, add_zero] using
          (tendsto_const_nhds (x := x)).add (hs.smul (tendsto_const_nhds (x := u)))
      exact φ.continuous.continuousAt.tendsto.comp ha)
  simpa only [bridgeFreeHeatAverage, integral_const, probReal_univ, one_smul] using h

theorem bridgeFreeHeatAverage_test_bound (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (C : ℝ) (hC : ∀ y, ‖φ y‖ ≤ C) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖bridgeFreeHeatAverage n t φ x‖ ≤ C := by
  have hi : Integrable (fun u => φ (x + Real.sqrt t • u))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    (integrable_const C).mono' (φ.continuous.comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => hC _)
  calc
    _ ≤ ∫ u, ‖φ (x + Real.sqrt t • u)‖ ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _u, C ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      integral_mono hi.norm (integrable_const _) (fun _ => hC _)
    _ = C := by simp

end AffineFKProof
