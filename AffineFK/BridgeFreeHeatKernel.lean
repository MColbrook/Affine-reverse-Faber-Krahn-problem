module

public import AffineFK.BridgeKilledRowAction

/-!
# The free kernel is actual Gaussian translation averaging

For the unrestricted domain the killing event is the whole probability
space. Haar scaling identifies the resulting transition law with the
actual image of a standard Gaussian vector, in every finite dimension.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem bridgeKilledKernel_univ (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x y : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledKernel n t x univ y = ENNReal.ofReal (bridgeFreeHeatDensity n t x y) := by
  rw [bridgeKilledKernel_bridge_formula n t ht x y univ]
  simp

theorem bridgeFreeHeatDensity_gaussian_map (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun u => x + Real.sqrt t • u) =
      volume.withDensity (fun y => ENNReal.ofReal (bridgeFreeHeatDensity n t x y)) := by
  rw [stdGaussian_eq_densityMeasure]
  change (volume.withDensity (fun y => ENNReal.ofReal (standardGaussianDensity n y))).map _ = _
  rw [bridge_affine_density_map n (Real.sqrt t) (Real.sqrt_pos.mpr ht) x _
    (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal]
  congr 1
  funext y
  rw [bridgeFreeHeatDensity, ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.sqrt t ^ n)⁻¹)]

theorem bridgeKilledTransitionKernel_univ (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledTransitionKernel n t ht univ isOpen_univ x =
      (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun u => x + Real.sqrt t • u) := by
  rw [bridgeKilledTransitionKernel_eq_withDensity, bridgeFreeHeatDensity_gaussian_map n t ht x]
  congr 1
  exact funext (bridgeKilledKernel_univ n t ht x)

theorem bridgeKilledIntegral_univ (n : ℕ) (t : ℝ) (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : AEStronglyMeasurable f volume) (x : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledIntegral n t ht univ isOpen_univ f x =
      ∫ u, f (x + Real.sqrt t • u) ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [bridgeKilledIntegral, bridgeKilledTransitionKernel_univ]
  apply integral_map (by fun_prop)
  rw [bridgeFreeHeatDensity_gaussian_map n t ht x]
  exact hf.mono_ac (withDensity_absolutelyContinuous volume _)

theorem bridgeFreeHeat_integrable_translate (n : ℕ) (t : ℝ) (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemLp f 2 volume)
    (x : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun u => f (x + Real.sqrt t • u)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hr := bridge_memLp_killed_row n t ht univ isOpen_univ f hf x
  rw [bridgeKilledTransitionKernel_univ] at hr
  exact hr.comp_measurePreserving
    (MeasureTheory.MeasurePreserving.mk (by fun_prop) rfl)

end AffineFKProof
