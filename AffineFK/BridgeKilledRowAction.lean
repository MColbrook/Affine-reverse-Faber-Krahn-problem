module

public import AffineFK.BridgeKilledRowInner
public import AffineFK.BridgeKilledL2Representatives

/-!
# The actual killed semigroup acting on its density rows

Every Bochner integral used here has the previously proved row-L1
integrability. The value is obtained from the particular pointwise
composition formula and therefore holds at every start.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem bridgeKilledIntegral_eq_density_integral (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledIntegral n t ht Ω hΩ f x =
      ∫ y, (bridgeKilledKernel n t x Ω y).toReal * f y ∂volume := by
  rw [bridgeKilledIntegral, bridgeKilledTransitionKernel_eq_withDensity]
  simpa only [smul_eq_mul] using integral_withDensity_eq_integral_toReal_smul
    (bridgeKilledKernel_measurable n t x Ω hΩ)
    (Filter.Eventually.of_forall fun y => lt_top_iff_ne_top.mpr
      (bridgeKilledKernel_ne_top n t x y Ω)) f

theorem bridgeKilledIntegral_row (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (x z : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledIntegral n s hs Ω hΩ
      (fun y => (bridgeKilledKernel n t x Ω y).toReal) z =
        (bridgeKilledKernel n (s+t) x Ω z).toReal := by
  rw [bridgeKilledIntegral_eq_density_integral,
    bridgeKilledKernel_row_product_integral n s t hs ht z x Ω hΩ,
    bridgeKilledKernel_symmetric n (s+t) (add_pos hs ht) z x Ω hΩ]

theorem bridgeKilledIntegral_row_integrable (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (x z : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => (bridgeKilledKernel n t x Ω y).toReal)
      (bridgeKilledTransitionKernel n s hs Ω hΩ z) :=
  (bridge_memLp_killed_row n s hs Ω hΩ _
    (bridgeKilledKernel_row_memLp_and_square n t ht x Ω hΩ).1 z).integrable (by norm_num)

end AffineFKProof
