module

public import AffineFK.BridgeAffineSurvivalProbability
public import AffineFK.BridgeGaussianMiddleDensity

/-!
# Pointwise composition of the particular killed bridge density

The proved actual full bridge splitting law, product-event integration and
exact Gaussian middle density give the equality at every endpoint pair.
It is not an almost-everywhere Radon--Nikodym argument and therefore also
identifies the already selected diagonal version.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem bridgeFreeHeatDensity_nonneg (n : ℕ) (T : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : 0 ≤ bridgeFreeHeatDensity n T x y :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg T) n))
    (standardGaussianDensity_pos n _).le

theorem bridgeAffineSurvivalProbability_middle_density (n : ℕ) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (x z : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeAffineSurvivalProbability n (s+t) x Ω z =
      ∫⁻ y, ENNReal.ofReal (bridgeFreeHeatDensity n (s*t/(s+t)) (bridgeGaussianMiddleMean n s t x z) y) *
        (bridgeAffineSurvivalProbability n s x Ω y * bridgeAffineSurvivalProbability n t y Ω z) ∂volume := by
  let F : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun y =>
    bridgeAffineSurvivalProbability n s x Ω y * bridgeAffineSurvivalProbability n t y Ω z
  have hleft : Measurable (fun y : EuclideanSpace ℝ (Fin n) => (x,y)) :=
    measurable_const.prodMk measurable_id
  have hright : Measurable (fun y : EuclideanSpace ℝ (Fin n) => (y,z)) :=
    measurable_id.prodMk measurable_const
  have hFs := (bridgeAffineSurvivalProbability_joint_measurable n s Ω hΩ).comp hleft
  have hFt := (bridgeAffineSurvivalProbability_joint_measurable n t Ω hΩ).comp hright
  have hF0 := hFs.mul hFt
  have hF : Measurable F := hF0
  have hD : Measurable (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      (bridgeFreeHeatDensity n (s*t/(s+t)) (bridgeGaussianMiddleMean n s t x z) y)) := by
    unfold bridgeFreeHeatDensity standardGaussianDensity
    fun_prop
  calc
    _ = ∫⁻ w, F (bridgeSplitMiddlePoint n s t x z w) ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      bridgeAffineSurvivalProbability_middle_factorization n s t hs ht x z Ω hΩ
    _ = ∫⁻ y, F y ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).map
        (bridgeSplitMiddlePoint n s t x z) :=
      (lintegral_map hF (bridgeSplitMiddlePoint_measurable n s t x z)).symm
    _ = ∫⁻ y, F y ∂volume.withDensity (fun y => ENNReal.ofReal
        (bridgeFreeHeatDensity n (s*t/(s+t)) (bridgeGaussianMiddleMean n s t x z) y)) := by
      rw [(bridgeSplitMiddlePoint_hasLaw_density n s t hs ht x z).map_eq]
    _ = _ := lintegral_withDensity_eq_lintegral_mul volume hD hF

theorem bridgeKilledKernel_pointwise_semigroup (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x z : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeKilledKernel n (s+t) x Ω z =
      ∫⁻ y, bridgeKilledKernel n s x Ω y * bridgeKilledKernel n t y Ω z ∂volume := by
  rw [bridgeKilledKernel_bridge_formula n (s+t) (add_pos hs ht) x z Ω]
  change ENNReal.ofReal (bridgeFreeHeatDensity n (s+t) x z) *
    bridgeAffineSurvivalProbability n (s+t) x Ω z = _
  rw [bridgeAffineSurvivalProbability_middle_density n s t hs ht x z Ω hΩ]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro y
  rw [bridgeKilledKernel_bridge_formula n s hs x y Ω,
    bridgeKilledKernel_bridge_formula n t ht y z Ω]
  change ENNReal.ofReal (bridgeFreeHeatDensity n (s+t) x z) *
    (ENNReal.ofReal (bridgeFreeHeatDensity n (s*t/(s+t)) (bridgeGaussianMiddleMean n s t x z) y) *
      (bridgeAffineSurvivalProbability n s x Ω y * bridgeAffineSurvivalProbability n t y Ω z)) =
    (ENNReal.ofReal (bridgeFreeHeatDensity n s x y) * bridgeAffineSurvivalProbability n s x Ω y) *
      (ENNReal.ofReal (bridgeFreeHeatDensity n t y z) * bridgeAffineSurvivalProbability n t y Ω z)
  have hfree : ENNReal.ofReal (bridgeFreeHeatDensity n (s+t) x z) *
      ENNReal.ofReal (bridgeFreeHeatDensity n (s*t/(s+t)) (bridgeGaussianMiddleMean n s t x z) y) =
      ENNReal.ofReal (bridgeFreeHeatDensity n s x y) * ENNReal.ofReal (bridgeFreeHeatDensity n t y z) := by
    rw [← ENNReal.ofReal_mul (bridgeFreeHeatDensity_nonneg n (s+t) x z),
      ← ENNReal.ofReal_mul (bridgeFreeHeatDensity_nonneg n s x y),
      bridge_free_heat_middle_product n s t hs ht x y z]
  calc
    _ = (ENNReal.ofReal (bridgeFreeHeatDensity n (s+t) x z) *
      ENNReal.ofReal (bridgeFreeHeatDensity n (s*t/(s+t)) (bridgeGaussianMiddleMean n s t x z) y)) *
        (bridgeAffineSurvivalProbability n s x Ω y * bridgeAffineSurvivalProbability n t y Ω z) := by ring
    _ = _ := by rw [hfree]; ring

end AffineFKProof
