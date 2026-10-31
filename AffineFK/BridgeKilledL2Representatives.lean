module

public import AffineFK.BridgeKilledL2Contraction

/-!
# The killed Brownian L2 estimate is independent of representatives

Every actual transition row is absolutely continuous with respect to
Lebesgue measure. Equality of inputs almost everywhere therefore gives
equality of their row integrals at every start. Borel representatives
remove the extra measurability presentation from the quadratic estimate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem bridgeKilledTransitionKernel_absolutelyContinuous_volume (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) (x : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledTransitionKernel n T hT Ω hΩ x ≪ volume := by
  rw [bridgeKilledTransitionKernel_eq_withDensity n T hT Ω hΩ x]
  exact withDensity_absolutelyContinuous volume _

theorem bridgeKilledIntegral_congr_ae_input (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hfg : f =ᵐ[volume] g) :
    bridgeKilledIntegral n T hT Ω hΩ f = bridgeKilledIntegral n T hT Ω hΩ g := by
  funext x
  exact integral_congr_ae (hfg.filter_mono
    (bridgeKilledTransitionKernel_absolutelyContinuous_volume n T hT Ω hΩ x).ae_le)

theorem bridgeKilledIntegral_memLp_and_sq_bound_of_memLp (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemLp f 2 volume) :
    MemLp (bridgeKilledIntegral n T hT Ω hΩ f) 2 volume ∧
      (∫ x, (bridgeKilledIntegral n T hT Ω hΩ f x)^2 ∂volume) ≤ ∫ y, (f y)^2 ∂volume := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hgm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hg : MemLp g 2 volume := hf.ae_eq hfg
  have hout := bridgeKilledIntegral_memLp_and_sq_bound n T hT Ω hΩ g hgm hg
  have hP := bridgeKilledIntegral_congr_ae_input n T hT Ω hΩ f g hfg
  have hsq : (∫ y, (f y)^2 ∂volume) = ∫ y, (g y)^2 ∂volume :=
    integral_congr_ae (hfg.fun_comp (fun z : ℝ => z^2))
  rw [hP, hsq]
  exact hout

end AffineFKProof
