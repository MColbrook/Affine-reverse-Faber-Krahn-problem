module

public import AffineFK.BridgeStartedBrownian
public import AffineFK.BridgeAffineDensityMap
public import AffineFK.GaussianReferenceScore

/-!
# Explicit killed Brownian endpoint kernels from every start and positive time

The reference law is the actual finite-horizon continuous Brownian law.
The pointwise bridge density is fixed explicitly, including its diagonal.
Haar change of variables supplies the full sqrt(T) Jacobian; no density or
semigroup assertion is assumed. The later Dirichlet spectral identification
must refer to this specific kernel and remains separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

def bridgeFreeHeatDensity (n : ℕ) (T : ℝ) (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ((Real.sqrt T ^ n)⁻¹) * standardGaussianDensity n ((Real.sqrt T)⁻¹ • (y - x))

def bridgeKilledKernel (n : ℕ) (T : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (y : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt T ^ n)⁻¹) *
    bridgeKilledEndpointDensity n (bridgeStartPullbackDomain n T x Ω)
      ((Real.sqrt T)⁻¹ • (y - x))

theorem bridgeKilledKernel_measurable (n : ℕ) (T : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    Measurable (bridgeKilledKernel n T x Ω) :=
  measurable_const.mul ((bridgeKilledEndpointDensity_measurable n _
    (bridgeStartPullbackDomain_isOpen n T x Ω hΩ)).comp (by fun_prop))

theorem bridgeStartedKilledEndpointMeasure_eq_withDensity (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeStartedKilledEndpointMeasure n T hT x Ω =
      volume.withDensity (bridgeKilledKernel n T x Ω) := by
  rw [bridgeStartedKilledEndpointMeasure_eq_map_unit n T hT x Ω hΩ,
    bridgeKilledEndpointMeasure_eq_volume_withDensity n _
      (bridgeStartPullbackDomain_isOpen n T x Ω hΩ)]
  exact bridge_affine_density_map n (Real.sqrt T) (Real.sqrt_pos.mpr hT) x _
    (bridgeKilledEndpointDensity_measurable n _ (bridgeStartPullbackDomain_isOpen n T x Ω hΩ))

theorem bridgeKilledKernel_bridge_formula (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x y : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    bridgeKilledKernel n T x Ω y = ENNReal.ofReal (bridgeFreeHeatDensity n T x y) *
      bridgeSeriesLaw n {f | ∀ u : Icc (0 : ℝ) 1,
        x + Real.sqrt T • f u + (u : ℝ) • (y - x) ∈ Ω} := by
  have hc : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  have heq : {f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) |
      ∀ u : Icc (0 : ℝ) 1, f u + (u : ℝ) • ((Real.sqrt T)⁻¹ • (y - x)) ∈
        bridgeStartPullbackDomain n T x Ω} =
      {f | ∀ u : Icc (0 : ℝ) 1, x + Real.sqrt T • f u + (u : ℝ) • (y - x) ∈ Ω} := by
    ext f
    apply forall_congr'
    intro u
    change (x + Real.sqrt T • (f u + (u : ℝ) • ((Real.sqrt T)⁻¹ • (y - x))) ∈ Ω) ↔ _
    simp only [smul_add, smul_smul]
    rw [show Real.sqrt T * ((u : ℝ) * (Real.sqrt T)⁻¹) = (u : ℝ) by field_simp]
    rw [add_assoc]
  rw [bridgeKilledKernel, bridgeKilledEndpointDensity, bridgeKilledSurvivalProbability, heq]
  rw [bridgeFreeHeatDensity, ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.sqrt T ^ n)⁻¹), mul_assoc]

theorem bridge_sqrt_jacobian (n : ℕ) (T : ℝ) (hT : 0 < T) :
    (Real.sqrt T ^ n)⁻¹ = T ^ (-(n : ℝ) / 2) := by
  calc
    _ = (Real.sqrt T) ^ (-(n : ℝ)) := by
      rw [Real.rpow_neg (Real.sqrt_nonneg T), Real.rpow_natCast]
    _ = (T ^ (1 / 2 : ℝ)) ^ (-(n : ℝ)) := by rw [Real.sqrt_eq_rpow]
    _ = _ := by
      rw [← Real.rpow_mul hT.le]
      congr 1
      ring

theorem bridgeFreeHeatDensity_diagonal (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) :
    bridgeFreeHeatDensity n T x x = (2 * Real.pi * T) ^ (-(n : ℝ) / 2) := by
  simp only [bridgeFreeHeatDensity, sub_self, smul_zero, standardGaussianDensity_zero]
  rw [bridge_sqrt_jacobian n T hT, ← Real.mul_rpow hT.le (by positivity : 0 ≤ 2 * Real.pi)]
  congr 1
  ring

theorem bridgeKilledKernel_diagonal (n : ℕ) (T : ℝ) (hT : 0 < T)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    bridgeKilledKernel n T x Ω x =
      ENNReal.ofReal ((2 * Real.pi * T) ^ (-(n : ℝ) / 2)) *
        bridgeSeriesLaw n {f | ∀ u : Icc (0 : ℝ) 1, x + Real.sqrt T • f u ∈ Ω} := by
  rw [bridgeKilledKernel_bridge_formula n T hT x x Ω, bridgeFreeHeatDensity_diagonal n T hT x]
  simp only [sub_self, smul_zero, add_zero]

theorem bridgeKilledKernel_le_free (n : ℕ) (T : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    bridgeKilledKernel n T x Ω y ≤ ENNReal.ofReal (bridgeFreeHeatDensity n T x y) := by
  rw [bridgeKilledKernel, bridgeFreeHeatDensity,
    ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.sqrt T ^ n)⁻¹)]
  exact mul_le_mul_right (bridgeKilledEndpointDensity_le_free n _ _) _

end AffineFKProof
