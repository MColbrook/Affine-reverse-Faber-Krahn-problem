module

public import AffineFK.BridgeKilledEndpoint
public import AffineFK.BridgeSeriesSurvival
public import AffineFK.StandardGaussianDensity

/-!
# An explicit Lebesgue density and its fixed diagonal value

The density is a specific pointwise bridge formula, not an arbitrary
Radon--Nikodym representative. It is a genuine density of the terminal
image of the survival-restricted Brownian path law, from origin at time
one. Its diagonal value therefore retains the exact bridge probability.
The identification with a variational Dirichlet heat kernel is separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

def bridgeKilledEndpointDensity (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal (standardGaussianDensity n z) * bridgeKilledSurvivalProbability n Ω z

theorem bridgeKilledEndpointDensity_measurable (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    Measurable (bridgeKilledEndpointDensity n Ω) :=
  (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal.mul
    (bridgeKilledSurvivalProbability_measurable n Ω hΩ)

theorem bridgeKilledEndpointMeasure_eq_volume_withDensity (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeKilledEndpointMeasure n Ω =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (bridgeKilledEndpointDensity n Ω) := by
  rw [bridgeKilledEndpointMeasure_eq_gaussian_withDensity n Ω hΩ, stdGaussian_eq_densityMeasure]
  unfold densityMeasure bridgeKilledEndpointDensity
  exact (withDensity_mul volume
    (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal
      (bridgeKilledSurvivalProbability_measurable n Ω hΩ)).symm

theorem bridgeKilledEndpointDensity_diagonal (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    bridgeKilledEndpointDensity n Ω 0 = ENNReal.ofReal (standardGaussianDensity n 0) *
      bridgeSeriesLaw n (bridgeBrownianSurvivalSet n Ω) := by
  simp [bridgeKilledEndpointDensity, bridgeKilledSurvivalProbability, bridgeBrownianSurvivalSet]

theorem standardGaussianDensity_zero (n : ℕ) :
    standardGaussianDensity n 0 = (2 * Real.pi) ^ (-(n : ℝ) / 2) := by
  have htwo : 0 < 2 * Real.pi := by positivity
  have hsingle : gaussianPDFReal 0 1 0 = (2 * Real.pi) ^ (-(1 / 2 : ℝ)) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_self, zero_pow (by norm_num : 2 ≠ 0),
      neg_zero, zero_div, Real.exp_zero, mul_one]
    rw [Real.sqrt_eq_rpow, Real.rpow_neg htwo.le]
  calc
    _ = ((2 * Real.pi) ^ (-(1 / 2 : ℝ))) ^ n := by
      simp [standardGaussianDensity, hsingle]
    _ = _ := by
      rw [← Real.rpow_mul_natCast htwo.le]
      congr 1
      ring

theorem bridgeKilledEndpointDensity_diagonal_explicit (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    bridgeKilledEndpointDensity n Ω 0 =
      ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2)) *
        bridgeSeriesLaw n (bridgeBrownianSurvivalSet n Ω) := by
  rw [bridgeKilledEndpointDensity_diagonal, standardGaussianDensity_zero]

theorem bridgeKilledSurvivalProbability_le_one (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledSurvivalProbability n Ω z ≤ 1 := by
  exact (measure_mono (subset_univ _)).trans_eq (measure_univ : bridgeSeriesLaw n univ = 1)

theorem bridgeKilledEndpointDensity_le_free (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledEndpointDensity n Ω z ≤ ENNReal.ofReal (standardGaussianDensity n z) := by
  exact (mul_le_mul_right (bridgeKilledSurvivalProbability_le_one n Ω z)
    (ENNReal.ofReal (standardGaussianDensity n z))).trans_eq (mul_one _)

theorem bridgeKilledEndpointDensity_diagonal_lower
    (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D)
    (hconvex : Convex ℝ D) (hzero : 0 ∈ interior D)
    (p a A : ℝ) (hp : 2 < p) (ha : 1 / p < a) (hupper : a < 1 / 2) (hA : 0 ≤ A)
    (hprofile : ∀ t : ℝ, 1 ≤ t →
      -Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))) (t • D)).toReal ≤ A * t ^ (-p)) :
    ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
      Real.exp (-A / (1 - (2 : ℝ) ^ (1 - a * p)))) ≤
        bridgeKilledEndpointDensity n ((2 * bridgeRadius a) • interior D) 0 := by
  rw [bridgeKilledEndpointDensity_diagonal_explicit,
    ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi) ^ (-(n : ℝ) / 2))]
  exact mul_le_mul_right
    (bridgeSeriesSurvival_probability_lower n D hcompact hconvex hzero p a A hp ha hupper hA hprofile)
    (ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2)))

end AffineFKProof
