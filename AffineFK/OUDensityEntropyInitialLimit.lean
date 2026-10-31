module

public import AffineFK.OUEntropyInitialLimit
public import AffineFK.StandardGaussianDensity

/-!
# The OU initial entropy endpoint for arbitrary Lebesgue densities

The proved actual Gaussian density is everywhere positive. Consequently
absolute continuity with respect to Lebesgue volume implies absolute
continuity with respect to the standard Gaussian. No continuity,
smoothness, finite entropy or logarithmic-density bound is required.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped Topology ENNReal

theorem ouInitial_volume_absolutelyContinuous_stdGaussian (n : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) ≪
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [stdGaussian_eq_densityMeasure, densityMeasure]
  apply withDensity_absolutelyContinuous'
  · exact (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal.aemeasurable
  · exact Filter.Eventually.of_forall fun x =>
      (ENNReal.ofReal_pos.mpr (standardGaussianDensity_pos n x)).ne'

theorem ouInitial_entropy_tendsto_of_volume_ac (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ volume) :
    Tendsto (fun t : ℝ => klDiv (ouInitialLaw n ν t)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))) (𝓝[>] 0)
      (𝓝 (klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))))) :=
  ouInitial_entropy_tendsto n ν (hac.trans (ouInitial_volume_absolutelyContinuous_stdGaussian n))

theorem ouInitial_density_entropy_tendsto (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    [IsProbabilityMeasure (densityMeasure n ρ)] :
    Tendsto (fun t : ℝ => klDiv (ouInitialLaw n (densityMeasure n ρ) t)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))) (𝓝[>] 0)
      (𝓝 (klDiv (densityMeasure n ρ) (stdGaussian (EuclideanSpace ℝ (Fin n))))) :=
  ouInitial_entropy_tendsto_of_volume_ac n (densityMeasure n ρ)
    (withDensity_absolutelyContinuous _ _)

end AffineFKProof
