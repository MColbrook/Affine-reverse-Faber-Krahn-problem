module

public import AffineFK.WeightedTestIntegration
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The actual Euclidean standard Gaussian as a positive smooth density

Finite product integration identifies the coordinate-product density.
The volume-preserving PiLp equivalence then transports it to Mathlib's
actual stdGaussian. This fixes the reference measure in the score formula.
The product integration and volume transport results are due to Xavier
Roblot and Sebastien Gouezel in Mathlib (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ContDiff

def standardGaussianDensity (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ i : Fin n, gaussianPDFReal 0 1 (x i)

theorem standardGaussianDensity_pos (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    0 < standardGaussianDensity n x := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos 0 1 (x i) one_ne_zero

theorem standardGaussianDensity_smooth (n : ℕ) : ContDiff ℝ ∞ (standardGaussianDensity n) := by
  unfold standardGaussianDensity gaussianPDFReal
  fun_prop

theorem pi_standardGaussian_density (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i : Fin n, gaussianPDFReal 0 1 (x i))) := by
  have hint : Integrable (fun x : Fin n → ℝ => ∏ i : Fin n, gaussianPDFReal 0 1 (x i)) :=
    Integrable.fintype_prod fun _ => integrable_gaussianPDFReal 0 1
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint.restrict
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i))]
  rw [show (volume : Measure (Fin n → ℝ)) = Measure.pi (fun _ : Fin n => (volume : Measure ℝ)) from rfl,
    Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  apply Finset.prod_congr rfl
  intro i _
  exact (gaussianReal_apply_eq_integral 0 one_ne_zero (s i)).symm

theorem stdGaussian_eq_densityMeasure (n : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) = densityMeasure n (standardGaussianDensity n) := by
  rw [← map_pi_eq_stdGaussian, pi_standardGaussian_density]
  unfold densityMeasure
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    withDensity_apply _ (hs.preimage (by fun_prop)), withDensity_apply _ hs]
  exact (PiLp.volume_preserving_toLp (Fin n)).setLIntegral_comp_preimage hs
    (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal

end AffineFKProof
