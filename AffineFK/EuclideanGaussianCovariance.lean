module

public import AffineFK.GaussianHermiteCovariance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.HasLaw

/-!
# Centred quadratic covariance under the actual Euclidean Gaussian

The product-measure result is transported using Mathlib's genuine
Gaussian pushforward identity and HasLaw change of variables (Remy Degenne,
Etienne Marion and the contributors credited in those modules).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem stdGaussian_quadratic_pair_covariance (n : ℕ) (j k l p : Fin n) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (x j * x k - if j = k then 1 else 0) * (x l * x p - if l = p then 1 else 0))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x : EuclideanSpace ℝ (Fin n),
      (x j * x k - if j = k then 1 else 0) * (x l * x p - if l = p then 1 else 0)
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      (if j = l then 1 else 0) * (if k = p then 1 else 0) +
        (if j = p then 1 else 0) * (if k = l then 1 else 0) := by
  have h := productGaussian_quadratic_pair_covariance n j k l p
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      (x j * x k - if j = k then 1 else 0) * (x l * x p - if l = p then 1 else 0)) := by fun_prop
  have hlaw : HasLaw (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (Measure.pi fun _ => gaussianReal 0 1) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hI : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (x j * x k - if j = k then 1 else 0) * (x l * x p - if l = p then 1 else 0))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    rw [← map_pi_eq_stdGaussian]
    apply (integrable_map_measure hc.aestronglyMeasurable (by fun_prop)).mpr
    simpa only [Function.comp_def] using h.1
  refine ⟨hI, ?_⟩
  calc
    _ = ∫ x : Fin n → ℝ,
        (x j * x k - if j = k then 1 else 0) * (x l * x p - if l = p then 1 else 0)
        ∂Measure.pi (fun _ => gaussianReal 0 1) :=
      (hlaw.integral_comp hc.aestronglyMeasurable).symm
    _ = _ := h.2

end AffineFKProof
