module

public import AffineFK.GaussianEntropyCalculusReferenceIntegral
public import AffineFK.OUGaussianEntropyBound

/-!
# The actual finite KL integral of a Gaussian-mixture relative density

The second moment implies finite extended-valued KL by the separately
proved mixture estimate. Mathlib's genuine RN/KL integral theorem then
identifies the smooth positive relative-density representative. Finiteness
and integrability are conclusions, so a default real Bochner integral
cannot conceal an infinite entropy.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

theorem gaussian_relative_smoothing_entropy_formula (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hsecond : Integrable (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ ^ 2) ν)
    (a b : ℝ) (hb : 0 < b) :
    let μ := (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)
    let q := gaussianSmoothingRelativeDensity n ν a b
    klDiv μ (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
    Integrable (fun x => klFun (q x)) (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (klDiv μ (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal =
      ∫ x, klFun (q x) ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  let μ := (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
    (fun p => a • p.1 + b • p.2)
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let q := gaussianSmoothingRelativeDensity n ν a b
  have hfin : klDiv μ γ ≠ ∞ := gaussian_mixture_entropy_finite n ν hsecond a b hb
  have hp := klDiv_ne_top_iff.mp hfin
  have hprops := gaussianSmoothingRelativeDensity_properties n ν a b hb
  have hrep : (fun x => (μ.rnDeriv γ x).toReal) =ᵐ[γ] q := by
    filter_upwards [hprops.2.2.2] with x hx
    rw [hx, ENNReal.toReal_ofReal (hprops.2.1 x).le]
  have hklrep := hrep.fun_comp klFun
  refine ⟨hfin, ((integrable_klFun_rnDeriv_iff hp.1).mpr hp.2).congr hklrep, ?_⟩
  exact (toReal_klDiv_eq_integral_klFun hp.1).trans (integral_congr_ae hklrep)

end AffineFKProof
