module

public import AffineFK.GaussianVarianceCancellation
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The standard Gaussian Poincare inequality with exact constant one

Actual Gaussian rotation covariance and integration by parts give its
derivative. The proved correlation bound makes the covariance minus the
cosine times the gradient energy monotone on the quarter circle. The two
actual endpoint values yield the variance inequality, in every dimension.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology

theorem stdGaussian_poincare (n : ℕ)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
        ∫ x, ‖gradient f x‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let C := ∫ x, ‖gradient f x‖ ^ 2 ∂γ
  let K : ℝ → ℝ := fun θ => ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
    ⟪gradient f p.1, gradient f (Real.cos θ • p.1 + Real.sin θ • p.2)⟫ ∂γ.prod γ
  let V : ℝ → ℝ := fun θ => gaussianVarianceCorrelation n f θ - C * Real.cos θ
  have hsin (θ : ℝ) (hθ : θ ∈ interior (Set.Icc (0 : ℝ) (Real.pi / 2))) : 0 < Real.sin θ := by
    rw [interior_Icc] at hθ
    exact Real.sin_pos_of_pos_of_lt_pi hθ.1 (by nlinarith [hθ.2, Real.pi_pos])
  have hcorr (θ : ℝ) : K θ ≤ C :=
    gaussianVariance_gradient_correlation_le n (Real.cos θ) (Real.sin θ)
      (by nlinarith [Real.sin_sq_add_cos_sq θ]) f
  have hdiff (θ : ℝ) (hθ : θ ∈ interior (Set.Icc (0 : ℝ) (Real.pi / 2))) :
      HasDerivAt V (Real.sin θ * (C - K θ)) θ := by
    have hd := gaussianVarianceCorrelation_derivative_formula n f θ (hsin θ hθ).ne'
    have hh := hd.sub ((Real.hasDerivAt_cos θ).const_mul C)
    convert hh using 1 <;> ring
  have hc : Continuous (gaussianVarianceCorrelation n f) :=
    continuous_iff_continuousAt.mpr fun θ => (gaussianVarianceCorrelation_hasDerivAt n f θ).2.continuousAt
  have hmono : MonotoneOn V (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (hc.sub (continuous_const.mul Real.continuous_cos)).continuousOn
      (fun θ hθ => (hdiff θ hθ).hasDerivWithinAt)
      (fun θ hθ => mul_nonneg (hsin θ hθ).le (sub_nonneg.mpr (hcorr θ)))
  have hend := hmono
    (show (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) from ⟨le_rfl, Real.pi_div_two_pos.le⟩)
    (show Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from ⟨Real.pi_div_two_pos.le, le_rfl⟩)
    Real.pi_div_two_pos.le
  dsimp only [V] at hend
  rw [gaussianVarianceCorrelation_zero, gaussianVarianceCorrelation_pi_div_two,
    Real.cos_zero, Real.cos_pi_div_two, mul_one, mul_zero, sub_zero] at hend
  have hfL2 := testFunction_memLp_two n γ f
  have hv : (∫ x, (f x - ∫ y, f y ∂γ) ^ 2 ∂γ) =
      (∫ x, (f x) ^ 2 ∂γ) - (∫ x, f x ∂γ) ^ 2 :=
    (variance_eq_integral hfL2.aemeasurable).symm.trans (variance_eq_sub hfL2)
  change (∫ x, (f x - ∫ y, f y ∂γ) ^ 2 ∂γ) ≤ C
  rw [hv]
  nlinarith [hend]

end AffineFKProof
