module

public import AffineFK.OUDensityTimeDifferentiation
public import AffineFK.GaussianSmoothingProduct
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The weak OU Fokker--Planck equation for the actual smoothing law

The generator below is the sum of genuine second coordinate derivatives
minus the coordinate-gradient contraction. The expectation derivative is
proved by dominated differentiation and actual Gaussian integration by
parts. Only the original measure's first moment is required. This is a
weak density equation, not an entropy chain rule or de Bruijn identity.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

/-- The genuine OU generator on compact smooth scalar tests, as another
compact smooth scalar test: the Laplacian minus x dot gradient. -/
def ouTestGenerator (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  ∑ i : Fin n, (partialTest n i (partialTest n i φ) - coordinateMulTest n i (partialTest n i φ))

theorem ouTestGenerator_apply (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ouTestGenerator n φ x =
      ∑ i : Fin n, (partialTest n i (partialTest n i φ) x - x i * partialTest n i φ x) := by
  simp [ouTestGenerator, coordinateMulTest]

theorem ou_fderiv_test_coordinate_sum (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ φ x v = ∑ i : Fin n, v i * partialTest n i φ x := by
  rw [← inner_gradient_left]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, partialTest_apply]

theorem ou_integral_directional_derivative_eq_generator (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (a b c : ℝ) (hb : b ≠ 0) (hbc : b ^ 2 + b * c = 1) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      fderiv ℝ φ (a • p.1 + b • p.2) ((-a) • p.1 + c • p.2)
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
    ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ouTestGenerator n φ (a • p.1 + b • p.2)
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ := stdGaussian E
  let μ := ν.prod γ
  let W : E × E → E := fun p => a • p.1 + b • p.2
  have hW : Continuous W := by fun_prop
  have hfirst (i : Fin n) : Integrable (fun p : E × E => p.1 i * partialTest n i φ (W p)) μ := by
    have hi : Integrable (fun u : E => u i) ν := by
      simpa only [coordinateFunctional_apply] using (coordinateFunctional n i).integrable_comp hU
    exact integrable_fst_mul_test_comp n ν γ (fun u => u i) hi W hW (partialTest n i φ)
  have hGauss (i : Fin n) := product_gaussian_smoothing_integration_by_parts n ν i a b hb
    (partialTest n i φ)
  have hV (i : Fin n) : Integrable (fun p : E × E =>
      ((-a) * p.1 i + c * p.2 i) * partialTest n i φ (W p)) μ := by
    convert ((hfirst i).const_mul (-a)).add ((hGauss i).1.const_mul c) using 1
    funext p
    change ((-a) * p.1 i + c * p.2 i) * partialTest n i φ (W p) =
      (-a) * (p.1 i * partialTest n i φ (W p)) + c * (p.2 i * partialTest n i φ (W p))
    ring
  have hWmul (i : Fin n) : Integrable (fun p : E × E =>
      W p i * partialTest n i φ (W p)) μ := by
    convert ((hfirst i).const_mul a).add ((hGauss i).1.const_mul b) using 1
    funext p
    change (a * p.1 i + b * p.2 i) * partialTest n i φ (W p) =
      a * (p.1 i * partialTest n i φ (W p)) + b * (p.2 i * partialTest n i φ (W p))
    ring
  have hgen (i : Fin n) : Integrable (fun p : E × E =>
      partialTest n i (partialTest n i φ) (W p) - W p i * partialTest n i φ (W p)) μ :=
    (hGauss i).2.1.sub (hWmul i)
  have heq (i : Fin n) :
      (∫ p : E × E, ((-a) * p.1 i + c * p.2 i) * partialTest n i φ (W p) ∂μ) =
      ∫ p : E × E, partialTest n i (partialTest n i φ) (W p) -
        W p i * partialTest n i φ (W p) ∂μ := by
    have hleft : (fun p : E × E => ((-a) * p.1 i + c * p.2 i) * partialTest n i φ (W p)) =
        (fun p => (-a) * (p.1 i * partialTest n i φ (W p)) +
          c * (p.2 i * partialTest n i φ (W p))) := by funext p; ring
    have hright : (fun p : E × E => W p i * partialTest n i φ (W p)) =
        (fun p => a * (p.1 i * partialTest n i φ (W p)) +
          b * (p.2 i * partialTest n i φ (W p))) := by
      funext p
      change (a * p.1 i + b * p.2 i) * _ = _
      ring
    rw [hleft, integral_add ((hfirst i).const_mul (-a)) ((hGauss i).1.const_mul c),
      integral_sub (hGauss i).2.1 (hWmul i), hright,
      integral_add ((hfirst i).const_mul a) ((hGauss i).1.const_mul b)]
    rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      (hGauss i).2.2]
    have hcoef := congrArg
      (fun z : ℝ => z * (∫ p : E × E, partialTest n i (partialTest n i φ) (W p) ∂μ)) hbc
    nlinarith [hcoef]
  have hdpoint (p : E × E) :
      fderiv ℝ φ (W p) ((-a) • p.1 + c • p.2) =
        ∑ i : Fin n, ((-a) * p.1 i + c * p.2 i) * partialTest n i φ (W p) := by
    rw [ou_fderiv_test_coordinate_sum]
    rfl
  change (∫ p : E × E, fderiv ℝ φ (W p) ((-a) • p.1 + c • p.2) ∂μ) =
    ∫ p : E × E, ouTestGenerator n φ (W p) ∂μ
  simp_rw [hdpoint, ouTestGenerator_apply]
  rw [integral_finsetSum _ (fun i _ => hV i), integral_finsetSum _ (fun i _ => hgen i)]
  exact Finset.sum_congr rfl (fun i _ => heq i)

theorem ou_test_expectation_weak_equation (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      φ (Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
      (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ouTestGenerator n φ (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) t := by
  have hd := ou_smoothing_scale_domain t ht
  have hs : Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 = 1 - Real.exp (-2 * t) :=
    Real.sq_sqrt (Real.sqrt_pos.mp hd.2.1).le
  have hc : Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 +
      Real.sqrt (1 - Real.exp (-2 * t)) *
        (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) = 1 := by
    rw [mul_div_cancel₀ _ hd.2.1.ne', hs]
    ring
  rw [← ou_integral_directional_derivative_eq_generator n ν hU φ _ _ _ hd.2.1.ne' hc]
  exact (ou_test_expectation_hasDerivAt n ν hU φ t ht).2

end AffineFKProof
