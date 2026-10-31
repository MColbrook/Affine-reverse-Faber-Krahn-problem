module

public import AffineFK.GaussianVarianceIntegrationByParts

/-! The exact Gaussian covariance-interpolation derivative, with cancellation. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace

theorem gaussianVarianceCorrelation_derivative_formula (n : ℕ)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (θ : ℝ) (hb : Real.sin θ ≠ 0) :
    HasDerivAt (gaussianVarianceCorrelation n f)
      ((-Real.sin θ) * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ⟪gradient f p.1, gradient f (Real.cos θ • p.1 + Real.sin θ • p.2)⟫
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n))))) θ := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let μ := γ.prod γ
  let a := Real.cos θ
  let b := Real.sin θ
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  let H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ :=
    fun p => f p.1 * fderiv ℝ f (W p) ((-b) • p.1 + a • p.2)
  have hx (i : Fin n) := gaussianVariance_IBP_fst n i f (partialTest n i f) a b
  have hy (i : Fin n) := gaussianVariance_IBP_snd n i f (partialTest n i f) a b hb
  have hterm (i : Fin n) : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (-b) * ((p.1 i * f p.1) * partialTest n i f (W p)) +
          a * ((f p.1 * p.2 i) * partialTest n i f (W p))) μ :=
    ((hx i).1.const_mul (-b)).add ((hy i).1.const_mul a)
  have hH (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
      H p = ∑ i : Fin n, ((-b) * ((p.1 i * f p.1) * partialTest n i f (W p)) +
        a * ((f p.1 * p.2 i) * partialTest n i f (W p))) := by
    dsimp only [H]
    rw [← inner_gradient_left]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, partialTest_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hEq : (∫ p, H p ∂μ) = (-b) * (∫ p, ⟪gradient f p.1, gradient f (W p)⟫ ∂μ) := by
    calc
      _ = ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ∑ i : Fin n, ((-b) * ((p.1 i * f p.1) * partialTest n i f (W p)) +
            a * ((f p.1 * p.2 i) * partialTest n i f (W p))) ∂μ :=
        integral_congr_ae (Eventually.of_forall hH)
      _ = ∑ i : Fin n, ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          (-b) * ((p.1 i * f p.1) * partialTest n i f (W p)) +
            a * ((f p.1 * p.2 i) * partialTest n i f (W p)) ∂μ :=
        integral_finsetSum _ (fun i _ => hterm i)
      _ = (-b) * ∑ i : Fin n, ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          partialTest n i f p.1 * partialTest n i f (W p) ∂μ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_add ((hx i).1.const_mul (-b)) ((hy i).1.const_mul a),
          integral_const_mul, integral_const_mul, (hx i).2.2.2, (hy i).2.2]
        ring
      _ = (-b) * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ∑ i : Fin n, partialTest n i f p.1 * partialTest n i f (W p) ∂μ) := by
        rw [integral_finsetSum _ (fun i _ => (hx i).2.1)]
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by
          simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, partialTest_apply]
          apply Finset.sum_congr rfl
          intro i _
          exact mul_comm _ _
  have hd := (gaussianVarianceCorrelation_hasDerivAt n f θ).2
  change HasDerivAt (gaussianVarianceCorrelation n f) (∫ p, H p ∂μ) θ at hd
  rw [hEq] at hd
  exact hd

end AffineFKProof
