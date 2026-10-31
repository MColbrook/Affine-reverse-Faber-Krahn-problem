module

public import AffineFK.GaussianRelativeScoreHessian
public import AffineFK.VectorPoincareRegressionWeakScore

/-!
# Poincare regression for the actual Gaussian-smoothed relative score

Literal isotropy and a bound for the actual least Poincare constant of
the output are the explicit geometric inputs. The actual relative score,
its L2 domain, smoothness, weak equations and component-gradient L2
domain are all derived. This is one regression step, not the information
jump; preservation of input isotropy and the final jump remain separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal NNReal

theorem gaussianSmoothing_relativeScore_poincare_regression (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b)
    (P : ℝ≥0) (hP0 : 0 < P)
    (hP : poincareConstant n (densityMeasure n (gaussianSmoothingDensity n ν a b)) ≤ (P : ℝ≥0∞))
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i
      ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) = 0)
    (hsecond : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
      ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) = if i = j then (1 : ℝ) else 0)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n
      (gaussianRelativeScore n (gaussianSmoothingDensity n ν a b)) x + A))
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
    ((∫ x, ‖gaussianRelativeScore n (gaussianSmoothingDensity n ν a b) x‖ ^ 2
      ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) + matrixHilbertSchmidtSq A) / (P : ℝ) ≤
      ∫ x, matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n
        (gaussianRelativeScore n (gaussianSmoothingDensity n ν a b)) x + A)
        ∂densityMeasure n (gaussianSmoothingDensity n ν a b) := by
  let ρ := gaussianSmoothingDensity n ν a b
  have hlaw := gaussianSmoothingDensity_law n ν a b hb
  have : IsProbabilityMeasure (densityMeasure n ρ) := by rw [← hlaw]; infer_instance
  obtain ⟨r, _hr, _hr2, _hr4, _hrep, _hid, hs2, _hs4, _hi, _hbound⟩ :=
    gaussianSmoothing_ordinaryScore_conditional_L4 n ν a b hb
  have hs : MemLp (gradient (fun x => Real.log (ρ x))) 2 (densityMeasure n ρ) := by
    simpa only [hlaw] using hs2
  have hx : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (densityMeasure n ρ) := memLp_piLp_iff.mpr (fun i => isotropic_coordinate_memLp n _ hsecond i)
  have hr : MemLp (gaussianRelativeScore n ρ) 2 (densityMeasure n ρ) := hs.add hx
  exact weakRelativeScore_poincare_regression n (densityMeasure n ρ) P hP0 hP hmean hsecond
    (gaussianRelativeScore n ρ) hr
    (fun F => (gaussianRelativeScore_vector_pairing n ρ (gaussianSmoothingDensity_smooth n ν a b)
      (gaussianSmoothingDensity_pos n ν a b hb) F).2.2)
    (gaussianRelativeScore_smooth n ρ (gaussianSmoothingDensity_smooth n ν a b)
      (gaussianSmoothingDensity_pos n ν a b hb))
    (gaussianSmoothing_relativeScore_component_gradient_memLp n ν a b hb) A

end AffineFKProof
