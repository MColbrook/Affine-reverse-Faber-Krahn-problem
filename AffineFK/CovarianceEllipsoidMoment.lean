module

public import AffineFK.CovarianceWhiteningMatrix
public import AffineFK.ProbabilityLinearCovariance
public import Mathlib.Probability.Moments.Covariance

/-!
# The actual centered covariance and its whitened quadratic moment

The centered matrix consists of genuine coordinate integrals of the
translated original law. The actual CFC inverse square root whitens this
matrix, and finite L1 summation proves its norm-square moment is n.
The matrix transport and square-root identities are reused from the
separately proved project covariance modules; Mathlib's covariance
definition and measure-map integral theorem retain their attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

def covarianceEllipsoidCenteredLaw (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (m : EuclideanSpace ℝ (Fin n)) :
    Measure (EuclideanSpace ℝ (Fin n)) := μ.map (fun x => x-m)

def covarianceEllipsoidMomentMatrix (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (m : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  probabilitySecondMomentMatrix n (covarianceEllipsoidCenteredLaw n μ m)

theorem covarianceEllipsoidMomentMatrix_entry (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (m : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    covarianceEllipsoidMomentMatrix n μ m i j =
      ∫ x : EuclideanSpace ℝ (Fin n), (x i-m i)*(x j-m j) ∂μ := by
  unfold covarianceEllipsoidMomentMatrix probabilitySecondMomentMatrix covarianceEllipsoidCenteredLaw
  rw [integral_map (by fun_prop : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x-m)).aemeasurable
    (by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i*x j)).aestronglyMeasurable]
  rfl

theorem covarianceEllipsoidMomentMatrix_covariance (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (m : EuclideanSpace ℝ (Fin n))
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂μ) = m i)
    (i j : Fin n) :
    covarianceEllipsoidMomentMatrix n μ m i j =
      covariance (fun x : EuclideanSpace ℝ (Fin n) => x i) (fun x => x j) μ := by
  rw [covarianceEllipsoidMomentMatrix_entry,covariance,hmean i,hmean j]

theorem covarianceEllipsoidCenteredLaw_memLp (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ)
    (m : EuclideanSpace ℝ (Fin n)) :
    MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (covarianceEllipsoidCenteredLaw n μ m) := by
  apply (memLp_map_measure_iff aestronglyMeasurable_id
    (by fun_prop : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x-m)).aemeasurable).mpr
  exact hX.sub (memLp_const m)

theorem covarianceEllipsoidWhitened_memLp (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ)
    (m : EuclideanSpace ℝ (Fin n)) (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef) :
    MemLp (fun x => covarianceWhiteningLinear n (covarianceEllipsoidMomentMatrix n μ m) hM (x-m)) 2 μ := by
  exact (covarianceWhiteningLinear n _ hM).toContinuousLinearMap.comp_memLp'
    (hX.sub (memLp_const m))

theorem covarianceEllipsoidWhitened_second_moment (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ)
    (m : EuclideanSpace ℝ (Fin n)) (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef) :
    (∫ x : EuclideanSpace ℝ (Fin n),
      ‖covarianceWhiteningLinear n (covarianceEllipsoidMomentMatrix n μ m) hM (x-m)‖^2 ∂μ) =
        (n : ℝ) := by
  let η := covarianceEllipsoidCenteredLaw n μ m
  let M := covarianceEllipsoidMomentMatrix n μ m
  let W := covarianceWhiteningMatrix n M
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) W
  let ζ := η.map T
  have hY : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 η :=
    covarianceEllipsoidCenteredLaw_memLp n μ hX m
  have hZ : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ζ :=
    (memLp_map_measure_iff aestronglyMeasurable_id T.continuous.measurable.aemeasurable).mpr
      (T.comp_memLp' hY)
  have hmoment : probabilitySecondMomentMatrix n ζ = 1 :=
    (probabilitySecondMomentMatrix_linear_image n η hY W).trans
      (covarianceWhiteningMatrix_identity n M hM)
  have hnorm : (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖^2 ∂ζ) = (n : ℝ) := by
    simp_rw [EuclideanSpace.real_norm_sq_eq,pow_two]
    calc
      _ = ∑ i : Fin n, (∫ z : EuclideanSpace ℝ (Fin n), z i*z i ∂ζ) :=
        integral_finsetSum Finset.univ (fun i _ => (hZ.eval_piLp i).integrable_mul (hZ.eval_piLp i))
      _ = ∑ i : Fin n, probabilitySecondMomentMatrix n ζ i i := rfl
      _ = (n : ℝ) := by rw [hmoment]; simp
  calc
    _ = ∫ z : EuclideanSpace ℝ (Fin n), ‖T z‖^2 ∂η := by
      symm
      exact integral_map
        (by fun_prop : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x-m)).aemeasurable
        (T.continuous.norm.pow 2).aestronglyMeasurable
    _ = ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖^2 ∂ζ := by
      symm
      exact integral_map T.continuous.measurable.aemeasurable
        (continuous_norm.pow 2).aestronglyMeasurable
    _ = (n : ℝ) := hnorm

end AffineFKProof
