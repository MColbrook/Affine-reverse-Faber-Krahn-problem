module

public import AffineFK.CovarianceEllipsoidIntersection
public import AffineFK.CovarianceEllipsoidVolume

/-!
# The covariance ellipsoid with derived mass, intersection and volume

The center is the actual mean and the matrix is the actual covariance.
The density and covariance determinant bounds are explicit inputs; the
ellipsoid mass, intersection and volume bounds are derived. Neither a
small-determinant point nor a universal Milman theorem is asserted here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix Set Metric
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator

theorem exists_covariance_ellipsoid_bounds (n : ℕ) (hn : 0 < n)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ)
    (m : EuclideanSpace ℝ (Fin n))
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂μ) = m i)
    (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hlaw : μ = densityMeasure n ρ)
    (hsupport : ∀ x, x ∉ K → ρ x = 0)
    (hbound : ∀ x ∈ K, ρ x ≤ Real.exp (n : ℝ))
    (C : ℝ) (hC : 0 ≤ C) (hdet : (covarianceEllipsoidMomentMatrix n μ m).det ≤ C^n) :
    (∀ i j : Fin n, covarianceEllipsoidMomentMatrix n μ m i j =
      covariance (fun x : EuclideanSpace ℝ (Fin n) => x i) (fun x => x j) μ) ∧
    ∃ E : Set (EuclideanSpace ℝ (Fin n)), IsCompact E ∧
      E = (fun z => m+Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (CFC.sqrt (covarianceEllipsoidMomentMatrix n μ m)) z) ''
          closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ))) ∧
      (1/2 : ℝ≥0∞) ≤ μ E ∧
      (1/(2*Real.exp 1))^n ≤ (volume (K ∩ E)).toReal ∧
      (volume E).toReal ≤ (Real.sqrt C*covarianceEllipsoidBallVolumeBase)^n := by
  refine ⟨covarianceEllipsoidMomentMatrix_covariance n μ m hmean, covarianceEllipsoidSet n μ m hM,
    covarianceEllipsoidSet_compact n μ m hM,covarianceEllipsoidSet_sqrt_image n μ m hM,
    covarianceEllipsoidSet_mass n hn μ hX m hM,?_,?_⟩
  · exact covarianceEllipsoid_intersection_lower n hn μ hX m hM K hK ρ hlaw hsupport hbound
  · exact covarianceEllipsoidSet_volume_bound n μ m hM C hC hdet

end AffineFKProof
