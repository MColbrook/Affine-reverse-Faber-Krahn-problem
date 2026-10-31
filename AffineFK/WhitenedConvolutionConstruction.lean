module

public import AffineFK.WhitenedConvolutionInformation
public import AffineFK.WhitenedConvolutionLogConcavity
public import AffineFK.WhitenedBodyLinear

/-!
# The covariance-whitened law used in the affine argument

All conclusions concern one actual independent sum and its prescribed
inverse-square-root image. The hypotheses are the input laws' genuine
moment, Poincare, density and ordinary-information bounds. In the source,
the restricted Gaussian and the Gaussian-weighted ground state supply
these inputs. Their construction and the geometric lower bound on alpha
remain separate prerequisites; neither is replaced by an output premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Matrix
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator

theorem whitened_convolution_construction (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f) (hg : Measurable g)
    [IsProbabilityMeasure (densityMeasure n f)] [IsProbabilityMeasure (densityMeasure n g)]
    [Measure.IsNegInvariant (densityMeasure n f)] [Measure.IsNegInvariant (densityMeasure n g)]
    (hlf : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hlg : LogConcaveDensity (fun x => ENNReal.ofReal (g x)))
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 (densityMeasure n f))
    (hY : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 (densityMeasure n g))
    (hmeanX : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂densityMeasure n f) = 0)
    (hmeanY : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂densityMeasure n g) = 0)
    (hPf : poincareConstant n (densityMeasure n f) ≤ 1)
    (hPg : poincareConstant n (densityMeasure n g) ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hcovX : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂densityMeasure n f) =
      if i = j then α else 0)
    (ell : ℝ) (hJg : ordinaryFisherMeasure n (densityMeasure n g) ≠ ∞)
    (hJgBound : (ordinaryFisherMeasure n (densityMeasure n g)).toReal ≤ 4 * ell + n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsuppX : ∀ᵐ x ∂densityMeasure n f, x ∈ K)
    (hsuppY : ∀ᵐ x ∂densityMeasure n g, x ∈ K) :
    let ζ := whitenedSumLaw n (densityMeasure n f) (densityMeasure n g) α
    let D := whitenedSupportBody n (densityMeasure n g) α K
    ∃ A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ h : EuclideanSpace ℝ (Fin n) → ℝ,
      Measurable h ∧ (∀ x, 0 ≤ h x) ∧ LogConcaveDensity (fun x => ENNReal.ofReal (h x)) ∧
      ζ = densityMeasure n h ∧ IsProbabilityMeasure ζ ∧ Measure.IsNegInvariant ζ ∧
      MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ζ ∧
      (∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ζ) = 0) ∧
      (∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ζ) = if i = j then 1 else 0) ∧
      D = A '' K ∧ ‖A.toContinuousLinearMap‖ ^ 2 ≤ 4 / α ∧
      IsCompact D ∧ Convex ℝ D ∧ (∀ᵐ x ∂ζ, x ∈ D) ∧
      poincareConstant n ζ ≤ ENNReal.ofReal (2 / α) ∧
      ordinaryFisherMeasure n ζ ≠ ∞ ∧ (ordinaryFisherMeasure n ζ).toReal ≤ 8 * ell + 2 * n ∧
      relativeFisherMeasure n ζ ≠ ∞ ∧ (relativeFisherMeasure n ζ).toReal ≤ 8 * ell + n ∧
      relativeFisherMeasure n ζ ≤ ENNReal.ofReal (8 * ell + n) := by
  let ν := densityMeasure n f
  let η := densityMeasure n g
  have hM := (convolutionCovarianceMatrix_bounds n η hY hmeanY hPg α hα hαone).2.2
  let A := covarianceWhiteningBodyLinear n (convolutionCovarianceMatrix n α η) hM
  obtain ⟨h, hh, hh0, hhlc, hlaw⟩ :=
    whitenedSumLaw_logConcave_density n f g hf hg hlf hlg hY hmeanY hPg α hα hαone
  have hiso := whitenedSumLaw_isotropic n ν η hX hY hmeanX hmeanY hPg α hα hαone hcovX
  have hinfo := whitenedSumLaw_relativeFisher_bound n ν η hX hY hmeanX hmeanY hPf hPg
    α hα hαone hcovX ell hJg hJgBound
  have hD := whitenedSupportBody_compact_convex n η α K hK hconv
  exact ⟨A, h, hh, hh0, hhlc, hlaw,
    whitenedSumLaw_isProbabilityMeasure n ν η α,
    whitenedSumLaw_neg_invariant n ν η α, hiso.1, hiso.2.1, hiso.2.2,
    whitenedSupportBody_eq_linear_image n η α K hM,
    covarianceWhiteningBodyLinear_norm_sq_bound n _ hM α hα
      (convolutionCovarianceMatrix_bounds n η hY hmeanY hPg α hα hαone).1,
    hD.1, hD.2, whitenedSumLaw_support n ν η K hK hconv hsuppX hsuppY α,
    (whitenedSumLaw_poincare_fisher_bounds n ν η hY hmeanY hPf hPg α hα hαone).1,
    hinfo.1, hinfo.2.1, hinfo.2.2.1, hinfo.2.2.2.1, hinfo.2.2.2.2⟩

end AffineFKProof
