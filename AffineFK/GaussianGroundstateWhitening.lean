module

public import AffineFK.WhitenedConvolutionConstruction
public import AffineFK.StrongLogConcaveDensityOrdinary
public import AffineFK.GroundstateGaussianLawBounds
public import AffineFK.DirichletEigenvaluePositive

/-!
# Whitening the actual Gaussian-weighted weak eigenfunction law

The input law is the normalized square of the genuine H0^1 Gaussian
multiplier. Its Poincare and Fisher bounds are derived from the proved
weak-eigenfunction calculation and a pointwise strongly log-concave
representative of that same law. Support follows from zero extension.
The existence, evenness and log-concavity of the required first ground
state, and the geometric uniform lower bound on alpha, remain separate
inputs to the main theorem.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Matrix
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator

theorem gaussianGroundstateDensity_support (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ψ : dirichletSobolev n U)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (hUK : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ K) :
    ∀ᵐ x ∂densityMeasure n (gaussianGroundstateDensity n U ψ), x ∈ K := by
  have hz := dirichletValue_ae_zero_outside n U K hK hUK (gaussianDirichletFactor n U ψ)
  apply (ae_withDensity_iff (gaussianGroundstateDensity_measurable n U ψ).ennreal_ofReal).mpr
  filter_upwards [hz] with x hx
  intro hne
  by_contra hxK
  apply hne
  simp only [gaussianGroundstateDensity, hx hxK, zero_pow (by norm_num : 2 ≠ 0),
    zero_div, ENNReal.ofReal_zero]

theorem gaussian_groundstate_whitening_construction (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (heven : ∀ x, -x ∈ K ↔ x ∈ K)
    (hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (hUK : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ K)
    (ell : ℝ) (ψ : dirichletSobolev n U)
    (hweak : IsDirichletWeakEigenfunction n U ell ψ) (hψ : ψ ≠ 0)
    (hψ0 : ∀ᵐ x ∂volume, 0 ≤ dirichletValue n U ψ x)
    [Measure.IsNegInvariant (densityMeasure n (gaussianGroundstateDensity n U ψ))]
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hgLaw : densityMeasure n (gaussianGroundstateDensity n U ψ) = densityMeasure n g)
    (hgTilt : LogConcaveDensity (fun x => ENNReal.ofReal
      (g x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2))))
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hcovX : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
      ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) =
        if i = j then α else 0) :
    let ν := ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K
    let η := densityMeasure n (gaussianGroundstateDensity n U ψ)
    let ζ := whitenedSumLaw n ν η α
    let D := whitenedSupportBody n η α K
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
  let ν := ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K
  let η := densityMeasure n (gaussianGroundstateDensity n U ψ)
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure hKpos
  let : Measure.IsNegInvariant ν := gaussianPosition_cond_even n K hK.measurableSet heven
  let : IsProbabilityMeasure η := gaussianGroundstateDensity_probability n U ψ hψ
  let f := gaussianPositionRestrictedDensity n K
  have hfLaw : densityMeasure n f = ν := gaussianPositionRestrictedDensity_law n K hK.measurableSet hKpos
  let : IsProbabilityMeasure (densityMeasure n f) := by rw [hfLaw]; infer_instance
  let : IsProbabilityMeasure (densityMeasure n g) := by rw [← hgLaw]; infer_instance
  let : Measure.IsNegInvariant (densityMeasure n f) := by rw [hfLaw]; infer_instance
  let : Measure.IsNegInvariant (densityMeasure n g) := by rw [← hgLaw]; infer_instance
  have hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν :=
    memLp_piLp_iff.mpr fun i => gaussianPosition_cond_coordinate_memLp n K hKpos i
  have hY : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 η :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr
      (gaussianGroundstateDensity_second_moment n U ψ).1
  have hmeanX := gaussianPosition_cond_coordinate_mean_zero n K hK.measurableSet hKpos heven
  have hmeanY := even_measure_coordinate_mean_zero n η
  have hPf := gaussianPosition_cond_poincareConstant_le_one n K hK.measurableSet hconv hKpos
  have hgood := gaussianGroundstateDensity_fisher_bound_of_representative n U ell ψ hweak hψ hψ0
    g hg hg0 hgLaw hgTilt
  have hresult := whitened_convolution_construction n f g
    (gaussianPositionRestrictedDensity_measurable n K hK.measurableSet) hg
    (gaussianPositionRestrictedDensity_logConcave n K hconv)
    (strongLogConcaveDensity_logConcave n g hg0 hgTilt)
    (by rw [hfLaw]; exact hX) (by rw [← hgLaw]; exact hY)
    (by rw [hfLaw]; exact hmeanX) (by rw [← hgLaw]; exact hmeanY)
    (by rw [hfLaw]; exact hPf) (by rw [← hgLaw]; exact hgood.1)
    α hα hαone (by rw [hfLaw]; exact hcovX) ell
    (by rw [← hgLaw]; exact hgood.2.2.1) (by rw [← hgLaw]; exact hgood.2.2.2)
    K hK hconv (by rw [hfLaw]; exact ae_cond_mem hK.measurableSet)
    (by rw [← hgLaw]; exact gaussianGroundstateDensity_support n U ψ K hK.measurableSet hUK)
  simpa only [hfLaw, ← hgLaw] using hresult

end AffineFKProof
