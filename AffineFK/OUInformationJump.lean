module

public import AffineFK.OUInformationJumpComparison
public import AffineFK.OUConvolutionRegression
public import AffineFK.IsotropicPoincareLowerBound

/-!
# The actual positive-time information jump for normalized copies

The actual Hessian regression bound and genuine numerical Fisher
dissipation satisfy the scalar comparison theorem. All positive-time
information values are finite as conclusions. The original input density
need only be measurable and log-concave; its initial information is not
assumed finite. The original positive dimension discharges P>=1 from
isotropy and the actual least-Poincare upper bound.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Interval

theorem ou_normalized_copies_information_jump (n : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂densityMeasure n f) = 0)
    (hcov : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂densityMeasure n f) =
      if i = j then (1 : ℝ) else 0)
    (P : ℝ≥0) (hP : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞))
    (s : ℝ) (hs : 0 < s) :
    let ν := densityMeasure n f
    let a := (Real.sqrt 2)⁻¹
    let ξ := (ν.prod ν).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + a • p.2)
    relativeFisherMeasure n (ouInitialLaw n ν s) ≠ (∞ : ℝ≥0∞) ∧
      relativeFisherMeasure n (ouInitialLaw n ξ s) ≠ (∞ : ℝ≥0∞) ∧
      (relativeFisherMeasure n (ouInitialLaw n ξ s)).toReal ≤
        (1 - 1 / (8 * (P : ℝ))) * (relativeFisherMeasure n (ouInitialLaw n ν s)).toReal := by
  let E := EuclideanSpace ℝ (Fin n)
  let ν := densityMeasure n f
  let a : ℝ := (Real.sqrt 2)⁻¹
  let W : E × E → E := fun p => a • p.1 + a • p.2
  have hW : Measurable W := by dsimp [W]; fun_prop
  let ξ := (ν.prod ν).map W
  let : IsProbabilityMeasure ξ := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  have haSq : a ^ 2 = (1 / 2 : ℝ) := by
    dsimp only [a]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hab : a ^ 2 + a ^ 2 = 1 := by rw [haSq]; norm_num
  have hξ := normalizedConvolution_isotropy n ν ν hmean hmean hcov hcov a a hab
  have hmeanξ : ∀ i : Fin n, (∫ x : E, x i ∂ξ) = 0 := hξ.2.1
  have hcovξ : ∀ i j : Fin n, (∫ x : E, x i * x j ∂ξ) = if i = j then (1 : ℝ) else 0 := hξ.2.2
  have hPone : (1 : ℝ≥0) ≤ P := isotropic_poincare_bound_ge_one n hn ν hmean hcov P hP
  let ρ : Measure E → ℝ → E → ℝ := fun κ t =>
    gaussianSmoothingDensity n κ (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
  let I : ℝ → ℝ := fun t => (relativeFisherMeasure n (ouInitialLaw n ν t)).toReal
  let K : ℝ → ℝ := fun t => ∫ x, ∑ i : Fin n,
    ‖gradient (fun y => gaussianRelativeScore n (ρ ν t) y i) x‖ ^ 2 ∂ouInitialLaw n ν t
  let S : ℝ → ℝ := fun t => (relativeFisherMeasure n (ouInitialLaw n ξ t)).toReal
  let L : ℝ → ℝ := fun t => ∫ x, ∑ i : Fin n,
    ‖gradient (fun y => gaussianRelativeScore n (ρ ξ t) y i) x‖ ^ 2 ∂ouInitialLaw n ξ t
  have hνFTC (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
      IntervalIntegrable I volume u v ∧ IntervalIntegrable K volume u v ∧
        I v - I u = ∫ r in u..v, -2 * I r - 2 * K r :=
    (ou_relative_fisher_dissipation_integrated n ν hmean hcov u v hu huv).2
  have hξFTC (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
      IntervalIntegrable S volume u v ∧ IntervalIntegrable L volume u v ∧
        S v - S u = ∫ r in u..v, -2 * S r - 2 * L r :=
    (ou_relative_fisher_dissipation_integrated n ξ hmeanξ hcovξ u v hu huv).2
  have hI0 (r : ℝ) (_hr : 0 < r) : 0 ≤ I r := ENNReal.toReal_nonneg
  have hS0 (r : ℝ) (_hr : 0 < r) : 0 ≤ S r := ENNReal.toReal_nonneg
  have hK0 (r : ℝ) (_hr : 0 < r) : 0 ≤ K r :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hL0 (r : ℝ) (_hr : 0 < r) : 0 ≤ L r :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hgap (r : ℝ) (hr : 0 < r) :
      (1 / (4 * (P : ℝ))) * (I r + K r) ≤ (K r + 2 * I r) - (L r + 2 * S r) := by
    have h := ou_convolution_hessian_regression_deficit n f f hf hf hlc hlc hmean hmean hcov hcov
      P hPone hP hP a a ha.ne' ha.ne' hab r hr
    change a ^ 2 * (K r + 2 * I r) + a ^ 2 * (K r + 2 * I r) - (L r + 2 * S r) ≥
      (a ^ 2 * a ^ 2) / (2 * (P : ℝ)) * (I r + K r + I r + K r) at h
    rw [haSq] at h
    have hcoef : ((1 / 2 : ℝ) * (1 / 2)) / (2 * (P : ℝ)) * (I r + K r + I r + K r) =
        (1 / (4 * (P : ℝ))) * (I r + K r) := by ring
    rw [hcoef] at h
    linarith
  have hscalar := positive_time_dissipation_gap_bound I K S L
    (fun u v hu huv => (hνFTC u v hu huv).1) (fun u v hu huv => (hνFTC u v hu huv).2.1)
    (fun u v hu huv => (hξFTC u v hu huv).1) (fun u v hu huv => (hξFTC u v hu huv).2.1)
    (fun u v hu huv => (hνFTC u v hu huv).2.2) (fun u v hu huv => (hξFTC u v hu huv).2.2)
    hI0 hK0 hS0 hL0 (1 / (4 * (P : ℝ))) (by positivity) hgap s hs
  refine ⟨(ou_isotropic_relativeFisher_toReal n ν hmean hcov s hs).1,
    (ou_isotropic_relativeFisher_toReal n ξ hmeanξ hcovξ s hs).1, ?_⟩
  change S s ≤ (1 - 1 / (8 * (P : ℝ))) * I s
  have hcoef : (1 / (4 * (P : ℝ))) / 2 = 1 / (8 * (P : ℝ)) := by ring
  rw [hcoef] at hscalar
  nlinarith

end AffineFKProof
