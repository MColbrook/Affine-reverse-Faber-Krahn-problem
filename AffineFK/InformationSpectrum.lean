module

public import AffineFK.GaussianDilationRate
public import AffineFK.BridgeProfileEigenvalue
public import AffineFK.SymmetricConvexInterior

/-!
# The actual information-to-Dirichlet-spectrum estimate

The constant is an explicit function of the Poincare bound alone. The
Gaussian profile, bridge survival and genuine H0 Rayleigh estimate are
proved by the imported chain; none is a final hypothesis. This theorem
uses the original actual density law, not a freely chosen information or
eigenvalue function. It does not assert the main affine conclusion.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal NNReal Pointwise

def informationSpectrumExponent (P : ℝ) : ℝ :=
  2 + (-Real.log (1 - 1 / (8 * P)) / Real.log 2)

def informationSpectrumProfileCoefficient (P : ℝ) : ℝ :=
  (2 : ℝ) ^ (informationSpectrumExponent P / 2) * Real.sqrt (2 * P * (P - 1))

def informationSpectrumConstant (P : ℝ) : ℝ :=
  bridgeRayleighConstant (informationSpectrumExponent P) *
    max 1 (informationSpectrumProfileCoefficient P)

theorem informationSpectrumConstant_pos (P : ℝ) (hP : 2 ≤ P) :
    0 < informationSpectrumConstant P := by
  have hp : 2 < informationSpectrumExponent P := gaussian_dilation_exponent_gt_two P hP
  exact mul_pos (bridgeRayleighConstant_pos _ hp) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem information_spectrum_density_bound (n : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)] [Measure.IsNegInvariant (densityMeasure n f)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (f x)))
    (hmean : ∀ i : Fin n, (∫ x, x i ∂densityMeasure n f) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂densityMeasure n f) = if i = j then 1 else 0)
    (P : ℝ≥0) (hP : poincareConstant n (densityMeasure n f) ≤ (P : ℝ≥0∞))
    (hPtwo : (2 : ℝ) ≤ P) (hI : relativeFisherMeasure n (densityMeasure n f) ≠ ∞)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D) (hD : Convex ℝ D)
    (hinterior : (interior D).Nonempty) (hsymmetric : ∀ x, -x ∈ D ↔ x ∈ D)
    (hsupp : ∀ᵐ x ∂densityMeasure n f, x ∈ D) :
    dirichletEigenvalue n (⟨interior D, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal (informationSpectrumConstant P *
        ((n : ℝ) + Real.sqrt ((n : ℝ) * (relativeFisherMeasure n (densityMeasure n f)).toReal))) := by
  let p := informationSpectrumExponent P
  let s := Real.sqrt ((n : ℝ) * (relativeFisherMeasure n (densityMeasure n f)).toReal)
  let A := (2 : ℝ) ^ (p / 2) *
    Real.sqrt (2 * (P : ℝ) * ((P : ℝ) - 1) * (n : ℝ) *
      (relativeFisherMeasure n (densityMeasure n f)).toReal)
  have hprofile := gaussian_dilation_profile_of_finite_information n hn f hf hlc hmean hcov
    P hP hPtwo hI D hcompact hD hsupp
  have hp : 2 < p := hprofile.1
  have hA : 0 ≤ A := by positivity
  have hzero := symmetric_convex_zero_mem_interior n D hD hinterior hsymmetric
  have h := bridge_dirichletEigenvalue_le_profile_constant p hp n hn D hcompact hD hzero A hA
    (fun t ht => (hprofile.2 t ht).2)
  have hfac : A = informationSpectrumProfileCoefficient P * s := by
    have hP1 : 0 ≤ (P : ℝ) - 1 := by linarith
    have hprod : 0 ≤ 2 * (P : ℝ) * ((P : ℝ) - 1) := by positivity
    have heq : 2 * (P : ℝ) * ((P : ℝ) - 1) * (n : ℝ) *
        (relativeFisherMeasure n (densityMeasure n f)).toReal =
        (2 * (P : ℝ) * ((P : ℝ) - 1)) *
          ((n : ℝ) * (relativeFisherMeasure n (densityMeasure n f)).toReal) := by ring
    dsimp only [A, informationSpectrumProfileCoefficient, s, p]
    rw [heq, Real.sqrt_mul hprod]
    ring
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hCb : 0 ≤ bridgeRayleighConstant p := (bridgeRayleighConstant_pos p hp).le
  have hM : 1 ≤ max 1 (informationSpectrumProfileCoefficient P) := le_max_left _ _
  have hF : informationSpectrumProfileCoefficient P ≤ max 1 (informationSpectrumProfileCoefficient P) := le_max_right _ _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hcore : A + (n : ℝ) ≤ max 1 (informationSpectrumProfileCoefficient P) * ((n : ℝ) + s) := by
    rw [hfac]
    have hFn := mul_le_mul_of_nonneg_right hF hs
    have hMn := mul_le_mul_of_nonneg_right hM hn0
    nlinarith
  have hfinal := mul_le_mul_of_nonneg_left hcore hCb
  simpa only [informationSpectrumConstant, p, s, mul_assoc] using hfinal

end AffineFKProof
