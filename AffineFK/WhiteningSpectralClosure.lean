module

public import AffineFK.GaussianGroundstateWhitening
public import AffineFK.InformationSpectrumLaw
public import AffineFK.DirichletLinearEigenvalue
public import AffineFK.Scalar

/-!
# The conditional analytic closure of the symmetric-body argument

The actual Gaussian-weighted weak groundstate law supplies the whitening
construction. The proved information-to-spectrum theorem applies to that
one actual law, and the genuine H0 linear pullback returns the bound to
the original domain. The final absorption uses the manuscript's exact
factor of eight. A uniform covariance lower bound and the required
groundstate log-concavity remain explicit inputs; their existence is not
asserted by this conditional theorem.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Set
open scoped ENNReal

def whiteningSpectralCoefficient (c : ℝ) : ℝ :=
  (4 / c) * informationSpectrumConstant (2 / c)

def whiteningSpectralConstant (c : ℝ) : ℝ :=
  4 * whiteningSpectralCoefficient c + 8 * (whiteningSpectralCoefficient c) ^ 2

theorem whiteningSpectralCoefficient_pos (c : ℝ) (hc : 0 < c) (hcOne : c ≤ 1) :
    0 < whiteningSpectralCoefficient c := by
  have hP : (2 : ℝ) ≤ 2 / c := (le_div_iff₀ hc).mpr (by nlinarith)
  exact mul_pos (div_pos (by norm_num) hc) (informationSpectrumConstant_pos _ hP)

theorem whiteningSpectralConstant_pos (c : ℝ) (hc : 0 < c) (hcOne : c ≤ 1) :
    0 < whiteningSpectralConstant c := by
  have h := whiteningSpectralCoefficient_pos c hc hcOne
  unfold whiteningSpectralConstant
  positivity

theorem dirichletLinearImage_interior (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    dirichletLinearImage n A (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) =
      (⟨interior (A '' K), isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) := by
  apply Opens.ext
  rw [dirichletLinearImage_coe]
  exact A.toHomeomorph.image_interior K

set_option maxHeartbeats 1000000 in
theorem symmetric_body_eigenvalue_bound_of_gaussian_groundstate (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty) (hKeven : ∀ x, -x ∈ K ↔ x ∈ K)
    (ψ : dirichletSobolev n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))))
    (hweak : IsDirichletWeakEigenfunction n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n)))
      (dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n)))).toReal ψ)
    (hψ : ψ ≠ 0)
    (hψ0 : ∀ᵐ x ∂volume, 0 ≤ dirichletValue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ψ x)
    [Measure.IsNegInvariant (densityMeasure n (gaussianGroundstateDensity n
      (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ψ))]
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hgLaw : densityMeasure n (gaussianGroundstateDensity n
      (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ψ) = densityMeasure n g)
    (hgTilt : LogConcaveDensity (fun x => ENNReal.ofReal
      (g x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2))))
    (c α : ℝ) (hc : 0 < c) (hcα : c ≤ α) (hαOne : α ≤ 1)
    (hcovX : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
      ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = if i = j then α else 0) :
    0 < whiteningSpectralConstant c ∧
      dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≠ ∞ ∧
      (dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n)))).toReal ≤
        whiteningSpectralConstant c * n ∧
      dirichletEigenvalue n (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
        ENNReal.ofReal (whiteningSpectralConstant c * n) := by
  let U : Opens (EuclideanSpace ℝ (Fin n)) := ⟨interior K, isOpen_interior⟩
  have hfinite : dirichletEigenvalue n U ≠ ∞ := dirichletEigenvalue_ne_top n U hinterior
  let ell := (dirichletEigenvalue n U).toReal
  let ν := ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K
  let η := densityMeasure n (gaussianGroundstateDensity n U ψ)
  let ζ := whitenedSumLaw n ν η α
  let D := whitenedSupportBody n η α K
  have hcOne : c ≤ 1 := hcα.trans hαOne
  have hα : 0 < α := hc.trans_le hcα
  have hPtwo : (2 : ℝ) ≤ 2 / c := (le_div_iff₀ hc).mpr (by nlinarith)
  have hKpos := gaussianPosition_gaussian_pos_of_volume_pos n K
    ((isOpen_interior.measure_pos volume hinterior).trans_le (measure_mono interior_subset))
  obtain ⟨A, h, hh, _hh0, hhlc, hlaw, hprob, heven, _hL2, hmean, hcov,
      hDimage, hAnorm, hDcompact, hDconv, hsupp, hP, _hJfin, _hJbound, hIfin, hIbound, _hIenn⟩ :=
    gaussian_groundstate_whitening_construction n K hK hconv hKeven hKpos U interior_subset
      ell ψ hweak hψ hψ0 g hg hg0 hgLaw hgTilt α hα hαOne hcovX
  let : IsProbabilityMeasure ζ := hprob
  let : Measure.IsNegInvariant ζ := heven
  have hDA : D = A '' K := hDimage
  have hImageInterior : A '' interior K = interior (A '' K) := A.toHomeomorph.image_interior K
  have hDinterior : (interior D).Nonempty := by
    rw [hDA, ← hImageInterior]
    exact hinterior.image A
  have hDeven : ∀ x, -x ∈ D ↔ x ∈ D := whitenedSupportBody_even n η α K hKeven
  have hCP : poincareConstant n ζ ≤ ENNReal.ofReal (2 / c) := hP.trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by norm_num) hc hcα))
  have hspec := information_spectrum_law_bound (2 / c) hPtwo n hn ζ
    ⟨h, hh, hlaw, hhlc⟩ hmean hcov hCP hIfin D hDcompact hDconv hDinterior hDeven hsupp
  have hCs : 0 ≤ informationSpectrumConstant (2 / c) := (informationSpectrumConstant_pos _ hPtwo).le
  have hspec' : dirichletEigenvalue n (⟨interior D, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal (informationSpectrumConstant (2 / c) *
        ((n : ℝ) + Real.sqrt ((n : ℝ) * (8 * ell + n)))) := hspec.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl (n : ℝ))
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hIbound (Nat.cast_nonneg n)))) hCs))
  have hAU : dirichletLinearImage n A U =
      (⟨interior D, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) := by
    change dirichletLinearImage n A (⟨interior K, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) = _
    rw [dirichletLinearImage_interior, ← hDA]
  have hAnormC : ‖A.toContinuousLinearMap‖ ^ 2 ≤ 4 / c := hAnorm.trans
    (div_le_div_of_nonneg_left (by norm_num) hc hcα)
  have hEigenBound : dirichletEigenvalue n U ≤ ENNReal.ofReal
      (whiteningSpectralCoefficient c * ((n : ℝ) + Real.sqrt ((n : ℝ) * (8 * ell + n)))) := by
    have hlinear := dirichletEigenvalue_linear_pullback_le n hn A U
    rw [hAU] at hlinear
    calc
      _ ≤ ENNReal.ofReal (‖A.toContinuousLinearMap‖ ^ 2) *
          dirichletEigenvalue n (⟨interior D, isOpen_interior⟩ : Opens (EuclideanSpace ℝ (Fin n))) := hlinear
      _ ≤ ENNReal.ofReal (4 / c) * ENNReal.ofReal (informationSpectrumConstant (2 / c) *
          ((n : ℝ) + Real.sqrt ((n : ℝ) * (8 * ell + n)))) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hAnormC) hspec'
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 / c)]
        congr 1
        dsimp only [whiteningSpectralCoefficient]
        ring
  have hA0 : 0 ≤ whiteningSpectralCoefficient c := (whiteningSpectralCoefficient_pos c hc hcOne).le
  have hEigenReal : ell ≤ whiteningSpectralCoefficient c *
      ((n : ℝ) + Real.sqrt ((n : ℝ) * (8 * ell + n))) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEigenBound
    rwa [ENNReal.toReal_ofReal (mul_nonneg hA0 (add_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)))] at h
  have hbound : ell ≤ whiteningSpectralConstant c * n :=
    absorb_information_bound (whiteningSpectralCoefficient c) n ell hA0 (Nat.cast_nonneg n)
      ENNReal.toReal_nonneg hEigenReal
  refine ⟨whiteningSpectralConstant_pos c hc hcOne, hfinite, hbound, ?_⟩
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hbound

end AffineFKProof
