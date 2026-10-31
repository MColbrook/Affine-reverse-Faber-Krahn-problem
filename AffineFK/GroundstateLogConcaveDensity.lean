module

public import AffineFK.GroundstateGaussianLawBounds
public import AffineFK.LogConcaveDensityCalculus
public import AffineFK.GaussianLogConcavity
public import AffineFK.SteinSumLaw

/-!
# The actual weighted density from a log-concave eigenfunction representative

A measurable nonnegative even log-concave representative r of the genuine
H0 value gives q(x)=exp(-norm(x)^2/2)*r(x)^2/Z. The actual multiplier-value
identity identifies q almost everywhere with the existing normalized
groundstate density. Its quadratic exponential tilt is exactly r^2/Z,
so strong log-concavity and evenness concern the same actual law. No
pointwise property is asserted for an arbitrary chosen Lp representative.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped ENNReal

def gaussianGroundstateRepresentativeDensity (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ψ : dirichletSobolev n U)
    (r : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  groundstateGaussianWeight n x * (r x) ^ 2 / gaussianGroundstateMass n U ψ

theorem gaussianGroundstateRepresentativeDensity_measurable (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ψ : dirichletSobolev n U)
    (r : EuclideanSpace ℝ (Fin n) → ℝ) (hr : Measurable r) :
    Measurable (gaussianGroundstateRepresentativeDensity n U ψ r) :=
  ((groundstateGaussianWeight_smooth n).continuous.measurable.mul (hr.pow_const 2)).div_const _

theorem gaussianGroundstateRepresentativeDensity_nonneg (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ψ : dirichletSobolev n U)
    (r : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ gaussianGroundstateRepresentativeDensity n U ψ r x := by
  exact div_nonneg (mul_nonneg (groundstateGaussianWeight_bound n x).1.le (sq_nonneg _))
    (integral_nonneg fun _ => sq_nonneg _)

theorem gaussianGroundstateRepresentativeDensity_ae_eq (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ψ : dirichletSobolev n U)
    (r : EuclideanSpace ℝ (Fin n) → ℝ)
    (hr : r =ᵐ[volume] (dirichletValue n U ψ : EuclideanSpace ℝ (Fin n) → ℝ)) :
    gaussianGroundstateRepresentativeDensity n U ψ r =ᵐ[volume] gaussianGroundstateDensity n U ψ := by
  filter_upwards [hr, gaussianDirichletFactor_value n U ψ] with x hx hfactor
  change groundstateGaussianWeight n x * (r x) ^ 2 / gaussianGroundstateMass n U ψ =
    (dirichletValue n U (gaussianDirichletFactor n U ψ) x) ^ 2 / gaussianGroundstateMass n U ψ
  apply congrArg (fun z : ℝ => z / gaussianGroundstateMass n U ψ)
  calc
    _ = groundstateGaussianWeight n x * (dirichletValue n U ψ x) ^ 2 :=
      congrArg (fun z : ℝ => groundstateGaussianWeight n x * z ^ 2) hx
    _ = (groundstateGaussianFactor n x) ^ 2 * (dirichletValue n U ψ x) ^ 2 :=
      congrArg (fun z : ℝ => z * (dirichletValue n U ψ x) ^ 2)
        (groundstateGaussianFactor_sq n x).symm
    _ = (groundstateGaussianFactor n x * dirichletValue n U ψ x) ^ 2 :=
      (mul_pow (groundstateGaussianFactor n x) (dirichletValue n U ψ x) 2).symm
    _ = _ := congrArg (fun z : ℝ => z ^ 2) hfactor.symm

theorem gaussianGroundstateRepresentativeDensity_law (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ψ : dirichletSobolev n U)
    (r : EuclideanSpace ℝ (Fin n) → ℝ)
    (hr : r =ᵐ[volume] (dirichletValue n U ψ : EuclideanSpace ℝ (Fin n) → ℝ)) :
    densityMeasure n (gaussianGroundstateRepresentativeDensity n U ψ r) =
      densityMeasure n (gaussianGroundstateDensity n U ψ) := by
  apply withDensity_congr_ae
  exact (gaussianGroundstateRepresentativeDensity_ae_eq n U ψ r hr).mono
    fun _ hx => congrArg ENNReal.ofReal hx

theorem gaussianGroundstateRepresentativeDensity_even (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ψ : dirichletSobolev n U)
    (r : EuclideanSpace ℝ (Fin n) → ℝ) (heven : ∀ x, r (-x) = r x)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussianGroundstateRepresentativeDensity n U ψ r (-x) =
      gaussianGroundstateRepresentativeDensity n U ψ r x := by
  simp only [gaussianGroundstateRepresentativeDensity, groundstateGaussianWeight, norm_neg, heven]

theorem gaussianGroundstateRepresentativeDensity_strong_logConcave (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ψ : dirichletSobolev n U) (hψ : ψ ≠ 0)
    (r : EuclideanSpace ℝ (Fin n) → ℝ) (hr0 : ∀ x, 0 ≤ r x)
    (hrlc : LogConcaveDensity (fun x => ENNReal.ofReal (r x))) :
    LogConcaveDensity (fun x => ENNReal.ofReal
      (gaussianGroundstateRepresentativeDensity n U ψ r x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2))) := by
  let Z := gaussianGroundstateMass n U ψ
  have hZ : 0 < Z := gaussianGroundstateMass_pos n U ψ hψ
  have hsq := logConcaveDensity_mul _ _ hrlc hrlc
  have h := logConcaveDensity_mul
    (fun _ : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal Z⁻¹) _
    (logConcaveDensity_const _) hsq
  have heq : (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal Z⁻¹ *
      (ENNReal.ofReal (r x) * ENNReal.ofReal (r x))) =
      (fun x => ENNReal.ofReal ((r x) ^ 2 / Z)) := by
    funext x
    rw [← ENNReal.ofReal_mul (hr0 x), ← ENNReal.ofReal_mul (inv_nonneg.mpr hZ.le)]
    congr 1
    ring
  rw [heq] at h
  have hcancel (x : EuclideanSpace ℝ (Fin n)) :
      gaussianGroundstateRepresentativeDensity n U ψ r x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2) =
        (r x) ^ 2 / Z := by
    have hexp : groundstateGaussianWeight n x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2) = 1 := by
      rw [groundstateGaussianWeight, ← Real.exp_add,
        show -(‖x‖ ^ 2 / 2) + (1 / 2 : ℝ) * ‖x‖ ^ 2 = 0 by ring, Real.exp_zero]
    calc
      _ = ((r x) ^ 2 / Z) * (groundstateGaussianWeight n x *
          Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)) := by dsimp only [gaussianGroundstateRepresentativeDensity, Z]; ring
      _ = _ := by rw [hexp, mul_one]
  simpa only [hcancel] using h

theorem gaussianGroundstateDensity_neg_invariant_of_representative (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ψ : dirichletSobolev n U)
    (r : EuclideanSpace ℝ (Fin n) → ℝ) (hr : Measurable r)
    (heven : ∀ x, r (-x) = r x)
    (hrAE : r =ᵐ[volume] (dirichletValue n U ψ : EuclideanSpace ℝ (Fin n) → ℝ)) :
    Measure.IsNegInvariant (densityMeasure n (gaussianGroundstateDensity n U ψ)) := by
  rw [← gaussianGroundstateRepresentativeDensity_law n U ψ r hrAE]
  apply even_density_neg_invariant volume _
    (gaussianGroundstateRepresentativeDensity_measurable n U ψ r hr).ennreal_ofReal
  intro x
  exact congrArg ENNReal.ofReal (gaussianGroundstateRepresentativeDensity_even n U ψ r heven x)

theorem gaussianGroundstateDensity_strong_logConcave_representative (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ψ : dirichletSobolev n U) (hψ : ψ ≠ 0)
    (r : EuclideanSpace ℝ (Fin n) → ℝ) (hr : Measurable r) (hr0 : ∀ x, 0 ≤ r x)
    (heven : ∀ x, r (-x) = r x)
    (hrlc : LogConcaveDensity (fun x => ENNReal.ofReal (r x)))
    (hrAE : r =ᵐ[volume] (dirichletValue n U ψ : EuclideanSpace ℝ (Fin n) → ℝ)) :
    (∀ᵐ x ∂volume, 0 ≤ dirichletValue n U ψ x) ∧
      Measure.IsNegInvariant (densityMeasure n (gaussianGroundstateDensity n U ψ)) ∧
      ∃ q : EuclideanSpace ℝ (Fin n) → ℝ,
        Measurable q ∧ (∀ x, 0 ≤ q x) ∧ (∀ x, q (-x) = q x) ∧
        densityMeasure n (gaussianGroundstateDensity n U ψ) = densityMeasure n q ∧
        LogConcaveDensity (fun x => ENNReal.ofReal (q x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2))) := by
  refine ⟨?_, gaussianGroundstateDensity_neg_invariant_of_representative n U ψ r hr heven hrAE,
    gaussianGroundstateRepresentativeDensity n U ψ r,
    gaussianGroundstateRepresentativeDensity_measurable n U ψ r hr,
    gaussianGroundstateRepresentativeDensity_nonneg n U ψ r,
    gaussianGroundstateRepresentativeDensity_even n U ψ r heven,
    (gaussianGroundstateRepresentativeDensity_law n U ψ r hrAE).symm,
    gaussianGroundstateRepresentativeDensity_strong_logConcave n U ψ hψ r hr0 hrlc⟩
  filter_upwards [hrAE] with x hx
  rw [← hx]
  exact hr0 x

end AffineFKProof
