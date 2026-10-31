module

public import AffineFK.GroundstateGaussianProbability
public import AffineFK.FisherInformationMeasure

/-!
# Actual Sobolev Fisher information of the Gaussian-weighted ground state

Normalisation is carried out inside the genuine H0^1 graph. For a
nonnegative original element the scaled value is the actual square root
of its square-density. The Fisher information is the existing canonical
law functional, not a new score-energy proxy. No finite-information or
computed-energy conclusion is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped ENNReal RealInnerProductSpace

set_option maxHeartbeats 1000000 in
theorem gaussianGroundstateDensity_sqrt_h0 (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ψ : dirichletSobolev n U)
    (hψ : ψ ≠ 0) (hψ0 : ∀ᵐ x ∂volume, 0 ≤ dirichletValue n U ψ x) :
    ∃ v : dirichletSobolev n U,
      (dirichletValue n U v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        (fun x => Real.sqrt (gaussianGroundstateDensity n U ψ x)) ∧
      (∫ x, ‖dirichletGradient n U v x‖ ^ 2) =
        (∫ x, ‖dirichletGradient n U (gaussianDirichletFactor n U ψ) x‖ ^ 2) /
          gaussianGroundstateMass n U ψ := by
  let w := gaussianDirichletFactor n U ψ
  let Z := gaussianGroundstateMass n U ψ
  let c := (Real.sqrt Z)⁻¹
  have hZ : 0 < Z := gaussianGroundstateMass_pos n U ψ hψ
  have h0w : ∀ᵐ x ∂volume, 0 ≤ dirichletValue n U w x := by
    filter_upwards [gaussianDirichletFactor_value n U ψ, hψ0] with x hx h0
    rw [hx]
    exact mul_nonneg (groundstateGaussianFactor_pos n x).le h0
  have hscaled : (dirichletValue n U (c • w) : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => c * dirichletValue n U w x := by
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul c (dirichletValue n U w)] with x hx
    simpa only [Pi.smul_apply, smul_eq_mul] using hx
  refine ⟨c • w, ?_, ?_⟩
  · filter_upwards [hscaled, h0w] with x hx h0
    rw [hx]
    change c * dirichletValue n U w x = Real.sqrt ((dirichletValue n U w x) ^ 2 / Z)
    rw [Real.sqrt_div (sq_nonneg _) Z, Real.sqrt_sq h0]
    dsimp [c]
    ring
  · have hc : c ^ 2 = Z⁻¹ := by
      dsimp [c]
      rw [inv_pow, Real.sq_sqrt hZ.le]
    calc
      _ = ‖dirichletGradient n U (c • w)‖ ^ 2 := (l2_norm_sq_integral volume _).symm
      _ = c ^ 2 * ‖dirichletGradient n U w‖ ^ 2 := by
        rw [map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ = Z⁻¹ * (∫ x, ‖dirichletGradient n U w x‖ ^ 2) :=
        congrArg₂ (fun p q : ℝ => p * q) hc (l2_norm_sq_integral volume (dirichletGradient n U w))
      _ = _ := (mul_comm Z⁻¹ _).trans (div_eq_mul_inv _ Z).symm

set_option maxHeartbeats 1000000 in
theorem gaussianGroundstateDensity_fisher_identity (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ell : ℝ) (ψ : dirichletSobolev n U)
    (hweak : IsDirichletWeakEigenfunction n U ell ψ) (hψ : ψ ≠ 0)
    (hψ0 : ∀ᵐ x ∂volume, 0 ≤ dirichletValue n U ψ x) :
    IsProbabilityMeasure (densityMeasure n (gaussianGroundstateDensity n U ψ)) ∧
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      (densityMeasure n (gaussianGroundstateDensity n U ψ)) ∧
    ordinaryFisherMeasure n (densityMeasure n (gaussianGroundstateDensity n U ψ)) =
      ENNReal.ofReal (4 * ell +
        ∫ x, ‖x‖ ^ 2 ∂densityMeasure n (gaussianGroundstateDensity n U ψ)) := by
  obtain ⟨v, hv, hgrad⟩ := gaussianGroundstateDensity_sqrt_h0 n U ψ hψ hψ0
  have henergy := gaussian_dirichlet_groundstate_energy n U ell ψ hweak
  have hmoment := gaussianGroundstateDensity_second_moment n U ψ
  refine ⟨gaussianGroundstateDensity_probability n U ψ hψ, hmoment.1, ?_⟩
  rw [ordinaryFisherMeasure_density n _ (gaussianGroundstateDensity_measurable n U ψ)
    (ae_of_all volume (gaussianGroundstateDensity_nonneg n U ψ))]
  have hv' : (unweightedValue n v.val : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (gaussianGroundstateDensity n U ψ x) := hv
  rw [fisherInformation_eq_graph n _ v.val hv']
  change ENNReal.ofReal (4 * ∫ x, ‖dirichletGradient n U v x‖ ^ 2) = _
  rw [hgrad, henergy.2.2.2, hmoment.2]
  congr 1
  change 4 * ((ell * gaussianGroundstateMass n U ψ + (1 / 4 : ℝ) *
      (∫ x, ‖x‖ ^ 2 * (dirichletValue n U (gaussianDirichletFactor n U ψ) x) ^ 2)) /
        gaussianGroundstateMass n U ψ) =
    4 * ell + (∫ x, ‖x‖ ^ 2 * (dirichletValue n U (gaussianDirichletFactor n U ψ) x) ^ 2) /
      gaussianGroundstateMass n U ψ
  field_simp [(gaussianGroundstateMass_pos n U ψ hψ).ne']

theorem dirichletWeakEigenfunction_eigenvalue_nonneg (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ell : ℝ) (ψ : dirichletSobolev n U)
    (hweak : IsDirichletWeakEigenfunction n U ell ψ) (hψ : ψ ≠ 0) : 0 ≤ ell := by
  have hvalue : dirichletValue n U ψ ≠ 0 := by
    intro h
    apply hψ
    apply dirichletValue_injective n U
    simpa only [map_zero] using h
  rw [← dirichletWeakEigenfunction_rayleigh n U ell ψ hweak hvalue, dirichletRayleigh]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem gaussianGroundstateDensity_fisher_real_identity (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ell : ℝ) (ψ : dirichletSobolev n U)
    (hweak : IsDirichletWeakEigenfunction n U ell ψ) (hψ : ψ ≠ 0)
    (hψ0 : ∀ᵐ x ∂volume, 0 ≤ dirichletValue n U ψ x) :
    IsProbabilityMeasure (densityMeasure n (gaussianGroundstateDensity n U ψ)) ∧
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      (densityMeasure n (gaussianGroundstateDensity n U ψ)) ∧
    ordinaryFisherMeasure n (densityMeasure n (gaussianGroundstateDensity n U ψ)) ≠ ∞ ∧
    (ordinaryFisherMeasure n (densityMeasure n (gaussianGroundstateDensity n U ψ))).toReal =
      4 * ell + ∫ x, ‖x‖ ^ 2 ∂densityMeasure n (gaussianGroundstateDensity n U ψ) := by
  have h := gaussianGroundstateDensity_fisher_identity n U ell ψ hweak hψ hψ0
  have hnonneg : 0 ≤ 4 * ell +
      ∫ x, ‖x‖ ^ 2 ∂densityMeasure n (gaussianGroundstateDensity n U ψ) :=
    add_nonneg (mul_nonneg (by norm_num) (dirichletWeakEigenfunction_eigenvalue_nonneg n U ell ψ hweak hψ))
      (integral_nonneg fun x => sq_nonneg ‖x‖)
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rw [h.2.2]
    exact ENNReal.ofReal_ne_top
  · rw [h.2.2, ENNReal.toReal_ofReal hnonneg]

end AffineFKProof
