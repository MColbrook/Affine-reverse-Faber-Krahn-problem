module

public import AffineFK.OUFisherBochner
public import AffineFK.OUDensityPDEScoreSpatial
public import AffineFK.OUFisherCompactTime
public import AffineFK.OUFisherTimeIntegrability

/-!
# The actual compact OU Fisher--Bochner identity

The previously proved pointwise temporal derivative is combined with the
independently constructed deterministic Bochner formula. Compact spatial
duality then transfers the OU operator to the actual test function.
Every use of Bochner integral linearity has genuine L1 premises.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set
open scoped Topology Distributions Interval ContDiff

theorem ou_ordinary_fisher_density_hasDerivAt_bochner (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
      gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
    let f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r y =>
      ‖gradient (fun z => Real.log (ρ r z)) y‖ ^ 2 * ρ r y
    HasDerivAt (fun r => f r x)
      (ouDensitySpatialOperator n (f t) x + 2 * f t x -
        2 * ρ t x * matrixHilbertSchmidtSq (densityLogHessian n (ρ t) x)) t := by
  have h := ou_ordinary_fisher_density_hasDerivAt_spatial_operator n ν hU t ht x
  dsimp only at h
  rw [ou_fisher_bochner_identity n _ (gaussianSmoothingDensity_smooth n ν (Real.exp (-t)) _)
    (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain t ht).2.1) x] at h
  exact h

theorem ou_fisher_bochner_test_identity (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hpos : ∀ x, 0 < ρ x)
    (hf : Integrable (fun x => ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 * ρ x))
    (hg : Integrable (fun x => ρ x * matrixHilbertSchmidtSq (densityLogHessian n ρ x)))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, φ x * (2 * (∑ i, gradient (fun y => Real.log (ρ y)) x i *
      gradient (fun y => ouDensitySpatialOperator n ρ y / ρ y) x i) * ρ x +
        ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 * ouDensitySpatialOperator n ρ x)) =
      (∫ x, ouTestGenerator n φ x * (‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 * ρ x)) +
      2 * (∫ x, φ x * (‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 * ρ x)) -
      2 * (∫ x, φ x * (ρ x * matrixHilbertSchmidtSq (densityLogHessian n ρ x))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let f : E → ℝ := fun x => ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 * ρ x
  let g : E → ℝ := fun x => ρ x * matrixHilbertSchmidtSq (densityLogHessian n ρ x)
  let B := TestFunction.toBoundedContinuousFunctionCLM ℝ φ
  have hfφ : Integrable (fun x => φ x * f x) := by
    have hfi : Integrable f := hf
    exact (hfi.mul_bdd φ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => B.norm_coe_le_norm x)).congr
        (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hgφ : Integrable (fun x => φ x * g x) := by
    have hgi : Integrable g := hg
    exact (hgi.mul_bdd φ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => B.norm_coe_le_norm x)).congr
        (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hfsm : ContDiff ℝ ∞ f := ((logDensity_ordinaryScore_smooth n ρ hρ hpos).norm_sq (𝕜 := ℝ)).mul hρ
  have hdual := ouDensitySpatialOperator_test_duality n f hfsm φ
  calc
    _ = ∫ x, φ x * ouDensitySpatialOperator n f x +
        2 * (φ x * f x) - 2 * (φ x * g x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [ou_fisher_bochner_identity n ρ hρ hpos x]
        change φ x * (_ + 2 * f x - 2 * ρ x * matrixHilbertSchmidtSq (densityLogHessian n ρ x)) = _
        dsimp only [g]
        ring
    _ = (∫ x, φ x * ouDensitySpatialOperator n f x) +
        2 * (∫ x, φ x * f x) - 2 * (∫ x, φ x * g x) := by
      rw [integral_sub (f := fun x => φ x * ouDensitySpatialOperator n f x + 2 * (φ x * f x))
        (g := fun x => 2 * (φ x * g x)) (hdual.1.add (hfφ.const_mul 2)) (hgφ.const_mul 2),
        integral_add (f := fun x => φ x * ouDensitySpatialOperator n f x)
          (g := fun x => 2 * (φ x * f x)) hdual.1 (hfφ.const_mul 2), integral_const_mul, integral_const_mul]
    _ = _ := by rw [hdual.2.2]

theorem gaussianSmoothing_fisher_energy_densities_integrable (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    Integrable (fun x => ‖gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x‖ ^ 2 *
      gaussianSmoothingDensity n ν a b x) ∧
    Integrable (fun x => gaussianSmoothingDensity n ν a b x *
      matrixHilbertSchmidtSq (densityLogHessian n (gaussianSmoothingDensity n ν a b) x)) := by
  have hρ := (gaussianSmoothingDensity_continuous n ν a b).measurable
  have hpos (x) := (gaussianSmoothingDensity_pos n ν a b hb x).le
  have hf := smooth_density_weight_integrable n _ hρ hpos _
    (gaussianSmoothing_ordinary_fisher_energy_bound n ν a b hb).1
  have hg := smooth_density_weight_integrable n _ hρ hpos _
    (gaussianSmoothing_logHessian_squared_energy_bound n ν a b hb).1
  exact ⟨hf.congr (Filter.Eventually.of_forall fun x => mul_comm _ _), hg⟩

theorem ou_ordinary_fisher_compact_bochner_integral (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
      gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
    let f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r x =>
      ‖gradient (fun y => Real.log (ρ r y)) x‖ ^ 2 * ρ r x
    let g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r x =>
      ρ r x * matrixHilbertSchmidtSq (densityLogHessian n (ρ r) x)
    let D : ℝ → ℝ := fun r => (∫ x, ouTestGenerator n φ x * f r x) +
      2 * (∫ x, φ x * f r x) - 2 * (∫ x, φ x * g r x)
    IntervalIntegrable D volume s t ∧
      (∫ r in s..t, D r) = (∫ x, φ x * f t x) - ∫ x, φ x * f s x := by
  let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
    gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
  let score : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun r => gradient (fun x => Real.log (ρ r x))
  let f : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r x => ‖score r x‖ ^ 2 * ρ r x
  let g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r x =>
    ρ r x * matrixHilbertSchmidtSq (densityLogHessian n (ρ r) x)
  let A : ℝ → ℝ := fun r => ∫ x, φ x *
    (2 * (∑ i, score r x i * ouOrdinaryScoreTimeDerivative n ν r x i) * ρ r x +
      ‖score r x‖ ^ 2 * ouDensityTimeDerivative n ν r x)
  let D : ℝ → ℝ := fun r => (∫ x, ouTestGenerator n φ x * f r x) +
    2 * (∫ x, φ x * f r x) - 2 * (∫ x, φ x * g r x)
  change IntervalIntegrable D volume s t ∧
    (∫ r in s..t, D r) = (∫ x, φ x * f t x) - ∫ x, φ x * f s x
  have hCompact : IntervalIntegrable A volume s t ∧
      (∫ r in s..t, A r) = (∫ x, φ x * f t x) - ∫ x, φ x * f s x :=
    ou_ordinary_fisher_compact_time_integral n ν hU φ s t hs hst
  have heq (r : ℝ) (hr : 0 < r) : A r = D r := by
    dsimp only [A, D, f, g, score, ρ]
    simp_rw [ou_ordinary_score_time_derivative_eq_gradient n ν hU r hr,
      ou_density_time_derivative_eq_spatial_operator n ν hU r hr]
    have hi := gaussianSmoothing_fisher_energy_densities_integrable n ν (Real.exp (-r))
      (Real.sqrt (1 - Real.exp (-2 * r))) (ou_smoothing_scale_domain r hr).2.1
    exact ou_fisher_bochner_test_identity n _ (gaussianSmoothingDensity_smooth n ν _ _)
      (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain r hr).2.1) hi.1 hi.2 φ
  have hAE : A =ᵐ[volume.restrict (Ι s t)] D := by
    rw [uIoc_of_le hst]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact heq r (hs.trans hr.1)
  exact ⟨hCompact.1.congr_ae hAE, (intervalIntegral.integral_congr_ae_restrict hAE).symm.trans hCompact.2⟩

end AffineFKProof
