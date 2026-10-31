module

public import AffineFK.SmoothDensitySobolev
public import AffineFK.DensityApproximationL1SquareRoot
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The ordinary no-moment score bridge for positive smooth densities

Actual probability mass gives square-root L2. The true ordinary logarithmic
score controls the genuine square-root gradient by the separately proved
pointwise identity, with no moment condition. Compact-test uniqueness
identifies an actual weak L2 ordinary score with that true gradient.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace ContDiff

theorem ordinaryWeakScore_smooth_density_integrable (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)] :
    Integrable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hmass : (∫⁻ x, ENNReal.ofReal (ρ x) ∂volume) = 1 := by
    have h := measure_univ (μ := densityMeasure n ρ)
    simpa only [densityMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using h
  exact (lintegral_ofReal_ne_top_iff_integrable hρ.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (hρpos x).le)).mp (by rw [hmass]; exact ENNReal.one_ne_top)

theorem ordinaryWeakScore_smooth_sqrt_L2 (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (hscore : MemLp (gradient (fun x => Real.log (ρ x))) 2 (densityMeasure n ρ)) :
    MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    MemLp (gradient (fun x => Real.sqrt (ρ x))) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ‖gradient (fun y => Real.sqrt (ρ y)) x‖ ^ 2) =
      (1 / 4 : ℝ) * ∫ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 ∂densityMeasure n ρ := by
  have hρL1 := ordinaryWeakScore_smooth_density_integrable n ρ hρ hρpos
  have hf := densityApproximation_sqrt_memLp volume ρ hρ.continuous.measurable
    (Filter.Eventually.of_forall fun x => (hρpos x).le) hρL1
  have hs2 := (memLp_two_iff_integrable_sq_norm hscore.aestronglyMeasurable).mp hscore
  have hweighted : Integrable (fun x => ρ x *
      ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2) volume := by
    have h := (integrable_withDensity_iff_integrable_smul'
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      hρ.continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hs2
    simpa only [ENNReal.toReal_ofReal (hρpos _).le, smul_eq_mul] using h
  have hg2 : Integrable (fun x => ‖gradient (fun y => Real.sqrt (ρ y)) x‖ ^ 2) volume := by
    apply (hweighted.const_mul (1 / 4 : ℝ)).congr
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [smooth_density_sqrt_gradient_norm n ρ hρ hρpos x]
      ring
  have hgcont : Continuous (gradient (fun x => Real.sqrt (ρ x))) := by
    have heq : gradient (fun x => Real.sqrt (ρ x)) =
        fun x => (Real.sqrt (ρ x) / 2) • gradient (fun y => Real.log (ρ y)) x :=
      funext (smooth_density_gradient_sqrt n ρ hρ hρpos)
    rw [heq]
    exact (hρ.continuous.sqrt.div_const 2).smul (continuous_log_density_gradient n ρ hρ hρpos)
  refine ⟨hf, (memLp_two_iff_integrable_sq_norm hgcont.aestronglyMeasurable).mpr hg2, ?_⟩
  rw [density_integral_eq n ρ hρ.continuous (fun x => (hρpos x).le), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [smooth_density_sqrt_gradient_norm n ρ hρ hρpos x]
    ring

theorem ordinaryWeakScore_smooth_sqrt_graph (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (hscore : MemLp (gradient (fun x => Real.log (ρ x))) 2 (densityMeasure n ρ)) :
    ∃ v : unweightedSobolevGraph n,
      (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] (fun x => Real.sqrt (ρ x)) ∧
      (unweightedGradient n v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
        gradient (fun x => Real.sqrt (ρ x)) ∧
      4 * (∫ x, ‖unweightedGradient n v x‖ ^ 2) =
        ∫ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 ∂densityMeasure n ρ := by
  obtain ⟨hf, hg, henergy⟩ := ordinaryWeakScore_smooth_sqrt_L2 n ρ hρ hρpos hscore
  obtain ⟨v, hv, hgv⟩ := unweighted_smooth_has_graph n (fun x => Real.sqrt (ρ x))
    (hρ.sqrt (fun x => (hρpos x).ne')) hf hg
  refine ⟨v, hv, hgv, ?_⟩
  have heq : (∫ x, ‖unweightedGradient n v x‖ ^ 2) =
      ∫ x, ‖gradient (fun y => Real.sqrt (ρ y)) x‖ ^ 2 :=
    integral_congr_ae (hgv.fun_comp fun z => ‖z‖ ^ 2)
  rw [heq, henergy]
  ring

theorem ordinaryWeakScore_smooth_identification (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : MemLp r 2 (densityMeasure n ρ))
    (hweak : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, r x i * φ x ∂densityMeasure n ρ) =
        -(∫ x, partialTest n i φ x ∂densityMeasure n ρ)) :
    r =ᵐ[densityMeasure n ρ] gradient (fun x => Real.log (ρ x)) ∧
    MemLp (gradient (fun x => Real.log (ρ x))) 2 (densityMeasure n ρ) ∧
    (∫ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 ∂densityMeasure n ρ) =
      ∫ x, ‖r x‖ ^ 2 ∂densityMeasure n ρ := by
  have hcoord (i : Fin n) : ∀ᵐ x ∂densityMeasure n ρ,
      r x i = gradient (fun y => Real.log (ρ y)) x i := by
    have hc : Continuous (fun x => gradient (fun y => Real.log (ρ y)) x i) := by
      have h := continuous_log_density_gradient n ρ hρ hρpos
      fun_prop
    apply ae_eq_of_integral_contDiff_smul_eq
      ((hr.eval_piLp i).integrable (by norm_num)).locallyIntegrable hc.locallyIntegrable
    intro ψ hψ hcompact
    let φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
      ⟨ψ, hψ, hcompact, Set.subset_univ _⟩
    have hl := hweak i φ
    have hg := (log_density_gradient_test_integration_by_parts n ρ hρ hρpos i φ).2.2
    have heq := hl.trans hg.symm
    change (∫ x, r x i * ψ x ∂densityMeasure n ρ) =
      ∫ x, gradient (fun y => Real.log (ρ y)) x i * ψ x ∂densityMeasure n ρ at heq
    simpa only [smul_eq_mul, mul_comm] using heq
  have hall : r =ᵐ[densityMeasure n ρ] gradient (fun x => Real.log (ρ x)) := by
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    ext i
    exact hx i
  refine ⟨hall, hr.ae_eq hall, ?_⟩
  exact integral_congr_ae (hall.symm.fun_comp fun z => ‖z‖ ^ 2)

theorem ordinaryWeakScore_smooth_sqrt_graph_of_weak_score (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hr : MemLp r 2 (densityMeasure n ρ))
    (hweak : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, r x i * φ x ∂densityMeasure n ρ) =
        -(∫ x, partialTest n i φ x ∂densityMeasure n ρ)) :
    ∃ v : unweightedSobolevGraph n,
      (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] (fun x => Real.sqrt (ρ x)) ∧
      (unweightedGradient n v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
        gradient (fun x => Real.sqrt (ρ x)) ∧
      4 * (∫ x, ‖unweightedGradient n v x‖ ^ 2) = ∫ x, ‖r x‖ ^ 2 ∂densityMeasure n ρ := by
  have hs := ordinaryWeakScore_smooth_identification n ρ hρ hρpos r hr hweak
  obtain ⟨v, hv, hgv, he⟩ := ordinaryWeakScore_smooth_sqrt_graph n ρ hρ hρpos hs.2.1
  exact ⟨v, hv, hgv, he.trans hs.2.2⟩

end AffineFKProof
