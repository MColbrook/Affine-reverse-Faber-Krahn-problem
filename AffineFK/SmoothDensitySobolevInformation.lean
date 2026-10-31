module

public import AffineFK.OrdinaryWeakScoreSobolevSmooth
public import AffineFK.GaussianSmoothedScore
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# The exact Sobolev meaning of smooth relative score energy

Square-integrable relative score and a second moment give the ordinary
score in L2. The proved ordinary-score bridge supplies the actual square
root in H1. Pointwise calculus then identifies the manuscript's Sobolev
relative information with the actual relative logarithmic score energy.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ContDiff RealInnerProductSpace

theorem smooth_density_relative_sobolev_information (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (hscore : MemLp (gaussianRelativeScore n ρ) 2 (densityMeasure n ρ))
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      2 (densityMeasure n ρ)) :
    ∃ v : unweightedSobolevGraph n,
      (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] (fun x => Real.sqrt (ρ x)) ∧
      (unweightedGradient n v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
        gradient (fun x => Real.sqrt (ρ x)) ∧
      Integrable (fun x => ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2) =
        ∫ x, ‖gaussianRelativeScore n ρ x‖ ^ 2 ∂densityMeasure n ρ := by
  have hord : MemLp (gradient (fun x => Real.log (ρ x))) 2 (densityMeasure n ρ) := by
    apply (hscore.sub hX).ae_eq
    exact Filter.Eventually.of_forall fun x => by
      change gradient (fun y => Real.log (ρ y)) x + x - x = gradient (fun y => Real.log (ρ y)) x
      exact add_sub_cancel_right _ _
  obtain ⟨v, hv, hgv, _⟩ := ordinaryWeakScore_smooth_sqrt_graph n ρ hρ hρpos hord
  have hs2 := (memLp_two_iff_integrable_sq_norm hscore.aestronglyMeasurable).mp hscore
  have hweighted : Integrable (fun x => ρ x * ‖gaussianRelativeScore n ρ x‖ ^ 2) volume := by
    have h := (integrable_withDensity_iff_integrable_smul'
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      hρ.continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hs2
    simpa only [ENNReal.toReal_ofReal (hρpos _).le, smul_eq_mul] using h
  have hpoint : (fun x => ρ x * ‖gaussianRelativeScore n ρ x‖ ^ 2) =ᵐ[volume]
      fun x => ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2 := by
    filter_upwards [hgv] with x hx
    rw [hx, smooth_density_relative_energy_pointwise n ρ hρ hρpos x]
  refine ⟨v, hv, hgv, hweighted.congr hpoint, ?_⟩
  rw [← integral_congr_ae hpoint,
    density_integral_eq n ρ hρ.continuous (fun x => (hρpos x).le)]

theorem gaussian_smoothing_relative_sobolev_information (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (a b : ℝ) (hb : 0 < b)
    (hscore : MemLp (gaussianSmoothingScore n ν a b) 2
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2))) :
    let ρ := gaussianSmoothingDensity n ν a b
    ∃ v : unweightedSobolevGraph n,
      (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] (fun x => Real.sqrt (ρ x)) ∧
      Integrable (fun x => ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ x, ‖(2 : ℝ) • unweightedGradient n v x + Real.sqrt (ρ x) • x‖ ^ 2) =
        ∫ x, ‖gaussianSmoothingScore n ν a b x‖ ^ 2
          ∂((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) := by
  dsimp only
  have hlaw := gaussianSmoothingDensity_law n ν a b hb
  let : IsProbabilityMeasure (densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
    rw [← hlaw]
    infer_instance
  have hW : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      a • p.1 + b • p.2) 2 (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) :=
    ((hX.comp_fst _).const_smul a).add
      (((IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin n))) 2 (by norm_num)).comp_snd ν).const_smul b)
  have hWmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      a • p.1 + b • p.2) := by fun_prop
  have hXout : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
    rw [← hlaw]
    exact (memLp_map_measure_iff aestronglyMeasurable_id hWmeas.aemeasurable).mpr hW
  rw [hlaw, gaussianSmoothingScore_eq_density_score n ν a b hb] at hscore
  obtain ⟨v, hv, _, hL1, heq⟩ := smooth_density_relative_sobolev_information n _
    (gaussianSmoothingDensity_smooth n ν a b) (gaussianSmoothingDensity_pos n ν a b hb) hscore hXout
  refine ⟨v, hv, hL1, ?_⟩
  simpa only [hlaw, gaussianSmoothingScore_eq_density_score n ν a b hb] using heq

end AffineFKProof
