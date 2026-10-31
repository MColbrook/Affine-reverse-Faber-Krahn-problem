module

public import AffineFK.FisherInformationL1Closure
public import AffineFK.OUInitialLebesgueL1
public import AffineFK.GaussianSmoothingRegularity
public import AffineFK.OrnsteinUhlenbeckScales

/-!
# A positive-time uniform Fisher bound passes to the actual initial law

The actual OU densities converge in Lebesgue L1, their actual square roots
converge strongly in L2, and the proved H1 sublevel closure gives the
initial numerical information bound. Initial finite information is not
assumed. This is an endpoint theorem for the actual OU law, not an assumed
general weak lower-semicontinuity principle.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal Classical

theorem ou_ordinaryFisher_initial_le_of_positive_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ volume) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, 0 < t → ordinaryFisherMeasure n (ouInitialLaw n ν t) ≤ ENNReal.ofReal M) :
    ordinaryFisherMeasure n ν ≤ ENNReal.ofReal M := by
  let τ : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
  have hτ (k : ℕ) : 0 < τ k := by dsimp [τ]; positivity
  have hτlimit : Tendsto τ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_inverse_succ, Eventually.of_forall hτ⟩
  have hout (k : ℕ) : ouInitialLaw n ν (τ k) ≪ volume := by
    rw [show ouInitialLaw n ν (τ k) = densityMeasure n (gaussianSmoothingDensity n ν
      (Real.exp (-τ k)) (Real.sqrt (1 - Real.exp (-2 * τ k)))) from
      gaussianSmoothingDensity_law n ν _ _ (ou_smoothing_scale_domain (τ k) (hτ k)).2.1]
    exact withDensity_absolutelyContinuous _ _
  let ρ := canonicalLebesgueDensity n ν
  let ρk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k =>
    canonicalLebesgueDensity n (ouInitialLaw n ν (τ k))
  have hρlaw : densityMeasure n ρ = ν := canonicalLebesgueDensity_reconstruct n ν hac
  letI : IsProbabilityMeasure (densityMeasure n ρ) := by rw [hρlaw]; infer_instance
  letI : ∀ k, IsProbabilityMeasure (densityMeasure n (ρk k)) := fun k => by
    rw [show densityMeasure n (ρk k) = ouInitialLaw n ν (τ k) from
      canonicalLebesgueDensity_reconstruct n _ (hout k)]
    infer_instance
  have hF (k : ℕ) : fisherInformation n (ρk k) ≤ ENNReal.ofReal M := by
    simpa only [ordinaryFisherMeasure, ite_eq_left (hout k)] using hbound (τ k) (hτ k)
  have hL1 : Tendsto (fun k => ∫ x, ‖ρk k x - ρ x‖) atTop (𝓝 0) :=
    (ouInitial_canonical_density_L1_tendsto n ν hac).comp hτlimit
  have h := fisherInformation_le_of_density_L1_limit n ρk ρ
    (canonicalLebesgueDensity_measurable n ν) (canonicalLebesgueDensity_nonneg n ν)
    (fun k => canonicalLebesgueDensity_nonneg n _)
    Measure.integrable_toReal_rnDeriv (fun _ => Measure.integrable_toReal_rnDeriv)
    M hM hF hL1
  simpa only [ordinaryFisherMeasure, ite_eq_left hac] using h

end AffineFKProof
