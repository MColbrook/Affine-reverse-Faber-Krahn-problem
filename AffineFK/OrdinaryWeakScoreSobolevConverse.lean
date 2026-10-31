module

public import AffineFK.OrdinaryWeakScoreSobolev

/-!
# The full nonnegative-AE and compact-vector ordinary-score converse

Probability mass supplies actual density L1, so it is not a separate
premise. Passing to the measurable positive part handles nonnegativity
only almost everywhere without changing the density law or square root
almost everywhere. Actual compact vector tests imply the scalar equations
with their genuine integrability guards.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem ordinaryWeakScore_probability_density_integrable (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)] :
    Integrable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hmass : (∫⁻ x, ENNReal.ofReal (ρ x) ∂volume) = 1 := by
    have h := measure_univ (μ := densityMeasure n ρ)
    simpa only [densityMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using h
  exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Filter.Eventually.of_forall hρ0)).mp (by rw [hmass]; exact ENNReal.one_ne_top)

theorem ordinaryWeakScore_sqrt_sobolev_ae (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hs : MemLp s 2 (densityMeasure n ρ))
    (hweak : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, s x i * φ x ∂densityMeasure n ρ) =
        -(∫ x, partialTest n i φ x ∂densityMeasure n ρ)) :
    ∃ v : unweightedSobolevGraph n,
      (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        (fun x => Real.sqrt (ρ x)) ∧
      4 * (∫ x, ‖unweightedGradient n v x‖ ^ 2) ≤
        ∫ x, ‖s x‖ ^ 2 ∂densityMeasure n ρ := by
  let ρplus : EuclideanSpace ℝ (Fin n) → ℝ := fun x => max (ρ x) 0
  have hmplus : Measurable ρplus := hm.max measurable_const
  have hplus0 (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ ρplus x := le_max_right _ _
  have heq : densityMeasure n ρplus = densityMeasure n ρ := by
    unfold densityMeasure
    apply withDensity_congr_ae
    filter_upwards [hρ0] with x hx
    simp only [ρplus, max_eq_left hx]
  let : IsProbabilityMeasure (densityMeasure n ρplus) := by rw [heq]; infer_instance
  have hsplus : MemLp s 2 (densityMeasure n ρplus) := by rw [heq]; exact hs
  have hweakplus : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, s x i * φ x ∂densityMeasure n ρplus) =
        -(∫ x, partialTest n i φ x ∂densityMeasure n ρplus) := by
    intro i φ
    simpa only [heq] using hweak i φ
  obtain ⟨v, hv, hbound⟩ := ordinaryWeakScore_sqrt_sobolev n ρplus hmplus hplus0
    (ordinaryWeakScore_probability_density_integrable n ρplus hmplus hplus0) s hsplus hweakplus
  refine ⟨v, ?_, ?_⟩
  · apply hv.trans
    filter_upwards [hρ0] with x hx
    simp only [ρplus, max_eq_left hx]
  · simpa only [heq] using hbound

theorem ordinaryWeakScore_vector_sqrt_sobolev (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hs : MemLp s 2 (densityMeasure n ρ))
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪s x, F x⟫ ∂densityMeasure n ρ) =
        -(∫ x, vectorDivergence n F x ∂densityMeasure n ρ)) :
    ∃ v : unweightedSobolevGraph n,
      (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        (fun x => Real.sqrt (ρ x)) ∧
      4 * (∫ x, ‖unweightedGradient n v x‖ ^ 2) ≤
        ∫ x, ‖s x‖ ^ 2 ∂densityMeasure n ρ := by
  let ν := densityMeasure n ρ
  have hguarded : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      Integrable (fun x => ⟪s x, F x⟫) ν ∧ Integrable (vectorDivergence n F) ν ∧
      (∫ x, ⟪s x, F x⟫ ∂ν) = -(∫ x, vectorDivergence n F x ∂ν) := by
    intro F
    have hF : MemLp F 2 ν :=
      (Lp.memLp (testFunctionToL2 ν F)).ae_eq (testFunctionToL2_coe ν F)
    have hpair : Integrable (fun x => ⟪s x, F x⟫) ν :=
      memLp_one_iff_integrable.mp ((innerSL ℝ).memLp_of_bilin 1 hs hF)
    have hdiv : Integrable (vectorDivergence n F) ν := by
      unfold vectorDivergence
      exact integrable_finsetSum Finset.univ fun i _ =>
        (testFunction_memLp_two n ν (partialTest n i (vectorComponentTest n i F))).integrable (by norm_num)
    exact ⟨hpair, hdiv, hweak F⟩
  have hc := ordinaryFisher_weak_vector_components n ν s hguarded
  exact ordinaryWeakScore_sqrt_sobolev_ae n ρ hm hρ0 s hs (fun i φ => (hc i φ).2.2)

end AffineFKProof
