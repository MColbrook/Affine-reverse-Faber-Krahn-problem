module

public import AffineFK.FisherInformationMeasure
public import AffineFK.FisherInformationSmoothing
public import AffineFK.OUEntropyContraction

/-!
# OU information bounds for the actual probability law

Finite relative information supplies the canonical square-root Sobolev
domain and second moment. The output information is identified with the
actual positive-time score energy by the proved Sobolev bridge. The
first-order bound includes time zero; the second-order bound uses positive
time, where its denominator and smooth output density are valid.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ENNReal

theorem fisherMeasure_gaussian_smoothing_score_energy (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (a b : ℝ) (hb : 0 < b)
    (hscore : MemLp (gaussianSmoothingScore n ν a b) 2
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2))) :
    let μ := (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)
    relativeFisherMeasure n μ ≠ ∞ ∧
    relativeFisherMeasure n μ = ENNReal.ofReal (∫ x, ‖gaussianSmoothingScore n ν a b x‖ ^ 2 ∂μ) := by
  dsimp only
  have hd : relativeFisherMeasure n
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2)) =
      relativeFisherInformation n (gaussianSmoothingDensity n ν a b) := by
    rw [gaussianSmoothingDensity_law n ν a b hb]
    exact relativeFisherMeasure_density n _ (gaussianSmoothingDensity_smooth n ν a b).continuous.measurable
      (Filter.Eventually.of_forall fun x => (gaussianSmoothingDensity_pos n ν a b hb x).le)
  have heq := gaussianSmoothing_relativeFisher_eq_score_energy n ν hX a b hb hscore
  exact ⟨hd.trans_ne heq.1, hd.trans heq.2⟩

theorem ouInitialLaw_zero (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] : ouInitialLaw n ν 0 = ν := by
  simp [ouInitialLaw]

theorem fisherMeasure_OU_contraction (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hI : relativeFisherMeasure n ν ≠ ∞) (t : ℝ) (ht : 0 ≤ t) :
    relativeFisherMeasure n (ouInitialLaw n ν t) ≠ ∞ ∧
    relativeFisherMeasure n (ouInitialLaw n ν t) ≤
      ENNReal.ofReal (Real.exp (-2 * t) * (relativeFisherMeasure n ν).toReal) := by
  classical
  by_cases ht0 : t = 0
  · subst t
    simpa only [ouInitialLaw_zero, mul_zero, Real.exp_zero, one_mul] using
      And.intro hI (le_of_eq (ENNReal.ofReal_toReal hI).symm)
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hac : ν ≪ volume := by
    by_contra h
    exact hI (by simp only [relativeFisherMeasure, ite_eq_right h])
  let ρ := canonicalLebesgueDensity n ν
  have hlaw : densityMeasure n ρ = ν := canonicalLebesgueDensity_reconstruct n ν hac
  let : IsProbabilityMeasure (densityMeasure n ρ) := by rw [hlaw]; infer_instance
  have hIeq : relativeFisherMeasure n ν = relativeFisherInformation n ρ := by
    simp only [relativeFisherMeasure, ite_eq_left hac, ρ]
  obtain ⟨⟨v, hv⟩, hsecond⟩ := (relativeFisherInformation_ne_top_iff n ρ).mp (hIeq ▸ hI)
  have hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x :=
    Filter.Eventually.of_forall (canonicalLebesgueDensity_nonneg n ν)
  have hout := finiteSobolev_OU_score_bound n ρ hρ0 v hv hsecond t htpos
  rw [hlaw] at hout hsecond
  have hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr hsecond
  have hb : 0 < Real.sqrt (1 - Real.exp (-2 * t)) :=
    Real.sqrt_pos.mpr (by linarith [Real.exp_lt_one_iff.mpr (show -2 * t < 0 by linarith)])
  have heq := fisherMeasure_gaussian_smoothing_score_energy n ν hX (Real.exp (-t))
    (Real.sqrt (1 - Real.exp (-2 * t))) hb hout.2.1
  change relativeFisherMeasure n (ouInitialLaw n ν t) ≠ ∞ ∧
    relativeFisherMeasure n (ouInitialLaw n ν t) = _ at heq
  refine ⟨heq.1, ?_⟩
  rw [heq.2]
  apply ENNReal.ofReal_le_ofReal
  simpa only [hIeq, relativeFisherInformation_eq_graph n ρ v hv (hlaw.symm ▸ hsecond),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg _))] using hout.2.2

theorem fisherMeasure_OU_two_bounds (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hI : relativeFisherMeasure n ν ≠ ∞)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν)
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) =
        ∫ x, vectorHessianContraction n T F x ∂ν)
    (t : ℝ) (ht : 0 < t) :
    relativeFisherMeasure n (ouInitialLaw n ν t) ≠ ∞ ∧
    relativeFisherMeasure n (ouInitialLaw n ν t) ≤ ENNReal.ofReal
      (min (Real.exp (-2 * t) * (relativeFisherMeasure n ν).toReal)
        ((2 * Real.exp (-6 * t) / (1 - Real.exp (-2 * t)) ^ 2) * (∫ x, ‖T x‖ ^ 2 ∂ν))) := by
  classical
  have hac : ν ≪ volume := by
    by_contra h
    exact hI (by simp only [relativeFisherMeasure, ite_eq_right h])
  let ρ := canonicalLebesgueDensity n ν
  have hlaw : densityMeasure n ρ = ν := canonicalLebesgueDensity_reconstruct n ν hac
  let : IsProbabilityMeasure (densityMeasure n ρ) := by rw [hlaw]; infer_instance
  have hIeq : relativeFisherMeasure n ν = relativeFisherInformation n ρ := by
    simp only [relativeFisherMeasure, ite_eq_left hac, ρ]
  have hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x :=
    Filter.Eventually.of_forall (canonicalLebesgueDensity_nonneg n ν)
  have hT' : MemLp T 2 (densityMeasure n ρ) := by rw [hlaw]; exact hT
  have hidentity' : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂densityMeasure n ρ) =
        ∫ x, vectorHessianContraction n T F x ∂densityMeasure n ρ := by
    simpa only [hlaw] using hidentity
  have hout := OU_relativeFisher_two_bounds n ρ hρ0 (hIeq ▸ hI) T hT' hidentity' t ht
  have hb : 0 < Real.sqrt (1 - Real.exp (-2 * t)) :=
    Real.sqrt_pos.mpr (by linarith [Real.exp_lt_one_iff.mpr (show -2 * t < 0 by linarith)])
  have hμ : relativeFisherMeasure n (ouInitialLaw n ν t) =
      relativeFisherInformation n (gaussianSmoothingDensity n (densityMeasure n ρ)
        (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))) := by
    change relativeFisherMeasure n
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) = _
    rw [gaussianSmoothingDensity_law n ν _ _ hb, hlaw]
    exact relativeFisherMeasure_density n _ (gaussianSmoothingDensity_smooth n ν _ _).continuous.measurable
      (Filter.Eventually.of_forall fun x => (gaussianSmoothingDensity_pos n ν _ _ hb x).le)
  rw [hμ]
  simpa only [← hIeq, hlaw] using hout

end AffineFKProof
