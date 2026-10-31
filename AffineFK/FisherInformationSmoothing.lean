module

public import AffineFK.FisherInformation
public import AffineFK.SmoothDensitySobolevInformation
public import AffineFK.OUFiniteSobolevInformation

/-!
# Actual numerical relative Fisher information after Gaussian smoothing

The output second moment follows from the true affine product law. Its
square-root H1 membership and exact Sobolev energy follow from the proved
smooth-score bridge. Consequently the OU bounds below concern the actual
extended numerical information, with output finiteness derived.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ENNReal

theorem gaussianSmoothingDensity_second_moment (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (a b : ℝ) (hb : 0 < b) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
  have hW : MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      a • p.1 + b • p.2) 2 (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) :=
    ((hX.comp_fst _).const_smul a).add
      (((IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin n))) 2 (by norm_num)).comp_snd ν).const_smul b)
  have hWmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      a • p.1 + b • p.2) := by fun_prop
  have hXout : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
    rw [← gaussianSmoothingDensity_law n ν a b hb]
    exact (memLp_map_measure_iff aestronglyMeasurable_id hWmeas.aemeasurable).mpr hW
  exact (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mp hXout

theorem gaussianSmoothing_relativeFisher_eq_score_energy (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (a b : ℝ) (hb : 0 < b)
    (hscore : MemLp (gaussianSmoothingScore n ν a b) 2
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2))) :
    relativeFisherInformation n (gaussianSmoothingDensity n ν a b) ≠ ∞ ∧
    relativeFisherInformation n (gaussianSmoothingDensity n ν a b) =
      ENNReal.ofReal (∫ x, ‖gaussianSmoothingScore n ν a b x‖ ^ 2
        ∂((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => a • p.1 + b • p.2))) := by
  obtain ⟨v, hv, _, heq⟩ := gaussian_smoothing_relative_sobolev_information n ν hX a b hb hscore
  have hsecond := gaussianSmoothingDensity_second_moment n ν hX a b hb
  refine ⟨(relativeFisherInformation_ne_top_iff n _).mpr ⟨⟨v, hv⟩, hsecond⟩, ?_⟩
  rw [relativeFisherInformation_eq_graph n _ v hv hsecond, heq]

theorem OU_relativeFisher_two_bounds (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hI : relativeFisherInformation n ρ ≠ ∞)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 (densityMeasure n ρ))
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂densityMeasure n ρ) =
        ∫ x, vectorHessianContraction n T F x ∂densityMeasure n ρ)
    (t : ℝ) (ht : 0 < t) :
    let ρt := gaussianSmoothingDensity n (densityMeasure n ρ) (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t)))
    relativeFisherInformation n ρt ≠ ∞ ∧
    relativeFisherInformation n ρt ≤ ENNReal.ofReal
      (min (Real.exp (-2 * t) * (relativeFisherInformation n ρ).toReal)
        ((2 * Real.exp (-6 * t) / (1 - Real.exp (-2 * t)) ^ 2) *
          (∫ x, ‖T x‖ ^ 2 ∂densityMeasure n ρ))) := by
  dsimp only
  obtain ⟨⟨v, hv⟩, hsecond⟩ := (relativeFisherInformation_ne_top_iff n ρ).mp hI
  have hout := finiteSobolev_OU_two_score_bounds n ρ hρ0 v hv hsecond T hT hidentity t ht
  have hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 (densityMeasure n ρ) :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr hsecond
  have hb : 0 < Real.sqrt (1 - Real.exp (-2 * t)) :=
    Real.sqrt_pos.mpr (by linarith [Real.exp_lt_one_iff.mpr (show -2 * t < 0 by linarith)])
  have heq := gaussianSmoothing_relativeFisher_eq_score_energy n (densityMeasure n ρ) hX
    (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) hb hout.2.1
  refine ⟨heq.1, ?_⟩
  rw [heq.2]
  apply ENNReal.ofReal_le_ofReal
  simpa only [relativeFisherInformation_eq_graph n ρ v hv hsecond,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg _))] using hout.2.2

end AffineFKProof
