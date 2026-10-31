module

public import AffineFK.OUFisherEndpointClosure
public import AffineFK.OUFisherRelativeDissipation

/-!
# The actual relative-Fisher initial bound for isotropic laws

The exact ordinary/relative numerical information identity transfers the
proved OU endpoint closure. Neither finite initial information nor a
lower-semicontinuity assertion is assumed. Literal raw isotropic moments
give all required L2 coordinates and the second norm moment.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem isotropic_norm_second_moment (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then (1 : ℝ) else 0) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) ν ∧
      (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 ∂ν) = n := by
  have hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν :=
    memLp_piLp_iff.mpr fun i => isotropic_coordinate_memLp n ν hcov i
  refine ⟨(memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mp hX, ?_⟩
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  have hsqi (i : Fin n) : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2) ν :=
    (isotropic_coordinate_memLp n ν hcov i).integrable_sq
  rw [integral_finsetSum Finset.univ fun i _ => hsqi i]
  have hi (i : Fin n) : (∫ x : EuclideanSpace ℝ (Fin n), (x i) ^ 2 ∂ν) = 1 := by
    simpa only [pow_two, ite_true] using hcov i i
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem ou_relativeFisher_initial_le_of_positive_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ volume)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t : ℝ, 0 < t → relativeFisherMeasure n (ouInitialLaw n ν t) ≤ ENNReal.ofReal M) :
    relativeFisherMeasure n ν ≤ ENNReal.ofReal M := by
  have hMn : 0 ≤ M + n := by positivity
  have hJbound (t : ℝ) (ht : 0 < t) :
      ordinaryFisherMeasure n (ouInitialLaw n ν t) ≤ ENNReal.ofReal (M + n) := by
    have hb := (ou_smoothing_scale_domain t ht).2.1
    have hlaw : ouInitialLaw n ν t = densityMeasure n (gaussianSmoothingDensity n ν
        (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))) :=
      gaussianSmoothingDensity_law n ν _ _ hb
    have hJ := gaussianSmoothing_ordinaryFisherMeasure_eq_energy n ν
      (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) hb
    dsimp only at hJ
    rw [← hlaw] at hJ
    have hI := ou_isotropic_relativeFisher_toReal n ν hmean hcov t ht
    have hIB : (relativeFisherMeasure n (ouInitialLaw n ν t)).toReal ≤ M := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound t ht)
      simpa only [ENNReal.toReal_ofReal hM] using h
    have hJB : (ordinaryFisherMeasure n (ouInitialLaw n ν t)).toReal ≤ M + n := by
      linarith [hJ.2, hI.2]
    calc
      _ = ENNReal.ofReal (ordinaryFisherMeasure n (ouInitialLaw n ν t)).toReal :=
        (ENNReal.ofReal_toReal hJ.1).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hJB
  have hJ := ou_ordinaryFisher_initial_le_of_positive_bound n ν hac (M + n) hMn hJbound
  have hJfin : ordinaryFisherMeasure n ν ≠ ∞ := by
    intro ht
    rw [ht] at hJ
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hJ)
  have hmom := isotropic_norm_second_moment n ν hcov
  have hI := fisherMeasure_unit_second_moment_identity n ν hJfin hmom.1 hmom.2
  have hJB : (ordinaryFisherMeasure n ν).toReal ≤ M + n := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hJ
    simpa only [ENNReal.toReal_ofReal hMn] using h
  have hIB : (relativeFisherMeasure n ν).toReal ≤ M := by linarith [hI.2]
  calc
    _ = ENNReal.ofReal (relativeFisherMeasure n ν).toReal := (ENNReal.ofReal_toReal hI.1).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hIB

end AffineFKProof
