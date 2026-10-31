module

public import AffineFK.FisherInformationMeasure
public import AffineFK.OrdinaryFisherLinearMapInformation

/-!
# Ordinary Fisher information of an invertible linear image law

The density calculation uses the absolute inverse determinant and direct
transport of actual square-root-H1 functions. In dimension zero every
measure is absolutely continuous with respect to its Dirac volume and
has zero ordinary information. This also resolves the zero operator norm
in the extended multiplication convention.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem absolutelyContinuous_volume_zero_dimension
    (ν : Measure (EuclideanSpace ℝ (Fin 0))) : ν ≪ volume := by
  intro s hs
  have hs0 : (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))) s = 0 := by
    simpa only [volume_euclideanSpace_eq_dirac] using hs
  have hempty : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx0 : x = 0 := by ext i; exact Fin.elim0 i
    have hmem : (0 : EuclideanSpace ℝ (Fin 0)) ∈ s := hx0 ▸ hx
    have h1 := Measure.dirac_apply_of_mem hmem
    exact zero_ne_one (hs0.symm.trans h1)
  rw [hempty, measure_empty]

theorem ordinaryFisherMeasure_zero_dimension
    (ν : Measure (EuclideanSpace ℝ (Fin 0))) : ordinaryFisherMeasure 0 ν = 0 := by
  rw [ordinaryFisherMeasure, ite_eq_left (absolutelyContinuous_volume_zero_dimension ν),
    fisherInformation_zero_dimension]

theorem ordinaryFisherMeasure_linearMap (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ordinaryFisherMeasure n (ν.map A) ≤
      ENNReal.ofReal (‖A.symm.toContinuousLinearMap‖ ^ 2) * ordinaryFisherMeasure n ν := by
  classical
  by_cases hn : n = 0
  · subst n
    rw [ordinaryFisherMeasure_zero_dimension, ordinaryFisherMeasure_zero_dimension, mul_zero]
  · let : NeZero n := ⟨hn⟩
    by_cases hac : ν ≪ volume
    · let ρ := canonicalLebesgueDensity n ν
      have hρ : Measurable ρ := canonicalLebesgueDensity_measurable n ν
      have hν : densityMeasure n ρ = ν := canonicalLebesgueDensity_reconstruct n ν hac
      have h := fisherInformation_linearMap_with_law n A ρ hρ
      have hκ : Measurable (ordinaryFisherLinearDensity n A ρ) :=
        measurable_const.mul (hρ.comp A.symm.continuous.measurable)
      have hκ0 : ∀ᵐ x ∂volume, 0 ≤ ordinaryFisherLinearDensity n A ρ x :=
        Filter.Eventually.of_forall fun x => mul_nonneg
          (ordinaryFisherLinearJacobian_pos n A).le (canonicalLebesgueDensity_nonneg n ν _)
      calc
        _ = ordinaryFisherMeasure n (densityMeasure n (ordinaryFisherLinearDensity n A ρ)) := by
          rw [← hν, h.1]
        _ = fisherInformation n (ordinaryFisherLinearDensity n A ρ) :=
          ordinaryFisherMeasure_density n _ hκ hκ0
        _ ≤ ENNReal.ofReal (‖A.symm.toContinuousLinearMap‖ ^ 2) * fisherInformation n ρ := h.2
        _ = ENNReal.ofReal (‖A.symm.toContinuousLinearMap‖ ^ 2) * ordinaryFisherMeasure n ν := by
          simp only [ordinaryFisherMeasure, ite_eq_left hac, ρ]
    · have hc : ENNReal.ofReal (‖A.symm.toContinuousLinearMap‖ ^ 2) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos A.symm.norm_pos))
      have htop : ordinaryFisherMeasure n ν = ∞ := by
        simp only [ordinaryFisherMeasure, ite_eq_right hac]
      rw [htop, ENNReal.mul_top hc]
      exact le_top

end AffineFKProof
