module

public import AffineFK.PoincareConstant

/-!
# Finite upper bounds for the actual least Poincare constant

Every finite nonnegative upper bound for the genuine infimum is itself
admissible. Approximate admissible constants below P+1/(k+1) give the
inequality for each fixed compact test by a real limit. No minimizing
constant or attainment property is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped Distributions ENNReal NNReal RealInnerProductSpace Topology ContDiff

theorem exists_admissiblePoincareConstant_lt_of_lt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (R : ℝ≥0)
    (h : poincareConstant n ν < (R : ℝ≥0∞)) :
    ∃ Q : ℝ≥0, AdmissiblePoincareConstant n ν Q ∧ Q < R := by
  change (⨅ (Q : ℝ≥0) (_ : AdmissiblePoincareConstant n ν Q), (Q : ℝ≥0∞)) < _ at h
  obtain ⟨Q, hQ⟩ := iInf_lt_iff.mp h
  obtain ⟨hAd, hQR⟩ := iInf_lt_iff.mp hQ
  exact ⟨Q, hAd, by exact_mod_cast hQR⟩

theorem admissiblePoincareConstant_of_poincareConstant_le (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (P : ℝ≥0)
    (hP : poincareConstant n ν ≤ (P : ℝ≥0∞)) :
    AdmissiblePoincareConstant n ν P := by
  intro f
  let E : ℝ := ∫ x, ‖gradient f x‖ ^ 2 ∂ν
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hbound (k : ℕ) : (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤
      ((P : ℝ) + ((k : ℝ) + 1)⁻¹) * E := by
    let ε : ℝ≥0 := ⟨((k : ℝ) + 1)⁻¹, by positivity⟩
    have hε : 0 < ε := by
      change (0 : ℝ) < ((k : ℝ) + 1)⁻¹
      positivity
    have hlt : poincareConstant n ν < ((P + ε : ℝ≥0) : ℝ≥0∞) := by
      apply lt_of_le_of_lt hP
      exact_mod_cast lt_add_of_pos_right P hε
    obtain ⟨Q, hAd, hQ⟩ := exists_admissiblePoincareConstant_lt_of_lt n ν (P + ε) hlt
    have hQ' : (Q : ℝ) ≤ (P : ℝ) + ((k : ℝ) + 1)⁻¹ := by
      change (Q : ℝ) ≤ ((P + ε : ℝ≥0) : ℝ)
      exact_mod_cast hQ.le
    exact (hAd f).trans (mul_le_mul_of_nonneg_right hQ' hE)
  have hlimit : Tendsto (fun k : ℕ => ((P : ℝ) + ((k : ℝ) + 1)⁻¹) * E)
      atTop (𝓝 ((P : ℝ) * E)) := by
    simpa only [add_zero] using (tendsto_const_nhds.add tendsto_inverse_succ).mul_const E
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlimit hbound

theorem poincareConstant_le_iff_admissible (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (P : ℝ≥0) :
    poincareConstant n ν ≤ (P : ℝ≥0∞) ↔ AdmissiblePoincareConstant n ν P :=
  ⟨admissiblePoincareConstant_of_poincareConstant_le n ν P,
    poincareConstant_le_of_admissible n ν P⟩

theorem poincareConstant_le_smooth_L2 (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ≥0) (hP : poincareConstant n ν ≤ (P : ℝ≥0∞))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfL2 : MemLp f 2 ν) (hgL2 : MemLp (gradient f) 2 ν) :
    (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤
      (P : ℝ) * (∫ x, ‖gradient f x‖ ^ 2 ∂ν) :=
  admissiblePoincareConstant_smooth_L2 n ν P
    (admissiblePoincareConstant_of_poincareConstant_le n ν P hP) f hf hfL2 hgL2

end AffineFKProof
