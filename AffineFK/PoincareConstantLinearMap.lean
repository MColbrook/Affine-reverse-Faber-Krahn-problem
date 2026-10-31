module

public import AffineFK.PoincareConstant

/-! The least Poincare constant under an arbitrary linear map, including zero. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions ENNReal NNReal RealInnerProductSpace

theorem poincareConstant_dirac (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    poincareConstant n (Measure.dirac x) = 0 := by
  apply le_antisymm _ zero_le
  simpa using poincareConstant_le_of_admissible n (Measure.dirac x) 0
    (fun f => by simp [AdmissiblePoincareConstant])

theorem poincareConstant_linearMap (n m : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    poincareConstant m (ν.map A) ≤ ENNReal.ofReal (‖A‖ ^ 2) * poincareConstant n ν := by
  by_cases hA : A = 0
  · subst A
    simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero, zero_mul]
    change poincareConstant m (ν.map (fun _ => (0 : EuclideanSpace ℝ (Fin m)))) ≤ 0
    simp [Measure.map_const, poincareConstant_dirac]
  · have hc0 : ENNReal.ofReal (‖A‖ ^ 2) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hA)))
    change _ ≤ ENNReal.ofReal (‖A‖ ^ 2) *
      (⨅ (P : ℝ≥0) (_ : AdmissiblePoincareConstant n ν P), (P : ℝ≥0∞))
    simp_rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
    refine le_iInf fun P => le_iInf fun hP => ?_
    let c : ℝ≥0 := ⟨‖A‖ ^ 2, sq_nonneg ‖A‖⟩
    have hvalid : AdmissiblePoincareConstant m (ν.map A) (c * P) := by
      intro f
      exact poincareLinearMap n m ν P P.coe_nonneg hP A f
    have h := poincareConstant_le_of_admissible m (ν.map A) (c * P) hvalid
    convert h using 1
    rw [ENNReal.coe_mul]
    congr 1
    exact ENNReal.ofReal_coe_nnreal (p := c)

theorem poincareConstant_OU (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (t : ℝ) (ht : 0 ≤ t) :
    poincareConstant n ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ≤
      ENNReal.ofReal (Real.exp (-2 * t)) * poincareConstant n ν +
        ENNReal.ofReal (1 - Real.exp (-2 * t)) := by
  have hc0 : ENNReal.ofReal (Real.exp (-2 * t)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hd : 0 ≤ 1 - Real.exp (-2 * t) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  change _ ≤ ENNReal.ofReal (Real.exp (-2 * t)) *
    (⨅ (P : ℝ≥0) (_ : AdmissiblePoincareConstant n ν P), (P : ℝ≥0∞)) + _
  simp_rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top, ENNReal.iInf_add]
  refine le_iInf fun P => le_iInf fun hP => ?_
  let Q : ℝ≥0 := ⟨Real.exp (-2 * t) * P + (1 - Real.exp (-2 * t)),
    add_nonneg (mul_nonneg (Real.exp_pos _).le P.coe_nonneg) hd⟩
  have hQreal : (Q : ℝ) = Real.exp (-2 * t) * P + (1 - Real.exp (-2 * t)) :=
    NNReal.coe_mk _ _
  have hvalid : AdmissiblePoincareConstant n
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) Q := by
    intro f
    change _ ≤ (Q : ℝ) * _
    rw [hQreal]
    simpa only [add_sub_assoc] using stdGaussian_OU_poincare n ν P P.coe_nonneg hP t ht f
  have h := poincareConstant_le_of_admissible n _ Q hvalid
  convert h using 1
  rw [← ENNReal.ofReal_coe_nnreal (p := Q), hQreal,
    ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le P.coe_nonneg) hd,
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_coe_nnreal]

end AffineFKProof
