module

public import AffineFK.GaussianHessianL2Calculus
public import AffineFK.GaussianSecondDensityRatio
public import AffineFK.GaussianSmoothedOrdinaryScoreL4
public import AffineFK.GaussianSmoothedScoreHessianSymmetry
public import AffineFK.MatrixHilbertSchmidt

/-!
# L2 logarithmic Hessian of an arbitrary Gaussian-smoothed law

The actual second-density ratio is L2 by its derived conditional
representation. The actual logarithmic score is L4 by the independently
constructed Gaussian score field. Their proved quotient identity gives
the actual Hessian entries and rows in L2, and an integrable explicit
Hilbert--Schmidt squared energy. No initial density or moment is needed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem gaussianSmoothing_logHessian_entry_memLp (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) (i j : Fin n) :
    MemLp (fun x => densityLogHessian n (gaussianSmoothingDensity n ν a b) x i j) 2
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) :=
  densityLogHessian_entry_memLp_of_secondRatio_and_score n _
    (gaussianSmoothingDensity_smooth n ν a b) (gaussianSmoothingDensity_pos n ν a b hb)
    _ i j (gaussianSmoothing_secondDensityRatio_memLp n ν i j a b hb).1
    (gaussianSmoothing_ordinaryScore_density_memLp_four n ν a b hb).1

theorem gaussianSmoothing_logHessian_row_memLp (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) (i : Fin n) :
    MemLp (gradient (fun y => gradient (fun z => Real.log (gaussianSmoothingDensity n ν a b z)) y i)) 2
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
  apply memLp_piLp_iff.mpr
  intro j
  exact gaussianSmoothing_logHessian_entry_memLp n ν a b hb i j

theorem gaussianSmoothing_logHessian_squared_energy_integrable (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    Integrable (fun x => matrixHilbertSchmidtSq (densityLogHessian n (gaussianSmoothingDensity n ν a b) x))
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
  have hentry (i j : Fin n) : Integrable (fun x =>
      (densityLogHessian n (gaussianSmoothingDensity n ν a b) x i j) ^ 2)
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (gaussianSmoothing_logHessian_entry_memLp n ν a b hb i j).integrable_norm_pow (by norm_num)
  exact integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hentry i j

theorem gaussianSmoothing_logHessian_L2 (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    (∀ i : Fin n,
      MemLp (gradient (fun y => gradient (fun z => Real.log (gaussianSmoothingDensity n ν a b z)) y i)) 2
        ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2))) ∧
    Integrable (fun x => matrixHilbertSchmidtSq (densityLogHessian n (gaussianSmoothingDensity n ν a b) x))
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
    (∀ x i j, densityLogHessian n (gaussianSmoothingDensity n ν a b) x i j =
      secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j x -
        gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x i *
        gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x j) ∧
    (∀ x i j, densityLogHessian n (gaussianSmoothingDensity n ν a b) x i j =
      densityLogHessian n (gaussianSmoothingDensity n ν a b) x j i) := by
  rw [gaussianSmoothingDensity_law n ν a b hb]
  refine ⟨gaussianSmoothing_logHessian_row_memLp n ν a b hb,
    gaussianSmoothing_logHessian_squared_energy_integrable n ν a b hb, ?_, ?_⟩
  · exact fun x i j => densityLogHessian_eq_secondDensityRatio_sub_score_product n _
      (gaussianSmoothingDensity_smooth n ν a b) (gaussianSmoothingDensity_pos n ν a b hb) x i j
  · exact fun x i j => gaussianSmoothing_ordinaryScore_hessian_component_symmetric n ν a b hb x i j

end AffineFKProof
