module

public import AffineFK.OrdinaryFisherConvolutionDensity
public import AffineFK.OrdinaryFisherLinearMapDensity

/-!
# Absolute continuity of the actual normalized-copy law

The genuine convolution density (finite almost everywhere by mass one)
and the actual invertible-linear Jacobian density identify the sum law.
No finite Fisher information, smoothness or assumed output density is
required. The two density formulas are reused from the independently
checked ordinary-Fisher convolution and linear-map developments.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory

theorem normalized_copies_absolutelyContinuous (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Measurable f)
    [IsProbabilityMeasure (densityMeasure n f)] (a : ℝ) (ha : a ≠ 0) :
    ((densityMeasure n f).prod (densityMeasure n f)).map
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • p.1 + a • p.2) ≪ volume := by
  let E := EuclideanSpace ℝ (Fin n)
  let ν := densityMeasure n f
  let κ := ordinaryFisherConvolutionDensity n ν f
  have hκ : Measurable κ := (ordinaryFisherConvolutionDensityENNReal_measurable n ν f hf).ennreal_toReal
  have hsum : (ν.prod ν).map (fun p => p.1 + p.2) = densityMeasure n κ :=
    ordinaryFisherConvolutionDensity_law n ν f hf
  let A : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E a ha).toContinuousLinearEquiv
  have hA (x : E) : A x = a • x := rfl
  have hlinear := ordinaryFisherLinearDensity_law n A κ hκ
  have hlaw : (ν.prod ν).map (fun p => a • p.1 + a • p.2) =
      densityMeasure n (ordinaryFisherLinearDensity n A κ) := by
    calc
      _ = ((ν.prod ν).map (fun p => p.1 + p.2)).map A := by
        rw [Measure.map_map A.continuous.measurable (by fun_prop)]
        congr 1
        funext p
        change a • p.1 + a • p.2 = A (p.1 + p.2)
        rw [hA, smul_add]
      _ = _ := by rw [hsum, hlinear]
  rw [hlaw]
  exact withDensity_absolutelyContinuous _ _

end AffineFKProof
