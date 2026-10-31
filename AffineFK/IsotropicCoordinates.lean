module

public import AffineFK.FirstSteinKernel

/-!
# Unit second moments give the required L2 coordinates

The isotropic coordinate moment, expressed as a genuine Bochner integral,
already forces integrability of its square. Thus the Poisson construction
does not need a separate extra moment assumption.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped RealInnerProductSpace

theorem coordinate_memLp_of_unit_second_moment
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (i : Fin n) (hvar : (∫ x, (x i) ^ 2 ∂ν) = 1) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) := by
    have heq : (coordinateFunctional n i : EuclideanSpace ℝ (Fin n) → ℝ) = (fun x => x i) :=
      funext (coordinateFunctional_apply n i)
    rw [← heq]
    exact (coordinateFunctional n i).continuous
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  simpa only [Real.norm_eq_abs, sq_abs] using integrable_of_integral_eq_one hvar

theorem isotropic_coordinate_memLp
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0)
    (i : Fin n) : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν := by
  apply coordinate_memLp_of_unit_second_moment n ν i
  simpa [pow_two] using hcov i i

theorem isotropic_coordinate_norm_sq
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0)
    (i : Fin n) :
    ‖(isotropic_coordinate_memLp n ν hcov i).toLp
      (fun x : EuclideanSpace ℝ (Fin n) => x i)‖ ^ 2 = 1 := by
  rw [coordinateL2_norm_sq]
  simpa [pow_two] using hcov i i

end AffineFKProof
