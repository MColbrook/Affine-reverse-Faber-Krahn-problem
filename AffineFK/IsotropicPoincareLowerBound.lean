module

public import AffineFK.PoincareConstantAttainment
public import AffineFK.PoincareSmoothExtension
public import AffineFK.IsotropicCoordinates

/-!
# Isotropy forces a finite Poincare upper bound to be at least one

The original manuscript has positive dimension. A genuine coordinate is
an admissible smooth L2 function with constant unit gradient. Its variance
is one by the literal input moments. The compact-test least constant is
extended by the already proved cutoff argument, not by assuming that
coordinate functions are compactly supported.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal NNReal

theorem isotropic_poincare_bound_ge_one (n : ℕ) (hn : 0 < n)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (P : ℝ≥0) (hP : poincareConstant n ν ≤ (P : ℝ≥0∞)) : 1 ≤ (P : ℝ) := by
  let i : Fin n := ⟨0, hn⟩
  have hf : MemLp (coordinateFunctional n i) 2 ν := by
    have he : (coordinateFunctional n i : EuclideanSpace ℝ (Fin n) → ℝ) = fun x => x i :=
      funext (coordinateFunctional_apply n i)
    rw [he]
    exact isotropic_coordinate_memLp n ν hcov i
  have hg : MemLp (gradient (coordinateFunctional n i)) 2 ν := by
    have he : gradient (coordinateFunctional n i) =
        fun _ : EuclideanSpace ℝ (Fin n) => EuclideanSpace.basisFun (Fin n) ℝ i :=
      funext (coordinateFunctional_gradient n i)
    rw [he]
    exact memLp_const _
  have h := poincareSmoothExtension n ν (P : ℝ)
    (admissiblePoincareConstant_of_poincareConstant_le n ν P hP)
    (coordinateFunctional n i) (coordinateFunctional n i).contDiff hf hg
  simp_rw [coordinateFunctional_apply, coordinateFunctional_gradient] at h
  rw [hmean i] at h
  simp only [sub_zero, (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one,
    one_pow, integral_const, probReal_univ, one_smul, mul_one] at h
  have hi : (∫ x : EuclideanSpace ℝ (Fin n), (x i) ^ 2 ∂ν) = 1 := by
    simpa only [pow_two, ite_true] using hcov i i
  rwa [hi] at h

end AffineFKProof
