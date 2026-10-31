module

public import AffineFK.TestReflection
public import AffineFK.OddTensorSymmetrization

/-!
# An odd centred third-order tensor with the component Stein identity

Antisymmetrising the actual constructed tensor preserves its component
identity under an even law, by reflection of the smooth tests. Its energy
does not increase. This proves existence of an odd centred coefficient field
directly; parity of the original Poisson solution representatives remains a
separate statement of the manuscript.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem tensor_contraction_oddPart
    (n : ℕ) (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    tensorPartialContraction n (oddPart T) i φ x = (1 / 2 : ℝ) *
      (tensorPartialContraction n T i φ x -
        tensorPartialContraction n (fun y => T (-y)) i φ x) := by
  change (∑ j : Fin n, ∑ k : Fin n,
    ((1 / 2 : ℝ) * (T x (i, j, k) - T (-x) (i, j, k))) *
      partialTest n k (partialTest n j φ) x) = _
  simp only [tensorPartialContraction, mul_sub, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]

theorem tensor_contraction_oddPart_integral
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    [Measure.IsNegInvariant ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (i : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, tensorPartialContraction n (oddPart T) i φ x ∂ν) = (1 / 2 : ℝ) *
      ((∫ x, tensorPartialContraction n T i φ x ∂ν) -
        (∫ x, tensorPartialContraction n (fun y => T (-y)) i φ x ∂ν)) := by
  have hneg : MemLp (fun x => T (-x)) 2 ν :=
    hT.comp_measurePreserving (Measure.measurePreserving_neg ν)
  simp_rw [tensor_contraction_oddPart]
  rw [integral_const_mul, integral_sub (tensorPartialContraction_integrable n ν T hT i φ)
    (tensorPartialContraction_integrable n ν (fun x => T (-x)) hneg i φ)]

theorem oddPart_preserves_component_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    [Measure.IsNegInvariant ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν)
    (hidentity : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν) =
        ∫ x, tensorPartialContraction n T i φ x ∂ν)
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν) =
      ∫ x, tensorPartialContraction n (oddPart T) i φ x ∂ν := by
  have hreflect : (∫ x, tensorPartialContraction n (fun y => T (-y)) i φ x ∂ν) =
      -((∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν)) := by
    rw [← tensor_contraction_reflected_integral, ← hidentity]
    exact stein_component_left_reflected n ν i φ
  rw [tensor_contraction_oddPart_integral n ν T hT, ← hidentity, hreflect]
  ring

/-- Existence of a genuine L2, odd and centred tensor with the exact
P(P-1)n energy and the component second-order Stein identity. -/
theorem second_stein_exists_odd_tensor_components
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    [Measure.IsNegInvariant ν]
    (P : ℝ) (hPnonneg : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (hmean : ∀ i : Fin n, ∫ x, x i ∂ν = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0) :
    ∃ T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n),
      MemLp T 2 ν ∧ Integrable T ν ∧ (∫ x, T x ∂ν) = 0 ∧
      (∀ x, T (-x) = -T x) ∧ ((∫ x, ‖T x‖ ^ 2 ∂ν) ≤ P * (P - 1) * n) ∧
      (∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
        (∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν) =
          ∫ x, tensorPartialContraction n T i φ x ∂ν) := by
  obtain ⟨T, hT, henergy, hidentity⟩ :=
    second_stein_exists_tensor_components n ν P hPnonneg hP hmean hcov
  have hmeanodd := oddPart_integral_zero ν T hT
  exact ⟨oddPart T, oddPart_memLp ν T hT, hmeanodd.1, hmeanodd.2,
    oddPart_odd T, (oddPart_energy_le ν T hT).trans henergy,
    oddPart_preserves_component_identity n ν T hT hidentity⟩

end AffineFKProof
