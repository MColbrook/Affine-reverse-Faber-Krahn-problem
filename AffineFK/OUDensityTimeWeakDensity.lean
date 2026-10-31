module

public import AffineFK.OUDensityTimeWeakEquation
public import AffineFK.GaussianSmoothingDensity

/-!
# The positive-time weak density equation for the actual OU density

The product-space equation is transported first to the actual image law,
then to the explicit Gaussian-mixture Lebesgue density. Equality with the
density law is used only in a positive-time neighbourhood. There is no
assumption of time differentiability of that density or of its entropy.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped Distributions Topology

theorem ou_law_test_expectation_weak_equation (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ x, φ x
      ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2))
      (∫ x, ouTestGenerator n φ x
        ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) t := by
  have heq (s : ℝ) (ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
      (∫ x, ψ x ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2)) =
      ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ψ (Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    integral_map (by fun_prop) ψ.continuous.aestronglyMeasurable
  simp_rw [heq]
  exact ou_test_expectation_weak_equation n ν hU φ t ht

theorem ou_density_test_expectation_weak_equation (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ x, φ x
      ∂densityMeasure n (gaussianSmoothingDensity n ν (Real.exp (-s))
        (Real.sqrt (1 - Real.exp (-2 * s)))))
      (∫ x, ouTestGenerator n φ x
        ∂densityMeasure n (gaussianSmoothingDensity n ν (Real.exp (-t))
          (Real.sqrt (1 - Real.exp (-2 * t))))) t := by
  have h := ou_law_test_expectation_weak_equation n ν hU φ t ht
  rw [gaussianSmoothingDensity_law n ν _ _ (ou_smoothing_scale_domain t ht).2.1] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  rw [gaussianSmoothingDensity_law n ν _ _ (ou_smoothing_scale_domain s hs).2.1]

end AffineFKProof
