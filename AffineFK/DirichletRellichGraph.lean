module

public import AffineFK.DirichletSobolev
public import AffineFK.BenensonRellich.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1

/-!
# Identifying the two genuine value-gradient completions

Adam Benenson's Apache-2.0 Euclidean Rellich proof uses the ordinary product
norm on its L2 value-gradient graph. Our H1 graph uses the equivalent Hilbert
product norm. The actual product equivalence carries every compact smooth
test to the same C1 value-gradient pair, hence carries its closure into the
imported graph. No compactness or eigenfunction is a premise here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

def dirichletRellichAmbient (n : ℕ) :
    SobolevAmbient (volume : Measure (EuclideanSpace ℝ (Fin n))) ≃L[ℝ]
      (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ×
        Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ _ _

def dirichletRellichTest (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    C1c (E := EuclideanSpace ℝ (Fin n)) :=
  ⟨φ, φ.contDiff.of_le (by simp), φ.hasCompactSupport⟩

theorem dirichletRellich_test_pair (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    dirichletRellichAmbient n (unweightedSmoothPair n φ) =
      graph (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) (dirichletRellichTest n φ) := by
  apply Prod.ext
  · apply Lp.ext
    exact (unweightedTestToL2_coe n φ).trans
      (memLp_of_mem_C1c (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (dirichletRellichTest n φ).property).coeFn_toLp.symm
  · apply Lp.ext
    have hleft := unweightedTestToL2_coe n (testFunctionGradient φ)
    have hright := (memLp_grad_of_mem_C1c
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (dirichletRellichTest n φ).property).coeFn_toLp
    filter_upwards [hleft, hright] with x hx hy
    exact hx.trans ((testFunctionGradient_apply φ x).trans hy.symm)

theorem dirichletRellich_graph_mem (n : ℕ) (v : unweightedSobolevGraph n) :
    dirichletRellichAmbient n (v : SobolevAmbient
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∈
        h1 (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hclosed : IsClosed ((dirichletRellichAmbient n) ⁻¹'
      (h1 (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) : Set _)) :=
    (isClosed_h1 (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))).preimage
      (dirichletRellichAmbient n).continuous
  apply closure_minimal _ hclosed v.property
  rintro _ ⟨φ, rfl⟩
  change dirichletRellichAmbient n (unweightedSmoothPair n φ) ∈
    h1 (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
  rw [dirichletRellich_test_pair]
  exact (graph (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))).range.le_topologicalClosure
    ⟨dirichletRellichTest n φ, rfl⟩

def dirichletRellichGraph (n : ℕ) :
    unweightedSobolevGraph n →L[ℝ]
      h1 (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
  (((dirichletRellichAmbient n).toContinuousLinearMap).comp
    (unweightedSobolevGraph n).subtypeL).codRestrict _ (dirichletRellich_graph_mem n)

theorem dirichletRellichGraph_value (n : ℕ) (v : unweightedSobolevGraph n) :
    h1ToL2 (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (dirichletRellichGraph n v) = unweightedValue n v := rfl

theorem dirichletRellichGraph_gradient (n : ℕ) (v : unweightedSobolevGraph n) :
    h1ToL2Grad (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (dirichletRellichGraph n v) = unweightedGradient n v := rfl

end AffineFKProof
