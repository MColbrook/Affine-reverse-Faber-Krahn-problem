module

public import AffineFK.SobolevFisherIdentity
public import AffineFK.SobolevDensityProductRule

/-!
# The information energy identity on the actual unweighted Sobolev graph

The genuine square product rule is supplied by the proved Sobolev graph
construction. No compact weak product identity or global coordinate
integration formula is assumed by these statements.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace ENNReal

theorem sobolevFisher_graph_weak_square_product (n : ℕ) (v : unweightedSobolevGraph n)
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (unweightedValue n v x) ^ 2 * partialTest n i φ x) =
      -(2 : ℝ) * (∫ x, unweightedValue n v x * (unweightedGradient n v x) i * φ x) := by
  rw [unweighted_graph_square_product_rule]
  have heq : (∫ x, (2 * unweightedValue n v x * (unweightedGradient n v x) i) * φ x) =
      (2 : ℝ) * (∫ x, unweightedValue n v x * (unweightedGradient n v x) i * φ x) := by
    calc
      _ = ∫ x, (2 : ℝ) * (unweightedValue n v x * (unweightedGradient n v x) i * φ x) :=
        integral_congr_ae (Eventually.of_forall fun x => by dsimp; ring)
      _ = _ := integral_const_mul _ _
  rw [heq]
  ring

theorem sobolevFisher_graph_relative_ordinary_identity (n : ℕ) (v : unweightedSobolevGraph n)
    (hxf : MemLp (fun x => unweightedValue n v x • x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))] :
    Integrable (fun x => ‖(2 : ℝ) • unweightedGradient n v x + unweightedValue n v x • x‖ ^ 2)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x : EuclideanSpace ℝ (Fin n),
      ‖(2 : ℝ) • unweightedGradient n v x + unweightedValue n v x • x‖ ^ 2) =
      4 * (∫ x, ‖unweightedGradient n v x‖ ^ 2) +
        (∫ x, ‖x‖ ^ 2 ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) - 2 * n := by
  exact sobolevFisher_square_root_relative_ordinary_identity n (unweightedValue n v) (unweightedGradient n v)
    (Lp.memLp _) (Lp.memLp _) hxf (sobolevFisher_graph_weak_square_product n v)

theorem sobolevFisher_graph_unit_second_moment_identity (n : ℕ) (v : unweightedSobolevGraph n)
    (hxf : MemLp (fun x => unweightedValue n v x • x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n (fun x => (unweightedValue n v x) ^ 2))]
    (hmoment : (∫ x, ‖x‖ ^ 2 ∂densityMeasure n (fun x => (unweightedValue n v x) ^ 2)) = n) :
    (∫ x : EuclideanSpace ℝ (Fin n),
      ‖(2 : ℝ) • unweightedGradient n v x + unweightedValue n v x • x‖ ^ 2) =
        4 * (∫ x, ‖unweightedGradient n v x‖ ^ 2) - n := by
  have h := (sobolevFisher_graph_relative_ordinary_identity n v hxf).2
  rw [hmoment] at h
  linarith

end AffineFKProof
