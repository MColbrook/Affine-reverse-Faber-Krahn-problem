module

public import AffineFK.BridgeSchauderSeries
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurable continuous paths from the actual Gaussian coefficient series

Summation in the Banach space `C([0,1], R^n)` produces a continuous path
for every coefficient array, including the usual zero value of a
nonsummable series. On the coefficient event the series genuinely
converges and has the exact radius in the manuscript. The induced law is
an actual probability measure. Its identification as the standard
Brownian bridge remains a separate theorem, not an assumption here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology

def bridgeSchauderLevelMap (n j : ℕ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) :
    C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) :=
  ⟨fun t => bridgeSchauderLevel n j ω t,
    (bridgeSchauderLevel_continuous n j ω).comp continuous_subtype_val⟩

def bridgeContinuousSeries (n : ℕ)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) :
    C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) := ∑' j, bridgeSchauderLevelMap n j ω

theorem bridgeSchauderLevelMap_measurable (n j : ℕ) :
    Measurable (bridgeSchauderLevelMap n j) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun ω => bridgeSchauderLevel n j ω t)
  unfold bridgeSchauderLevel
  fun_prop

theorem bridgeContinuousSeries_measurable (n : ℕ) : Measurable (bridgeContinuousSeries n) := by
  exact Measurable.tsum (fun j => bridgeSchauderLevelMap_measurable n j)

theorem bridgeContinuousSeries_eq (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D)
    (a : ℝ) (ha : a < 1 / 2)
    (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n))
    (hω : ω ∈ bridgeCoefficientEvent n D a) (t : Icc (0 : ℝ) 1) :
    bridgeContinuousSeries n ω t = bridgeSchauderSeries n ω t := by
  obtain ⟨M, hM, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  have hgeom := (two_rpow_multiple_hasSum (a - 1 / 2) (by linarith)).summable.mul_left (M / 2)
  have hnorm (j : ℕ) : ‖bridgeSchauderLevelMap n j ω‖ ≤
      (M / 2) * (2 : ℝ) ^ ((a - 1 / 2) * (j : ℝ)) := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    exact bridgeSchauderLevel_norm_bound n D M hM.le hbound a ω hω j x
  have hs : Summable (fun j => bridgeSchauderLevelMap n j ω) := hgeom.of_norm_bounded hnorm
  exact (ContinuousMap.evalCLM ℝ t).map_tsum hs

/-- The actual law of the continuous coefficient series; not yet identified
with the standard Brownian-bridge law. -/
def bridgeSeriesLaw (n : ℕ) : Measure C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) :=
  (bridgeCoefficientMeasure n).map (bridgeContinuousSeries n)

instance bridgeSeriesLaw_probability (n : ℕ) : IsProbabilityMeasure (bridgeSeriesLaw n) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (bridgeContinuousSeries_measurable n).aemeasurable).mpr inferInstance

theorem bridgeSeriesLaw_radius_lower
    (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n))) (hcompact : IsCompact D)
    (hconvex : Convex ℝ D) (hzero : 0 ∈ interior D)
    (p a A : ℝ) (hp : 2 < p) (ha : 1 / p < a) (hupper : a < 1 / 2) (hA : 0 ≤ A)
    (hprofile : ∀ t : ℝ, 1 ≤ t →
      -Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))) (t • D)).toReal ≤ A * t ^ (-p)) :
    ENNReal.ofReal (Real.exp (-A / (1 - (2 : ℝ) ^ (1 - a * p)))) ≤
      bridgeSeriesLaw n {f | ∀ t : Icc (0 : ℝ) 1, gauge D (f t) ≤
        1 / (2 * (1 - (2 : ℝ) ^ (a - 1 / 2)))} := by
  let R := 1 / (2 * (1 - (2 : ℝ) ^ (a - 1 / 2)))
  have hnhds : D ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) := mem_interior_iff_mem_nhds.mp hzero
  have hclosed : IsClosed {f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) |
      ∀ t, gauge D (f t) ≤ R} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun t => isClosed_le
      ((continuous_gauge hconvex hnhds).comp (continuous_eval_const t)) continuous_const)
  have hcoeff := bridgeCoefficientEvent_probability_lower_of_log n D hcompact.isClosed.measurableSet
    ⟨0, hzero⟩ p a A hp ha hupper hA hprofile
  rw [bridgeSeriesLaw, Measure.map_apply (bridgeContinuousSeries_measurable n) hclosed.measurableSet]
  apply hcoeff.trans (measure_mono ?_)
  intro ω hω t
  rw [bridgeContinuousSeries_eq n D hcompact a hupper ω hω t]
  exact (bridgeSchauderSeries_controlled n D hcompact hconvex hzero a hupper ω hω).2.2 t

end AffineFKProof
