module

public import AffineFK.BridgeKilledKernel
public import AffineFK.BridgeKilledTransitionKernel

/-!
# Joint measurability of the fixed killed bridge density

The explicit independent-bridge version is jointly measurable in both
endpoints. Its equality with each actual killed transition measure is
retained. No everywhere Chapman--Kolmogorov identity for density versions
is inferred from equality of measures.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

def bridgeEndpointBridgePath (n : ℕ) (T : ℝ) (x y : EuclideanSpace ℝ (Fin n))
    (f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n))) :
    C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) where
  toFun u := x + Real.sqrt T • f u + (u : ℝ) • (y-x)
  continuous_toFun := by fun_prop

theorem bridgeEndpointBridgePath_joint_measurable (n : ℕ) (T : ℝ) :
    Measurable (fun p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
      C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) =>
      bridgeEndpointBridgePath n T p.1.1 p.1.2 p.2) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro u
  change Measurable (fun p : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
      C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) =>
      p.1.1+Real.sqrt T • p.2 u+(u:ℝ) • (p.1.2-p.1.1))
  fun_prop

theorem bridgeEndpointBridgePath_survival_measurable (n : ℕ) (T : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    MeasurableSet {f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) |
      ∀ u : Icc (0 : ℝ) 1, x+Real.sqrt T • f u+(u:ℝ) • (y-x) ∈ Ω} :=
  (bridgeFiniteSurvivalSet_isOpen n 1 Ω hΩ).measurableSet.preimage
    ((bridgeEndpointBridgePath_joint_measurable n T).comp
      ((measurable_const (a := (x,y))).prodMk measurable_id))

theorem bridgeKilledKernel_joint_measurable (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      bridgeKilledKernel n T p.1 Ω p.2) := by
  let A : Set ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
      C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n))) :=
    {p | ∀ u : Icc (0 : ℝ) 1,
      p.1.1+Real.sqrt T • p.2 u+(u:ℝ) • (p.1.2-p.1.1) ∈ Ω}
  have hA : MeasurableSet A := (bridgeFiniteSurvivalSet_isOpen n 1 Ω hΩ).measurableSet.preimage
    (bridgeEndpointBridgePath_joint_measurable n T)
  have hp := measurable_measure_prodMk_left (ν := bridgeSeriesLaw n) hA
  have hf : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (bridgeFreeHeatDensity n T p.1 p.2)) := by
    unfold bridgeFreeHeatDensity standardGaussianDensity
    fun_prop
  convert hf.mul hp using 1
  funext p
  exact bridgeKilledKernel_bridge_formula n T hT p.1 p.2 Ω

theorem bridgeKilledTransitionKernel_eq_withDensity (n : ℕ) (T : ℝ) (hT : 0 < T)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) (x : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledTransitionKernel n T hT Ω hΩ x =
      volume.withDensity (bridgeKilledKernel n T x Ω) :=
  bridgeStartedKilledEndpointMeasure_eq_withDensity n T hT x Ω hΩ

end AffineFKProof
