module

public import AffineFK.BridgeBrownianIncrements

/-!
# Genuine Brownian scaling to an arbitrary positive finite horizon

The transformed path is `sqrt(T) B(t/T)` on `[0,T]`. Its covariance is
`min(s,t)` times the identity, preserving the generator Δ/2 convention.
The construction uses the already proved actual probability law.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

def bridgeUnitTime (T : ℝ) (hT : 0 < T) (t : Icc (0 : ℝ) T) : Icc (0 : ℝ) 1 :=
  ⟨(t : ℝ) / T, div_nonneg t.property.1 hT.le, (div_le_one hT).mpr t.property.2⟩

theorem bridgeUnitTime_continuous (T : ℝ) (hT : 0 < T) : Continuous (bridgeUnitTime T hT) :=
  (continuous_subtype_val.div_const T).subtype_mk _

theorem bridgeUnitTime_monotone (T : ℝ) (hT : 0 < T) : Monotone (bridgeUnitTime T hT) := by
  intro s t hst
  exact div_le_div_of_nonneg_right hst hT.le

def bridgeScaledBrownianPath (n : ℕ) (T : ℝ) (hT : 0 < T)
    (f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n))) :
    C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) where
  toFun t := Real.sqrt T • f (bridgeUnitTime T hT t)
  continuous_toFun := (f.continuous.comp (bridgeUnitTime_continuous T hT)).const_smul (Real.sqrt T)

theorem bridgeScaledBrownianPath_measurable (n : ℕ) (T : ℝ) (hT : 0 < T) :
    Measurable (bridgeScaledBrownianPath n T hT) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (ContinuousMap.measurable_eval (bridgeUnitTime T hT t)).const_smul (Real.sqrt T)

def bridgeScaledBrownianLaw (n : ℕ) (T : ℝ) (hT : 0 < T) :
    Measure C(Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin n)) :=
  (bridgeBrownianLaw n).map (bridgeScaledBrownianPath n T hT)

instance bridgeScaledBrownianLaw_probability (n : ℕ) (T : ℝ) (hT : 0 < T) :
    IsProbabilityMeasure (bridgeScaledBrownianLaw n T hT) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (bridgeScaledBrownianPath_measurable n T hT).aemeasurable).mpr inferInstance

theorem bridgeScaledBrownianPath_gaussian_process (n : ℕ) (T : ℝ) (hT : 0 < T) :
    IsGaussianProcess (fun q : Icc (0 : ℝ) T × Fin n =>
      fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) =>
        bridgeScaledBrownianPath n T hT f q.1 q.2) (bridgeBrownianLaw n) := by
  exact ((bridgeBrownianLaw_gaussian_process n).comp_right
    (fun q : Icc (0 : ℝ) T × Fin n => (bridgeUnitTime T hT q.1, q.2))).smul
      (fun _ => Real.sqrt T)

theorem bridgeScaledBrownianPath_hasIndepIncrements (n : ℕ) (T : ℝ) (hT : 0 < T) :
    HasIndepIncrements (fun t : Icc (0 : ℝ) T =>
      fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) =>
        bridgeScaledBrownianPath n T hT f t) (bridgeBrownianLaw n) := by
  have hinc : HasIndepIncrements (fun t : Icc (0 : ℝ) T =>
      fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f (bridgeUnitTime T hT t))
        (bridgeBrownianLaw n) := by
    intro m t ht
    exact bridgeBrownianLaw_hasIndepIncrements n m (fun i => bridgeUnitTime T hT (t i))
      ((bridgeUnitTime_monotone T hT).comp ht)
  exact hinc.smul (Real.sqrt T)

theorem bridgeScaledBrownianPath_coordinate_mean (n : ℕ) (T : ℝ) (hT : 0 < T)
    (t : Icc (0 : ℝ) T) (i : Fin n) :
    (∫ f, bridgeScaledBrownianPath n T hT f t i ∂bridgeBrownianLaw n) = 0 := by
  change (∫ f, Real.sqrt T * f (bridgeUnitTime T hT t) i ∂bridgeBrownianLaw n) = 0
  rw [integral_const_mul, bridgeBrownianLaw_coordinate_mean, mul_zero]

theorem bridgeScaledBrownianPath_coordinate_covariance (n : ℕ) (T : ℝ) (hT : 0 < T)
    (s t : Icc (0 : ℝ) T) (i l : Fin n) :
    cov[fun f => bridgeScaledBrownianPath n T hT f s i,
      fun f => bridgeScaledBrownianPath n T hT f t l; bridgeBrownianLaw n] =
        min (s : ℝ) t * (if i = l then 1 else 0) := by
  change cov[fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) =>
      Real.sqrt T * f (bridgeUnitTime T hT s) i,
    fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) =>
      Real.sqrt T * f (bridgeUnitTime T hT t) l; bridgeBrownianLaw n] = _
  rw [covariance_const_mul_left, covariance_const_mul_right, bridgeBrownianLaw_coordinate_covariance]
  change Real.sqrt T * (Real.sqrt T * (min ((s : ℝ) / T) ((t : ℝ) / T) *
    (if i = l then 1 else 0))) = _
  rw [min_div_div_right hT.le]
  calc
    _ = (Real.sqrt T * Real.sqrt T) * (min (s : ℝ) t / T) * (if i = l then 1 else 0) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hT.le]; field_simp

theorem bridgeScaledBrownianPath_sub_terminal (n : ℕ) (T : ℝ) (hT : 0 < T)
    (p : BridgeBrownianSample n) (t : Icc (0 : ℝ) T) :
    bridgeScaledBrownianPath n T hT (bridgeBrownianPath n p) t -
      ((t : ℝ) / T) • bridgeScaledBrownianPath n T hT (bridgeBrownianPath n p)
        ⟨T, hT.le, le_rfl⟩ =
      Real.sqrt T • bridgeContinuousSeries n p.1 (bridgeUnitTime T hT t) := by
  have hterminal : bridgeUnitTime T hT ⟨T, hT.le, le_rfl⟩ = (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    exact div_self hT.ne'
  change Real.sqrt T • bridgeBrownianPath n p (bridgeUnitTime T hT t) -
    ((t : ℝ) / T) • (Real.sqrt T • bridgeBrownianPath n p (bridgeUnitTime T hT ⟨T, hT.le, le_rfl⟩)) = _
  rw [hterminal]
  calc
    _ = Real.sqrt T • (bridgeBrownianPath n p (bridgeUnitTime T hT t) -
        ((t : ℝ) / T) • bridgeBrownianPath n p ⟨1, by norm_num⟩) := by
      rw [smul_sub, smul_smul, smul_smul, mul_comm ((t : ℝ) / T) (Real.sqrt T)]
    _ = _ := congrArg (fun x : EuclideanSpace ℝ (Fin n) => Real.sqrt T • x)
      (bridgeBrownianPath_sub_terminal n p (bridgeUnitTime T hT t))

end AffineFKProof
