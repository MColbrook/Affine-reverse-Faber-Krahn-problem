module

public import AffineFK.BridgeBrownianGaussian

/-!
# Exact means and Brownian covariances on the finite-horizon realization

The covariance calculation uses genuine product independence. The cross
terms vanish, and the independent endpoint contributes `s*t` times the
identity covariance, cancelling the bridge's terminal covariance term.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

def bridgeProductBridgeCoordinate (n : ℕ) (t : Icc (0 : ℝ) 1) (i : Fin n)
    (p : BridgeBrownianSample n) : ℝ := bridgeContinuousSeries n p.1 t i

def bridgeProductEndpointCoordinate (n : ℕ) (i : Fin n) (p : BridgeBrownianSample n) : ℝ := p.2 i

theorem bridgeProductBridgeCoordinate_memLp (n : ℕ) (t : Icc (0 : ℝ) 1) (i : Fin n) :
    MemLp (bridgeProductBridgeCoordinate n t i) 2 (bridgeBrownianProductMeasure n) :=
  ((bridgeContinuousSeries_gaussian_process n).hasGaussianLaw_eval (t, i)).memLp_two.comp_measurePreserving
    (measurePreserving_fst (μ := bridgeCoefficientMeasure n)
      (ν := stdGaussian (EuclideanSpace ℝ (Fin n))))

theorem bridgeProductEndpointCoordinate_memLp (n : ℕ) (i : Fin n) :
    MemLp (bridgeProductEndpointCoordinate n i) 2 (bridgeBrownianProductMeasure n) := by
  have h : MemLp (fun z : EuclideanSpace ℝ (Fin n) => z i) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa only [coordinateFunctional_apply, Function.comp_def, id_eq] using
      ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (coordinateFunctional n i)).memLp_two
  exact h.comp_measurePreserving (measurePreserving_snd (μ := bridgeCoefficientMeasure n)
    (ν := stdGaussian (EuclideanSpace ℝ (Fin n))))

theorem bridgeProductBridgeCoordinate_mean (n : ℕ) (t : Icc (0 : ℝ) 1) (i : Fin n) :
    (∫ p, bridgeProductBridgeCoordinate n t i p ∂bridgeBrownianProductMeasure n) = 0 := by
  calc
    _ = ∫ ω, bridgeContinuousSeries n ω t i ∂bridgeCoefficientMeasure n :=
      (measurePreserving_fst (μ := bridgeCoefficientMeasure n)
        (ν := stdGaussian (EuclideanSpace ℝ (Fin n)))).hasLaw.integral_comp
        ((bridgeContinuousSeries_gaussian_process n).hasGaussianLaw_eval (t, i)).aemeasurable.aestronglyMeasurable
    _ = 0 := bridgeContinuousSeries_coordinate_mean n i t

theorem bridgeProductEndpointCoordinate_mean (n : ℕ) (i : Fin n) :
    (∫ p, bridgeProductEndpointCoordinate n i p ∂bridgeBrownianProductMeasure n) = 0 := by
  calc
    _ = ∫ z : EuclideanSpace ℝ (Fin n), z i ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      (measurePreserving_snd (μ := bridgeCoefficientMeasure n)
        (ν := stdGaussian (EuclideanSpace ℝ (Fin n)))).hasLaw.integral_comp
        (f := fun z : EuclideanSpace ℝ (Fin n) => z i) (by fun_prop)
    _ = 0 := bridgeGaussian_coordinate_mean n i

theorem bridgeProductBridgeCoordinate_covariance (n : ℕ) (s t : Icc (0 : ℝ) 1) (i l : Fin n) :
    cov[bridgeProductBridgeCoordinate n s i, bridgeProductBridgeCoordinate n t l;
      bridgeBrownianProductMeasure n] =
        (min (s : ℝ) t - (s : ℝ) * t) * (if i = l then 1 else 0) := by
  rw [show cov[bridgeProductBridgeCoordinate n s i, bridgeProductBridgeCoordinate n t l;
      bridgeBrownianProductMeasure n] =
        cov[fun ω => bridgeContinuousSeries n ω s i, fun ω => bridgeContinuousSeries n ω t l;
          bridgeCoefficientMeasure n] from
    (measurePreserving_fst (μ := bridgeCoefficientMeasure n)
      (ν := stdGaussian (EuclideanSpace ℝ (Fin n)))).hasLaw.covariance_fun_comp
      ((bridgeContinuousSeries_gaussian_process n).aemeasurable (s, i))
      ((bridgeContinuousSeries_gaussian_process n).aemeasurable (t, l))]
  exact bridgeContinuousSeries_brownian_covariance n i l s t

theorem bridgeProductEndpointCoordinate_covariance (n : ℕ) (i l : Fin n) :
    cov[bridgeProductEndpointCoordinate n i, bridgeProductEndpointCoordinate n l;
      bridgeBrownianProductMeasure n] = if i = l then 1 else 0 := by
  have hGi (q : Fin n) : MemLp (fun z : EuclideanSpace ℝ (Fin n) => z q) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa only [coordinateFunctional_apply, Function.comp_def, id_eq] using
      ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (coordinateFunctional n q)).memLp_two
  calc
    _ = cov[fun z : EuclideanSpace ℝ (Fin n) => z i,
        fun z : EuclideanSpace ℝ (Fin n) => z l; stdGaussian (EuclideanSpace ℝ (Fin n))] :=
      (measurePreserving_snd (μ := bridgeCoefficientMeasure n)
        (ν := stdGaussian (EuclideanSpace ℝ (Fin n)))).hasLaw.covariance_fun_comp
        (hGi i).aemeasurable (hGi l).aemeasurable
    _ = _ := by
      rw [covariance_eq_sub (hGi i) (hGi l), bridgeGaussian_coordinate_mean,
        bridgeGaussian_coordinate_mean, zero_mul, sub_zero]
      exact bridgeGaussian_coordinate_cross_moment n i l

theorem bridgeProductBridgeEndpoint_covariance (n : ℕ) (t : Icc (0 : ℝ) 1) (i l : Fin n) :
    cov[bridgeProductBridgeCoordinate n t i, bridgeProductEndpointCoordinate n l;
      bridgeBrownianProductMeasure n] = 0 := by
  have hmZ : AEMeasurable (fun z : EuclideanSpace ℝ (Fin n) => z l)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa only [coordinateFunctional_apply] using
      (show AEMeasurable (fun z : EuclideanSpace ℝ (Fin n) => coordinateFunctional n l z)
        (stdGaussian (EuclideanSpace ℝ (Fin n))) from
          (coordinateFunctional n l).measurable.aemeasurable)
  have hind : IndepFun (bridgeProductBridgeCoordinate n t i) (bridgeProductEndpointCoordinate n l)
      (bridgeBrownianProductMeasure n) :=
    indepFun_prod₀ ((bridgeContinuousSeries_gaussian_process n).aemeasurable (t, i))
      hmZ
  exact hind.covariance_eq_zero (bridgeProductBridgeCoordinate_memLp n t i)
    (bridgeProductEndpointCoordinate_memLp n l)

theorem bridgeBrownianPath_coordinate_mean (n : ℕ) (t : Icc (0 : ℝ) 1) (i : Fin n) :
    (∫ p, bridgeBrownianPath n p t i ∂bridgeBrownianProductMeasure n) = 0 := by
  change (∫ p, bridgeProductBridgeCoordinate n t i p +
    (t : ℝ) * bridgeProductEndpointCoordinate n i p ∂bridgeBrownianProductMeasure n) = 0
  rw [integral_add ((bridgeProductBridgeCoordinate_memLp n t i).integrable (by norm_num))
      (((bridgeProductEndpointCoordinate_memLp n i).const_mul (t : ℝ)).integrable (by norm_num)),
    integral_const_mul, bridgeProductBridgeCoordinate_mean, bridgeProductEndpointCoordinate_mean]
  ring

theorem bridgeBrownianPath_coordinate_covariance (n : ℕ) (s t : Icc (0 : ℝ) 1) (i l : Fin n) :
    cov[fun p => bridgeBrownianPath n p s i, fun p => bridgeBrownianPath n p t l;
      bridgeBrownianProductMeasure n] = min (s : ℝ) t * (if i = l then 1 else 0) := by
  have hBs := bridgeProductBridgeCoordinate_memLp n s i
  have hBt := bridgeProductBridgeCoordinate_memLp n t l
  have hZs := (bridgeProductEndpointCoordinate_memLp n i).const_mul (s : ℝ)
  have hZt := (bridgeProductEndpointCoordinate_memLp n l).const_mul (t : ℝ)
  change cov[bridgeProductBridgeCoordinate n s i + (fun p => (s : ℝ) * bridgeProductEndpointCoordinate n i p),
    bridgeProductBridgeCoordinate n t l + (fun p => (t : ℝ) * bridgeProductEndpointCoordinate n l p);
      bridgeBrownianProductMeasure n] = _
  rw [covariance_add_left hBs hZs (hBt.add hZt), covariance_add_right hBs hBt hZt,
    covariance_add_right hZs hBt hZt, covariance_const_mul_right,
    covariance_const_mul_left, covariance_const_mul_left, covariance_const_mul_right,
    bridgeProductBridgeCoordinate_covariance, bridgeProductBridgeEndpoint_covariance,
    covariance_comm (bridgeProductEndpointCoordinate n i) (bridgeProductBridgeCoordinate n t l),
    bridgeProductBridgeEndpoint_covariance, bridgeProductEndpointCoordinate_covariance]
  ring

end AffineFKProof
