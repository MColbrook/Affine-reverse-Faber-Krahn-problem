module

public import AffineFK.BridgeMiddleAffinePaths
public import Mathlib.Tactic.FieldSimp

/-!
# The exact Gaussian middle density of an endpoint bridge

The middle variance is `s*t/(s+t)` and the mean is
`x+s/(s+t)(z-x)`. Completing the square in the actual Gaussian density
gives its pointwise product identity, including the full Jacobian.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

/-- The affine Gaussian bridge middle mean, equivalently
`(t*x+s*z)/(s+t)`, between starts x and z at time s. -/
def bridgeGaussianMiddleMean (n : ℕ) (s t : ℝ) (x z : EuclideanSpace ℝ (Fin n)) :=
  x+(s/(s+t)) • (z-x)

theorem bridge_middle_variance_pos (s t : ℝ) (hs : 0 < s) (ht : 0 < t) : 0 < s*t/(s+t) :=
  div_pos (mul_pos hs ht) (add_pos hs ht)

theorem bridge_middle_sqrt_product (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Real.sqrt (s+t) * Real.sqrt (s*t/(s+t)) = Real.sqrt s * Real.sqrt t := by
  rw [← Real.sqrt_mul (add_pos hs ht).le, ← Real.sqrt_mul hs.le]
  congr 1
  field_simp

theorem bridge_middle_density_prefactor (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ((Real.sqrt (s+t))^n)⁻¹ * ((Real.sqrt (s*t/(s+t)))^n)⁻¹ =
      ((Real.sqrt s)^n)⁻¹ * ((Real.sqrt t)^n)⁻¹ := by
  calc
    _ = ((Real.sqrt (s+t)*Real.sqrt (s*t/(s+t)))^n)⁻¹ := by rw [mul_pow,mul_inv]
    _ = _ := by rw [bridge_middle_sqrt_product s t hs ht,mul_pow,mul_inv]

theorem bridge_norm_scaled_sqrt_sq (n : ℕ) (a : ℝ) (ha : 0 < a)
    (w : EuclideanSpace ℝ (Fin n)) : ‖(Real.sqrt a)⁻¹ • w‖^2 = ‖w‖^2/a := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt ha.le]
  ring

theorem bridge_middle_energy_identity (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x y z : EuclideanSpace ℝ (Fin n)) :
    ‖y-x‖^2/s+‖z-y‖^2/t = ‖z-x‖^2/(s+t)+
      ‖y-bridgeGaussianMiddleMean n s t x z‖^2/(s*t/(s+t)) := by
  let a := y-x
  let b := z-x
  let c := s/(s+t)
  have hzy : z-y = b-a := by dsimp [a,b]; abel
  have hym : y-bridgeGaussianMiddleMean n s t x z = a-c • b := by
    dsimp [bridgeGaussianMiddleMean,a,b,c]
    module
  rw [hzy,hym]
  change ‖a‖^2/s+‖b-a‖^2/t = ‖b‖^2/(s+t)+‖a-c • b‖^2/(s*t/(s+t))
  rw [norm_sub_sq_real b a,norm_sub_sq_real a (c • b),real_inner_smul_right,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm b a]
  dsimp [c]
  field_simp [hs.ne',ht.ne',(add_pos hs ht).ne']
  ring

theorem bridge_standardGaussian_product_of_norm_sq (n : ℕ)
    (a b c d : EuclideanSpace ℝ (Fin n)) (h : ‖a‖^2+‖b‖^2 = ‖c‖^2+‖d‖^2) :
    standardGaussianDensity n a * standardGaussianDensity n b =
      standardGaussianDensity n c * standardGaussianDensity n d := by
  apply Real.log_injOn_pos
    (mul_pos (standardGaussianDensity_pos n a) (standardGaussianDensity_pos n b))
    (mul_pos (standardGaussianDensity_pos n c) (standardGaussianDensity_pos n d))
  rw [Real.log_mul (standardGaussianDensity_pos n a).ne' (standardGaussianDensity_pos n b).ne',
    Real.log_mul (standardGaussianDensity_pos n c).ne' (standardGaussianDensity_pos n d).ne',
    log_standardGaussianDensity, log_standardGaussianDensity,
    log_standardGaussianDensity, log_standardGaussianDensity]
  linarith

theorem bridge_free_heat_middle_product (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x y z : EuclideanSpace ℝ (Fin n)) :
    bridgeFreeHeatDensity n (s+t) x z *
      bridgeFreeHeatDensity n (s*t/(s+t)) (bridgeGaussianMiddleMean n s t x z) y =
      bridgeFreeHeatDensity n s x y * bridgeFreeHeatDensity n t y z := by
  have henergy : ‖(Real.sqrt (s+t))⁻¹ • (z-x)‖^2+
      ‖(Real.sqrt (s*t/(s+t)))⁻¹ • (y-bridgeGaussianMiddleMean n s t x z)‖^2 =
      ‖(Real.sqrt s)⁻¹ • (y-x)‖^2+‖(Real.sqrt t)⁻¹ • (z-y)‖^2 := by
    rw [bridge_norm_scaled_sqrt_sq n (s+t) (add_pos hs ht),
      bridge_norm_scaled_sqrt_sq n (s*t/(s+t)) (bridge_middle_variance_pos s t hs ht),
      bridge_norm_scaled_sqrt_sq n s hs, bridge_norm_scaled_sqrt_sq n t ht]
    exact (bridge_middle_energy_identity n s t hs ht x y z).symm
  have hg := bridge_standardGaussian_product_of_norm_sq n _ _ _ _ henergy
  have hp := bridge_middle_density_prefactor n s t hs ht
  unfold bridgeFreeHeatDensity
  calc
    _ = (((Real.sqrt (s+t))^n)⁻¹*((Real.sqrt (s*t/(s+t)))^n)⁻¹) *
      (standardGaussianDensity n ((Real.sqrt (s+t))⁻¹ • (z-x)) *
        standardGaussianDensity n ((Real.sqrt (s*t/(s+t)))⁻¹ • (y-bridgeGaussianMiddleMean n s t x z))) := by ring
    _ = _ := by rw [hp,hg]; ring

theorem bridgeSplitMiddlePoint_hasLaw_density (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x z : EuclideanSpace ℝ (Fin n)) :
    HasLaw (bridgeSplitMiddlePoint n s t x z)
      (volume.withDensity (fun y => ENNReal.ofReal
        (bridgeFreeHeatDensity n (s*t/(s+t)) (bridgeGaussianMiddleMean n s t x z) y)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hv := bridge_middle_variance_pos s t hs ht
  have hσ : 0 < bridgeMiddleScale s t := Real.sqrt_pos.mpr hv
  refine ⟨(bridgeSplitMiddlePoint_measurable n s t x z).aemeasurable, ?_⟩
  rw [stdGaussian_eq_densityMeasure, densityMeasure]
  change (volume.withDensity (fun w => ENNReal.ofReal (standardGaussianDensity n w))).map
    (fun w => bridgeGaussianMiddleMean n s t x z+bridgeMiddleScale s t • w) = _
  rw [bridge_affine_density_map n (bridgeMiddleScale s t) hσ (bridgeGaussianMiddleMean n s t x z)
    (fun w => ENNReal.ofReal (standardGaussianDensity n w))
    (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal]
  congr 1
  funext y
  exact (ENNReal.ofReal_mul (by positivity : 0 ≤ ((bridgeMiddleScale s t)^n)⁻¹)).symm

end AffineFKProof
