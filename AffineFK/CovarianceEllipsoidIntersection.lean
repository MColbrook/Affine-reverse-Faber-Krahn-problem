module

public import AffineFK.CovarianceEllipsoidMass
public import AffineFK.WeightedTestIntegration

/-!
# Intersection volume from a genuine bounded probability density

The actual covariance ellipsoid has mass at least one half. A density
supported on K and at most exp(n) there therefore gives an intersection
volume at least (1/(2*exp(1)))^n, for every positive dimension. Tonelli
and the actual density measure are used; no desired volume is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator

theorem densityMeasure_mass_le_intersection_volume (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (K E : Set (EuclideanSpace ℝ (Fin n)))
    (hK : MeasurableSet K) (hE : MeasurableSet E) (d : ℝ)
    (hsupport : ∀ x, x ∉ K → ρ x = 0) (hbound : ∀ x ∈ K, ρ x ≤ d) :
    densityMeasure n ρ E ≤ ENNReal.ofReal d * volume (K ∩ E) := by
  have hpoint : ∀ x, ENNReal.ofReal (ρ x) ≤ K.indicator (fun _ => ENNReal.ofReal d) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (hbound x hx)
    · rw [hsupport x hx,ENNReal.ofReal_zero,indicator_of_notMem hx]
  rw [densityMeasure,withDensity_apply _ hE]
  calc
    _ ≤ ∫⁻ x in E, K.indicator (fun _ => ENNReal.ofReal d) x := lintegral_mono hpoint
    _ = ENNReal.ofReal d * volume (K ∩ E) := by
      rw [lintegral_indicator hK,Measure.restrict_restrict hK,lintegral_const,
        Measure.restrict_apply_univ]

theorem covarianceEllipsoid_intersection_scalar (n : ℕ) (hn : 0 < n) :
    (1/(2*Real.exp 1))^n ≤ (1/2 : ℝ)/Real.exp (n : ℝ) := by
  have htwo : (2 : ℝ) ≤ (2 : ℝ)^n := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  have hreciprocal : (1 : ℝ)/(2 : ℝ)^n ≤ 1/2 :=
    one_div_le_one_div_of_le (by norm_num) htwo
  have heq : (Real.exp 1)^n = Real.exp (n : ℝ) := by
    rw [← Real.exp_nat_mul]
    simp only [mul_one]
  have hformula : (1/(2*Real.exp 1))^n = ((1 : ℝ)/(2 : ℝ)^n)/Real.exp (n : ℝ) := by
    rw [div_pow,mul_pow,one_pow,heq]
    field_simp
  rw [hformula]
  exact (div_le_div_iff_of_pos_right (Real.exp_pos _)).mpr hreciprocal

theorem covarianceEllipsoid_intersection_lower (n : ℕ) (hn : 0 < n)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ)
    (m : EuclideanSpace ℝ (Fin n)) (hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hlaw : μ = densityMeasure n ρ)
    (hsupport : ∀ x, x ∉ K → ρ x = 0)
    (hbound : ∀ x ∈ K, ρ x ≤ Real.exp (n : ℝ)) :
    (1/(2*Real.exp 1))^n ≤ (volume (K ∩ covarianceEllipsoidSet n μ m hM)).toReal := by
  let E := covarianceEllipsoidSet n μ m hM
  have hE : IsCompact E := covarianceEllipsoidSet_compact n μ m hM
  have hupper : μ E ≤ ENNReal.ofReal (Real.exp (n : ℝ))*volume (K ∩ E) := by
    rw [hlaw]
    exact densityMeasure_mass_le_intersection_volume n ρ K E hK.measurableSet hE.measurableSet
      (Real.exp (n : ℝ)) hsupport hbound
  have hvolumeFinite : volume (K ∩ E) ≠ ∞ := (hK.inter_right hE.isClosed).measure_ne_top
  have hupperReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolumeFinite) hupper
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le] at hupperReal
  have hhalf : (1/2 : ℝ) ≤ μ.real E := covarianceEllipsoidSet_mass_real n hn μ hX m hM
  have hvolume : (1/2 : ℝ)/Real.exp (n : ℝ) ≤ (volume (K ∩ E)).toReal := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    exact hhalf.trans (by simpa only [mul_comm,measureReal_def] using hupperReal)
  exact (covarianceEllipsoid_intersection_scalar n hn).trans hvolume

end AffineFKProof
