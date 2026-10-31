module

public import AffineFK.OrdinaryFisherLinearMapH1

/-!
# The exact Sobolev energy factor under invertible linear maps

The square-root Jacobian makes scalar L2 pullback isometric. Applying the
inverse adjoint to the actual input graph gradient then gives the exact
squared operator-norm bound, with the genuine transformed H1 square root
already constructed by compact smooth approximation.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

theorem ordinaryFisherLinear_scaled_pullback_energy (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (fun z => Real.sqrt (ordinaryFisherLinearJacobian n A) • f (A.symm z)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ z, ‖Real.sqrt (ordinaryFisherLinearJacobian n A) • f (A.symm z)‖ ^ 2) =
      ∫ x, ‖f x‖ ^ 2 := by
  have hp : MemLp (fun z => f (A.symm z)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (Lp.memLp (ordinaryFisherLinearPullbackLp n A F f)).ae_eq
      (ordinaryFisherLinearPullbackLp_coe n A f)
  refine ⟨hp.const_smul _, ?_⟩
  have hm : (∫ z, ‖f (A.symm z)‖ ^ 2
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).map A) = ∫ x, ‖f x‖ ^ 2 := by
    rw [integral_map (f := fun z => ‖f (A.symm z)‖ ^ 2) A.continuous.measurable.aemeasurable
      (((Lp.stronglyMeasurable f).comp_measurable A.symm.continuous.measurable).norm.pow 2).aestronglyMeasurable]
    simp only [A.symm_apply_apply]
  rw [ordinaryFisherLinearMap_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (ordinaryFisherLinearJacobian_pos n A).le] at hm
  simp only [smul_eq_mul] at hm
  calc
    _ = (Real.sqrt (ordinaryFisherLinearJacobian n A)) ^ 2 *
        ∫ z, ‖f (A.symm z)‖ ^ 2 := by
      simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      exact integral_const_mul _ _
    _ = _ := by rw [Real.sq_sqrt (ordinaryFisherLinearJacobian_pos n A).le, hm]

theorem ordinaryFisherLinear_adjoint_energy_bound (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x, ‖A.symm.toContinuousLinearMap.adjoint (g x)‖ ^ 2) ≤
      ‖A.symm.toContinuousLinearMap‖ ^ 2 * ∫ x, ‖g x‖ ^ 2 := by
  have hg := (memLp_two_iff_integrable_sq_norm (Lp.memLp g).aestronglyMeasurable).mp (Lp.memLp g)
  have ha : MemLp (fun x => A.symm.toContinuousLinearMap.adjoint (g x)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply ((Lp.memLp g).norm.const_mul ‖A.symm.toContinuousLinearMap.adjoint‖).mono'
      (A.symm.toContinuousLinearMap.adjoint.continuous.comp_stronglyMeasurable
        (Lp.stronglyMeasurable g)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => A.symm.toContinuousLinearMap.adjoint.le_opNorm (g x)
  have ha2 := (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mp ha
  rw [← integral_const_mul]
  apply integral_mono_ae ha2 (hg.const_mul _)
  exact Filter.Eventually.of_forall fun x => by
    have hb := A.symm.toContinuousLinearMap.adjoint.le_opNorm (g x)
    have hn : ‖A.symm.toContinuousLinearMap.adjoint‖ = ‖A.symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    rw [hn] at hb
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hb

theorem ordinaryFisher_linear_sqrt_H1_energy (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x)) :
    ∃ w : unweightedSobolevGraph n,
      (unweightedValue n w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        (fun z => Real.sqrt (ordinaryFisherLinearDensity n A ρ z)) ∧
      (unweightedGradient n w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
        (fun z => Real.sqrt (ordinaryFisherLinearJacobian n A) •
          A.symm.toContinuousLinearMap.adjoint (unweightedGradient n v (A.symm z))) ∧
      (4 * ∫ z, ‖unweightedGradient n w z‖ ^ 2) ≤
        ‖A.symm.toContinuousLinearMap‖ ^ 2 * (4 * ∫ x, ‖unweightedGradient n v x‖ ^ 2) := by
  obtain ⟨w, hwv, hwg⟩ := ordinaryFisher_linear_sqrt_graph n A ρ v hv
  let g := unweightedGradient n v
  let q := A.symm.toContinuousLinearMap.adjoint.compLp g
  have hq := A.symm.toContinuousLinearMap.adjoint.coeFn_compLp' g
  have hA := ordinaryFisherLinearMap_quasiMeasurePreserving n A.symm
  have heq : (fun z => ‖unweightedGradient n w z‖ ^ 2) =ᵐ[volume]
      fun z => ‖Real.sqrt (ordinaryFisherLinearJacobian n A) • q (A.symm z)‖ ^ 2 := by
    filter_upwards [hwg, hA.ae_eq_comp hq] with z hw hqq
    change q (A.symm z) = A.symm.toContinuousLinearMap.adjoint (g (A.symm z)) at hqq
    rw [hw, hqq]
  have henergy : (∫ z, ‖unweightedGradient n w z‖ ^ 2) =
      ∫ x, ‖A.symm.toContinuousLinearMap.adjoint (g x)‖ ^ 2 := by
    rw [integral_congr_ae heq, (ordinaryFisherLinear_scaled_pullback_energy n A q).2]
    apply integral_congr_ae
    filter_upwards [hq] with x hx
    rw [hx]
  refine ⟨w, hwv, hwg, ?_⟩
  rw [henergy]
  have hb := mul_le_mul_of_nonneg_left (ordinaryFisherLinear_adjoint_energy_bound n A g)
    (by norm_num : (0 : ℝ) ≤ 4)
  simpa only [g, mul_assoc, mul_left_comm] using hb

theorem ordinaryFisher_linear_H1_transport_with_law (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    (v : unweightedSobolevGraph n)
    (hv : (unweightedValue n v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => Real.sqrt (ρ x)) :
    (densityMeasure n ρ).map A = densityMeasure n (ordinaryFisherLinearDensity n A ρ) ∧
    ∃ w : unweightedSobolevGraph n,
      (unweightedValue n w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
        (fun z => Real.sqrt (ordinaryFisherLinearDensity n A ρ z)) ∧
      (unweightedGradient n w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
        (fun z => Real.sqrt (ordinaryFisherLinearJacobian n A) •
          A.symm.toContinuousLinearMap.adjoint (unweightedGradient n v (A.symm z))) ∧
      (4 * ∫ z, ‖unweightedGradient n w z‖ ^ 2) ≤
        ‖A.symm.toContinuousLinearMap‖ ^ 2 * (4 * ∫ x, ‖unweightedGradient n v x‖ ^ 2) := by
  exact ⟨ordinaryFisherLinearDensity_law n A ρ hρ,
    ordinaryFisher_linear_sqrt_H1_energy n A ρ v hv⟩

end AffineFKProof
