module

public import AffineFK.GaussianEntropyCalculusDissipation
public import AffineFK.SobolevApproximation

/-!
# Spatial cutoff limits for truncated entropy dissipation

The boundary estimate uses a bounded scalar derivative and the first
moment of an L2 vector field. The elementary bound norm(v) <= 1+norm(v)^2
avoids any higher moment. The main term is dominated by the actual square
norm energy. These are spatial limits at a fixed probability law, not an
asserted interchange with the time integral.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Filter
open scoped Distributions RealInnerProductSpace Topology

theorem entropy_boundary_flux_bound (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 μ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hgm : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hgb : ∀ x, ‖g x‖ ≤ B)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (M : ℝ) (hM : 0 ≤ M) (hgrad : ∀ x, ‖gradient φ x‖ ≤ M) :
    Integrable (fun x => g x * ⟪v x, gradient φ x⟫) μ ∧
    ‖∫ x, g x * ⟪v x, gradient φ x⟫ ∂μ‖ ≤
      B * M * (1 + ∫ x, ‖v x‖ ^ 2 ∂μ) := by
  have hnorm : Integrable (fun x => ‖v x‖) μ := (hv.integrable (by norm_num)).norm
  have hsq : Integrable (fun x => ‖v x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hgradm : StronglyMeasurable (gradient φ) := by
    have heq : (testFunctionGradient φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
        gradient φ := funext (testFunctionGradient_apply φ)
    rw [← heq]
    exact (testFunctionGradient φ).continuous.stronglyMeasurable
  have hfm : AEStronglyMeasurable (fun x => g x * ⟪v x, gradient φ x⟫) μ :=
    hgm.aestronglyMeasurable.mul (hv.aestronglyMeasurable.inner hgradm.aestronglyMeasurable)
  have hb (x) : ‖g x * ⟪v x, gradient φ x⟫‖ ≤ (B * M) * ‖v x‖ := by
    rw [norm_mul]
    calc
      _ ≤ B * (‖v x‖ * ‖gradient φ x‖) :=
        mul_le_mul (hgb x) (norm_inner_le_norm _ _) (norm_nonneg _) hB
      _ ≤ B * (‖v x‖ * M) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hgrad x) (norm_nonneg _)) hB
      _ = _ := by ring
  have hi : Integrable (fun x => (B * M) * ‖v x‖) μ := hnorm.const_mul (B * M)
  have hnle : (∫ x, ‖v x‖ ∂μ) ≤ 1 + ∫ x, ‖v x‖ ^ 2 ∂μ := by
    have h := integral_mono hnorm ((integrable_const (1 : ℝ)).add hsq)
      (fun x => by
        change ‖v x‖ ≤ 1 + ‖v x‖ ^ 2
        nlinarith [sq_nonneg (‖v x‖ - 1), norm_nonneg (v x)])
    simpa only [Pi.add_apply, integral_add (integrable_const (1 : ℝ)) hsq,
      integral_const, probReal_univ, one_smul] using h
  refine ⟨hi.mono' hfm (Filter.Eventually.of_forall hb), ?_⟩
  calc
    _ ≤ ∫ x, (B * M) * ‖v x‖ ∂μ := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
    _ = B * M * ∫ x, ‖v x‖ ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hnle (mul_nonneg hB hM)

theorem entropy_boundary_flux_cutoff_tendsto_zero (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 μ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hgm : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hgb : ∀ x, ‖g x‖ ≤ B)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (M : ℝ) (hM : 0 ≤ M) (hgrad : ∀ x, ‖gradient χ x‖ ≤ M) :
    Tendsto (fun k : ℕ => ∫ x, g x * ⟪v x, gradient (cutoffSequence χ k) x⟫ ∂μ)
      atTop (𝓝 0) := by
  have hb (k : ℕ) := (entropy_boundary_flux_bound n μ v hv g hgm B hB hgb
    (cutoffSequence χ k) (M / ((k : ℝ) + 1)) (by positivity)
      (gradient_scaledTestFunction_bound ((k : ℝ) + 1) (by positivity) χ M hgrad)).2
  have hlim : Tendsto (fun k : ℕ => B * (M / ((k : ℝ) + 1)) *
      (1 + ∫ x, ‖v x‖ ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul] using
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul tendsto_inverse_succ)).mul_const
        (1 + ∫ x, ‖v x‖ ^ 2 ∂μ)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hb hlim)

theorem entropy_main_dissipation_cutoff_tendsto (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 μ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hwm : Measurable w)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    Tendsto (fun k : ℕ => ∫ x, cutoffSequence χ k x * w x * ‖v x‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ x, w x * ‖v x‖ ^ 2 ∂μ)) := by
  have hsq : Integrable (fun x => ‖v x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  apply tendsto_integral_of_dominated_convergence (fun x => ‖v x‖ ^ 2)
  · intro k
    exact (((cutoffSequence χ k).continuous.measurable.mul hwm).aestronglyMeasurable.mul
      (hv.aestronglyMeasurable.norm.pow 2))
  · exact hsq
  · intro k
    exact Filter.Eventually.of_forall fun x => by
      have hc := hχ (((k : ℝ) + 1)⁻¹ • x)
      have hχk : 0 ≤ cutoffSequence χ k x ∧ cutoffSequence χ k x ≤ 1 := hc
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (mul_nonneg hχk.1 (hw x).1) (sq_nonneg _))]
      have hm : cutoffSequence χ k x * w x ≤ 1 :=
        (mul_le_mul hχk.2 (hw x).2 (hw x).1 (by norm_num)).trans_eq (one_mul _)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (sq_nonneg ‖v x‖)
  · exact Filter.Eventually.of_forall fun x => by
      have hx : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹ • x) atTop (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
        simpa only [zero_smul] using tendsto_inverse_succ.smul_const x
      have hc : Tendsto (fun k : ℕ => cutoffSequence χ k x) atTop (𝓝 (1 : ℝ)) := by
        simpa only [Function.comp_def, cutoffSequence_apply, hχ0] using (χ.continuous.tendsto 0).comp hx
      simpa only [one_mul] using (hc.mul_const (w x)).mul_const (‖v x‖ ^ 2)

theorem entropy_main_dissipation_bound (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 μ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hwm : Measurable w)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    Integrable (fun x => φ x * w x * ‖v x‖ ^ 2) μ ∧
      ‖∫ x, φ x * w x * ‖v x‖ ^ 2 ∂μ‖ ≤ ∫ x, ‖v x‖ ^ 2 ∂μ := by
  have hsq : Integrable (fun x => ‖v x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  have hm : AEStronglyMeasurable (fun x => φ x * w x * ‖v x‖ ^ 2) μ :=
    ((φ.continuous.measurable.mul hwm).aestronglyMeasurable.mul (hv.aestronglyMeasurable.norm.pow 2))
  have hb (x) : ‖φ x * w x * ‖v x‖ ^ 2‖ ≤ ‖v x‖ ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hφ x).1 (hw x).1) (sq_nonneg _))]
    have hle : φ x * w x ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (hφ x).2 (hw x).2 (hw x).1 (by norm_num : (0:ℝ) ≤ 1)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hle (sq_nonneg ‖v x‖)
  exact ⟨hsq.mono' hm (Filter.Eventually.of_forall hb),
    norm_integral_le_of_norm_le hsq (Filter.Eventually.of_forall hb)⟩

theorem entropy_dissipation_cutoff_tendsto (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 μ)
    (g w : EuclideanSpace ℝ (Fin n) → ℝ) (hgm : Measurable g) (hwm : Measurable w)
    (B : ℝ) (hB : 0 ≤ B) (hgb : ∀ x, ‖g x‖ ≤ B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ0 : χ 0 = 1) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (M : ℝ) (hM : 0 ≤ M) (hgrad : ∀ x, ‖gradient χ x‖ ≤ M) :
    Tendsto (fun k : ℕ => ∫ x, g x * ⟪v x, gradient (cutoffSequence χ k) x⟫ +
      cutoffSequence χ k x * w x * ‖v x‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ x, w x * ‖v x‖ ^ 2 ∂μ)) := by
  have hiB (k : ℕ) := (entropy_boundary_flux_bound n μ v hv g hgm B hB hgb
    (cutoffSequence χ k) (M / ((k : ℝ) + 1)) (by positivity)
      (gradient_scaledTestFunction_bound ((k : ℝ) + 1) (by positivity) χ M hgrad)).1
  have hiM (k : ℕ) := (entropy_main_dissipation_bound n μ v hv w hwm hw (cutoffSequence χ k)
    (fun x => hχ (((k : ℝ) + 1)⁻¹ • x))).1
  simp_rw [integral_add (hiB _) (hiM _)]
  simpa only [zero_add] using
    (entropy_boundary_flux_cutoff_tendsto_zero n μ v hv g hgm B hB hgb χ M hM hgrad).add
      (entropy_main_dissipation_cutoff_tendsto n μ v hv w hwm hw χ hχ0 hχ)

theorem entropy_dissipation_cutoff_uniform_bound (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 μ)
    (g w : EuclideanSpace ℝ (Fin n) → ℝ) (hgm : Measurable g) (hwm : Measurable w)
    (B : ℝ) (hB : 0 ≤ B) (hgb : ∀ x, ‖g x‖ ≤ B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ 1)
    (χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (M : ℝ) (hM : 0 ≤ M) (hgrad : ∀ x, ‖gradient χ x‖ ≤ M)
    (I : ℝ) (hI : (∫ x, ‖v x‖ ^ 2 ∂μ) ≤ I) (k : ℕ) :
    ‖∫ x, g x * ⟪v x, gradient (cutoffSequence χ k) x⟫ +
      cutoffSequence χ k x * w x * ‖v x‖ ^ 2 ∂μ‖ ≤ B * M * (1 + I) + I := by
  have hcut (x) : ‖gradient (cutoffSequence χ k) x‖ ≤ M := by
    have hle : M / ((k : ℝ) + 1) ≤ M :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
        (by nlinarith [mul_nonneg hM (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))])
    exact (gradient_scaledTestFunction_bound ((k : ℝ) + 1) (by positivity) χ M hgrad x).trans hle
  have hBd := entropy_boundary_flux_bound n μ v hv g hgm B hB hgb (cutoffSequence χ k) M hM hcut
  have hMd := entropy_main_dissipation_bound n μ v hv w hwm hw (cutoffSequence χ k)
    (fun x => hχ (((k : ℝ) + 1)⁻¹ • x))
  rw [integral_add hBd.1 hMd.1]
  calc
    _ ≤ ‖∫ x, g x * ⟪v x, gradient (cutoffSequence χ k) x⟫ ∂μ‖ +
        ‖∫ x, cutoffSequence χ k x * w x * ‖v x‖ ^ 2 ∂μ‖ := norm_add_le _ _
    _ ≤ B * M * (1 + ∫ x, ‖v x‖ ^ 2 ∂μ) + (∫ x, ‖v x‖ ^ 2 ∂μ) := add_le_add hBd.2 hMd.2
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hI) (mul_nonneg hB hM)) hI

end AffineFKProof
