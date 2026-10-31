module

public import AffineFK.DirichletSupportL2Dilation
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Strong L2 convergence of actual normalized inward dilations

The compact-support dominated-convergence argument and exact isometry
extend the limit to every genuine Lebesgue L2 class. The density theorem
is Mathlib's `Lp.dense_hasCompactSupport_contDiff` (Moritz Doll, Apache 2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter Set Metric
open scoped Distributions RealInnerProductSpace Topology ContDiff

theorem supportDilation_dense_isometry_limit
    {V : Type*} [NormedAddCommGroup V] (S : Set V) (hS : Dense S)
    (T : ℕ → V → V) (hT : ∀ k f g, ‖T k f - T k g‖ ≤ ‖f - g‖)
    (hlim : ∀ g ∈ S, Tendsto (fun k => T k g) atTop (𝓝 g)) (f : V) :
    Tendsto (fun k => T k f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := hS.exists_dist_lt f (by linarith : 0 < ε / 3)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hlim g hg) (ε / 3) (by linarith)
  refine ⟨N, fun k hk => ?_⟩
  have hkg := hN k hk
  have htri := norm_add_le (T k f - T k g) (T k g - g)
  have htri' := norm_add_le (T k f - g) (g - f)
  have hid : T k f - T k g + (T k g - g) = T k f - g := by abel
  have hid' : T k f - g + (g - f) = T k f - f := by abel
  rw [hid] at htri
  rw [hid'] at htri'
  rw [dist_eq_norm] at hfg hkg ⊢
  have hgf : ‖g - f‖ = ‖f - g‖ := norm_sub_rev _ _
  have hb := hT k f g
  linarith

set_option maxHeartbeats 1000000 in
theorem supportDilationL2_test_tendsto (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ k, (1 / 2 : ℝ) ≤ a k) (haone : ∀ k, a k ≤ 1)
    (hlim : Tendsto a atTop (𝓝 1))
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hfg : f =ᵐ[volume] g)
    (hg : HasCompactSupport g) (hgc : Continuous g) :
    Tendsto (fun k => supportDilationL2 n (a k) (by have := ha k; linarith) f)
      atTop (𝓝 f) := by
  have ha0 (k) : 0 < a k := by have := ha k; linarith
  let c : ℕ → ℝ := fun k => Real.sqrt (ordinaryFisherLinearJacobian n
    (supportDilationLinearEquiv n (a k) (ha0 k).ne'))
  have hc : Tendsto c atTop (𝓝 1) := supportDilation_sqrt_jacobian_tendsto n a ha0 hlim
  obtain ⟨R, hR, hsupp⟩ := hg.isCompact.isBounded.subset_closedBall_lt 0 0
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hg
  let C : ℝ := ((Real.sqrt ((2 : ℝ)^n) + 1) * max M 0)^2
  let B : EuclideanSpace ℝ (Fin n) → ℝ :=
    (closedBall 0 R).indicator (fun _ => C)
  have hB : Integrable B (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).measure_ne_top)
  refine poincareSmoothExtension_L2_tendsto volume _ f
    (fun k x => c k * g ((a k)⁻¹ • x)) g ?_ hfg B hB ?_ ?_
  · intro k
    have hA := ordinaryFisherLinearMap_quasiMeasurePreserving n
      (supportDilationLinearEquiv n (a k) (ha0 k).ne').symm
    filter_upwards [supportDilationL2_coe n (a k) (ha0 k).ne' f,
      hA.ae_eq_comp hfg] with x hx hgx
    change f ((a k)⁻¹ • x) = g ((a k)⁻¹ • x) at hgx
    rw [hx, hgx]
  · intro k
    exact Eventually.of_forall fun x => by
      have hm (y) : ‖g y‖ ≤ max M 0 := (hM y).trans (le_max_left _ _)
      by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) R
      · change _ ≤ (closedBall 0 R).indicator (fun _ => C) x
        rw [indicator_of_mem hx]
        have htri := norm_sub_le (c k * g ((a k)⁻¹ • x)) (g x)
        have hcb : ‖c k‖ ≤ Real.sqrt ((2 : ℝ)^n) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact supportDilation_sqrt_jacobian_bound n (a k) (ha k)
        have hprod : ‖c k * g ((a k)⁻¹ • x)‖ ≤ Real.sqrt ((2 : ℝ)^n) * max M 0 := by
          rw [norm_mul]
          exact mul_le_mul hcb (hm _) (norm_nonneg _) (Real.sqrt_nonneg _)
        have hlin : ‖c k * g ((a k)⁻¹ • x) - g x‖ ≤
            (Real.sqrt ((2 : ℝ)^n) + 1) * max M 0 := by nlinarith [hm x]
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hlin
      · change _ ≤ (closedBall 0 R).indicator (fun _ => C) x
        rw [indicator_of_notMem hx]
        have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
        have hgy : g ((a k)⁻¹ • x) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hy
          have hyR := hsupp hy
          rw [mem_closedBall_zero_iff] at hyR
          apply hx
          rw [mem_closedBall_zero_iff]
          have heq : x = a k • ((a k)⁻¹ • x) := by simp [smul_smul, (ha0 k).ne']
          calc
            ‖x‖ = ‖a k‖ * ‖(a k)⁻¹ • x‖ := by conv_lhs => rw [heq]; rw [norm_smul]
            _ ≤ 1 * R := mul_le_mul (by simpa [Real.norm_eq_abs, abs_of_pos (ha0 k)] using haone k)
              hyR (norm_nonneg _) zero_le_one
            _ = R := one_mul R
        simp only [hgx, hgy, mul_zero, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), le_refl]
  · exact Eventually.of_forall fun x => by
      have hax : Tendsto (fun k => (a k)⁻¹ • x) atTop (𝓝 x) := by
        simpa only [inv_one, one_smul] using (hlim.inv₀ (by norm_num)).smul_const x
      simpa only [one_mul, Function.comp_def] using hc.mul ((hgc.tendsto x).comp hax)

theorem supportDilationL2_tendsto (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ k, (1 / 2 : ℝ) ≤ a k) (haone : ∀ k, a k ≤ 1)
    (hlim : Tendsto a atTop (𝓝 1))
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Tendsto (fun k => supportDilationL2 n (a k) (by have := ha k; linarith) f)
      atTop (𝓝 f) := by
  apply supportDilation_dense_isometry_limit
    {f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) |
      ∃ g, f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g}
    (MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num))
    (fun k => supportDilationL2 n (a k) (by have := ha k; linarith))
    (fun k f g => (supportDilationL2_norm_sub n _ _ f g).le) _ f
  rintro g ⟨g', hgg', hcompact, hsmooth⟩
  exact supportDilationL2_test_tendsto n a ha haone hlim g g' hgg' hcompact hsmooth.continuous

end AffineFKProof
