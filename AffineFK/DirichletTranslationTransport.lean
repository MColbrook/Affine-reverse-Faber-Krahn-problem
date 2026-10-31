module

public import AffineFK.DirichletTranslationTests

/-!
# Translation preserves the actual H0 domain and Dirichlet eigenvalue

Compact tests are translated inside the translated open set. Their value
and gradient have actual measure-preserving L2 limits. The two closed
compact-test graph domains provide the transported H0 element. Thus the
Rayleigh quotient and its extended infimum are preserved, including
empty domains, without any eigenfunction or boundary regularity premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem dirichlet_translation_graph_transport (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n))
    (v : dirichletSobolev n U) :
    ∃ w : dirichletSobolev n (dirichletTranslatedOpen n U z),
      dirichletValue n _ w = dirichletTranslateLp n ℝ z (dirichletValue n U v) ∧
      dirichletGradient n _ w = dirichletTranslateLp n (EuclideanSpace ℝ (Fin n)) z (dirichletGradient n U v) := by
  let V := dirichletTranslatedOpen n U z
  obtain ⟨φ,hφ⟩ := dirichlet_approximating_tests n U v
  let ψ : ℕ → 𝓓(V,ℝ) := fun k => dirichletTranslationTest n U z (φ k)
  let Lv := (dirichletTranslateLp n ℝ z).toContinuousLinearMap
  let Lg := (dirichletTranslateLp n (EuclideanSpace ℝ (Fin n)) z).toContinuousLinearMap
  have hvLim : Tendsto (fun k => unweightedTestToL2 n (dirichletTestToTop n V (ψ k))) atTop
      (𝓝 (Lv (dirichletValue n U v))) := by
    have hlim := (Lv.continuous.tendsto _).comp
      (((unweightedValue n).continuous.tendsto v.val).comp hφ)
    exact hlim.congr' (Eventually.of_forall fun k =>
      (dirichletTranslationTest_value_Lp n U z (φ k)).symm)
  have hgLim : Tendsto (fun k => unweightedTestToL2 n
      (testFunctionGradient (dirichletTestToTop n V (ψ k)))) atTop
      (𝓝 (Lg (dirichletGradient n U v))) := by
    have hlim := (Lg.continuous.tendsto _).comp
      (((unweightedGradient n).continuous.tendsto v.val).comp hφ)
    exact hlim.congr' (Eventually.of_forall fun k =>
      (dirichletTranslationTest_gradient_Lp n U z (φ k)).symm)
  let q : SobolevAmbient (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ
      (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))).symm
        (Lv (dirichletValue n U v),Lg (dirichletGradient n U v))
  have hpair : Tendsto (fun k => unweightedSmoothPair n (dirichletTestToTop n V (ψ k)))
      atTop (𝓝 q) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ
      (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))).symm.continuous.tendsto _).comp
        (hvLim.prodMk_nhds hgLim)
  have hq : q ∈ unweightedSobolevGraph n :=
    (unweightedSobolevGraph_isClosed n).mem_of_tendsto hpair
      (Eventually.of_forall fun k => unweighted_smooth_pair_mem n _)
  let w : unweightedSobolevGraph n := ⟨q,hq⟩
  have hH1 : Tendsto (fun k => dirichletTestToH1 n V (ψ k)) atTop (𝓝 w) :=
    tendsto_subtype_rng.mpr hpair
  have hw : w ∈ dirichletSobolev n V :=
    (dirichletSobolev_isClosed n V).mem_of_tendsto hH1
      (Eventually.of_forall fun k => dirichlet_test_mem n V (ψ k))
  exact ⟨⟨w,hw⟩,rfl,rfl⟩

set_option maxHeartbeats 1000000 in
theorem dirichlet_translation_graph_energy (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n))
    (v : dirichletSobolev n U) :
    ∃ w : dirichletSobolev n (dirichletTranslatedOpen n U z),
      ‖dirichletValue n _ w‖^2 = ‖dirichletValue n U v‖^2 ∧
      ‖dirichletGradient n _ w‖^2 = ‖dirichletGradient n U v‖^2 := by
  obtain ⟨w,hv,hg⟩ := dirichlet_translation_graph_transport n U z v
  refine ⟨w,?_,?_⟩
  · rw [hv,(dirichletTranslateLp n ℝ z).norm_map]
  · rw [hg,(dirichletTranslateLp n (EuclideanSpace ℝ (Fin n)) z).norm_map]

theorem dirichlet_translation_rayleigh_transport (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n))
    (v : dirichletSobolev n U) (hv : dirichletValue n U v ≠ 0) :
    ∃ w : dirichletSobolev n (dirichletTranslatedOpen n U z),
      dirichletValue n _ w ≠ 0 ∧
      dirichletRayleigh n _ w = dirichletRayleigh n U v := by
  obtain ⟨w,hwv,hwg⟩ := dirichlet_translation_graph_energy n U z v
  refine ⟨w,?_,?_⟩
  · intro hw
    have hz : ‖dirichletValue n U v‖^2=0 := by
      rw [← hwv,hw,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
    exact hv (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · simp only [dirichletRayleigh,hwv,hwg]

theorem dirichletEigenvalue_translated_le (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    dirichletEigenvalue n (dirichletTranslatedOpen n U z) ≤ dirichletEigenvalue n U := by
  unfold dirichletEigenvalue
  apply le_iInf
  intro v
  apply le_iInf
  intro hv
  obtain ⟨w,hw,hR⟩ := dirichlet_translation_rayleigh_transport n U z v hv
  calc
    _ ≤ ENNReal.ofReal (dirichletRayleigh n _ w) := iInf_le_of_le w (iInf_le _ hw)
    _ = _ := congrArg ENNReal.ofReal hR

theorem dirichletEigenvalue_translated (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    dirichletEigenvalue n (dirichletTranslatedOpen n U z) = dirichletEigenvalue n U := by
  apply le_antisymm (dirichletEigenvalue_translated_le n U z)
  have h := dirichletEigenvalue_translated_le n (dirichletTranslatedOpen n U z) (-z)
  simpa only [dirichletTranslatedOpen_inverse] using h

end AffineFKProof
