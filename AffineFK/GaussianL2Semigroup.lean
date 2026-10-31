module

public import AffineFK.GaussianL2HeatIdentification
public import AffineFK.GaussianVarianceRotation
public import AffineFK.GaussianPositionRestriction
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Self-adjointness and genuine half-time composition of Gaussian heat

Actual translation isometries and the genuine product-Gaussian rotation
law prove these identities in the Hilbert space L2. Every Hilbert-valued
double integral is integrable before Fubini is applied.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology RealInnerProductSpace

theorem gaussianL2Translate_add (n : ℕ) (y z : EuclideanSpace ℝ (Fin n))
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    bridgeL2Translate n y (bridgeL2Translate n z f) = bridgeL2Translate n (y+z) f := by
  apply Lp.ext
  have hs := (measurePreserving_add_right
    (volume : Measure (EuclideanSpace ℝ (Fin n))) y).quasiMeasurePreserving.ae_eq_comp
      (bridgeL2Translate_coe n z f)
  filter_upwards [bridgeL2Translate_coe n y (bridgeL2Translate n z f), hs,
    bridgeL2Translate_coe n (y+z) f] with x hy hz hyz
  change bridgeL2Translate n z f (x+y) = f (x+y+z) at hz
  rw [hy, hz, hyz, add_assoc]

theorem gaussianL2Translate_inner (n : ℕ) (y : EuclideanSpace ℝ (Fin n))
    (f g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ⟪bridgeL2Translate n y f,g⟫ = ⟪f,bridgeL2Translate n (-y) g⟫ := by
  have he := (bridgeL2Translate n y).inner_map_map f (bridgeL2Translate n (-y) g)
  rw [gaussianL2Translate_add, add_neg_cancel, bridgeL2Translate_zero] at he
  exact he

theorem gaussianL2Average_inner (n : ℕ) (b : ℝ)
    (f g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ⟪bridgeGaussianL2Average n b f,g⟫ = ⟪f,bridgeGaussianL2Average n b g⟫ := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  letI : Measure.IsNegInvariant γ := gaussianPosition_standardGaussian_even n
  calc
    _ = ∫ u, ⟪bridgeL2Translate n (b•u) f,g⟫ ∂γ := by
      simpa only [real_inner_comm, bridgeGaussianL2Average, γ] using
        (integral_inner (bridgeGaussianL2Average_integrable n b f) g).symm
    _ = ∫ u, ⟪f,bridgeL2Translate n (b•(-u)) g⟫ ∂γ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        change ⟪bridgeL2Translate n (b•u) f,g⟫ = ⟪f,bridgeL2Translate n (b•(-u)) g⟫
        rw [gaussianL2Translate_inner, smul_neg]
    _ = ∫ u, ⟪f,bridgeL2Translate n (b•u) g⟫ ∂γ :=
      integral_neg_eq_self (fun u : EuclideanSpace ℝ (Fin n) =>
        inner ℝ f (bridgeL2Translate n (b•u) g)) γ
    _ = _ := integral_inner (bridgeGaussianL2Average_integrable n b g) f

theorem gaussianFreeHeatL2_selfAdjoint (n : ℕ) (h : ℝ) (hh : 0 < h) :
    IsSelfAdjoint (bridgeFreeHeatL2 n h hh) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change ⟪bridgeFreeHeatL2 n h hh f,g⟫ = ⟪f,bridgeFreeHeatL2 n h hh g⟫
  rw [← gaussianL2Average_eq_heat n h hh f, ← gaussianL2Average_eq_heat n h hh g]
  exact gaussianL2Average_inner n (Real.sqrt h) f g

theorem gaussianL2Average_twice (n : ℕ) (b : ℝ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    bridgeGaussianL2Average n b (bridgeGaussianL2Average n b f) =
      bridgeGaussianL2Average n (Real.sqrt 2*b) f := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ := stdGaussian E
  let c : ℝ := (Real.sqrt 2)⁻¹
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hcc : c^2+c^2=1 := by dsimp [c]; field_simp; nlinarith
  let W : E × E → E := fun p => c•p.1+c•p.2
  have hW : HasLaw W γ (γ.prod γ) := ⟨by fun_prop, gaussianVariance_mix_law n c c hcc⟩
  let F : E × E → Lp ℝ 2 (volume : Measure E) :=
    fun p => bridgeL2Translate n (b•p.1+b•p.2) f
  have hF : Integrable F (γ.prod γ) := by
    apply (integrable_const ‖f‖).mono'
      ((bridgeL2Translate_continuous n f).comp (by fun_prop)).aestronglyMeasurable
    exact Eventually.of_forall fun p => (bridgeL2Translate_norm n _ f).le
  calc
    _ = ∫ u, ∫ v, F (u,v) ∂γ ∂γ := by
      unfold bridgeGaussianL2Average
      apply integral_congr_ae
      apply Eventually.of_forall
      intro u
      change bridgeL2Translate n (b•u) (∫ v, bridgeL2Translate n (b•v) f ∂γ) =
        ∫ v, F (u,v) ∂γ
      rw [← (bridgeL2Translate n (b•u)).integral_comp_comm]
      apply integral_congr_ae
      exact Eventually.of_forall fun v => gaussianL2Translate_add n (b•u) (b•v) f
    _ = ∫ p, F p ∂γ.prod γ := (integral_prod _ hF).symm
    _ = ∫ p, bridgeL2Translate n ((Real.sqrt 2*b)•W p) f ∂γ.prod γ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        have hc : (Real.sqrt 2*b)*c=b := by dsimp [c]; field_simp
        simp only [F, W, smul_add, smul_smul, hc]
    _ = _ := hW.integral_comp
      (((bridgeL2Translate_continuous n f).comp (by fun_prop)).aestronglyMeasurable)

theorem gaussianFreeHeatL2_half_semigroup (n : ℕ) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    bridgeFreeHeatL2 n (h/2) (by positivity)
      (bridgeFreeHeatL2 n (h/2) (by positivity) f) = bridgeFreeHeatL2 n h hh f := by
  rw [← gaussianL2Average_eq_heat, ← gaussianL2Average_eq_heat, gaussianL2Average_twice]
  have hs : Real.sqrt 2 * Real.sqrt (h/2) = Real.sqrt h := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hs, gaussianL2Average_eq_heat n h hh]

theorem gaussianFreeHeatL2_quadratic_nonneg (n : ℕ) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    0 ≤ ⟪bridgeFreeHeatL2 n h hh f,f⟫ := by
  rw [← gaussianFreeHeatL2_half_semigroup n h hh f]
  have he := (gaussianFreeHeatL2_selfAdjoint n (h/2) (by positivity)).isSymmetric
    (bridgeFreeHeatL2 n (h/2) (by positivity) f) f
  change ⟪bridgeFreeHeatL2 n (h/2) _ (bridgeFreeHeatL2 n (h/2) _ f),f⟫ = _ at he
  rw [he]
  exact real_inner_self_nonneg

end AffineFKProof
