module

public import AffineFK.H1DirectionalTranslationTests

/-!
# The exact directional estimate for the genuine completed H1 graph

All translations act on actual Lebesgue L2 equivalence classes. Both sides
are continuous on the genuine value-gradient completion, so density of
compact smooth tests extends the directional estimate without a dimension
factor or an assumed distributional derivative.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory InnerProductSpace TopologicalSpace Filter
open scoped RealInnerProductSpace Distributions Topology

def l2DirectionalPairing (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (toDual ℝ (EuclideanSpace ℝ (Fin n)) z).compLpL 2 volume

theorem l2DirectionalPairing_coe (n : ℕ) (z : EuclideanSpace ℝ (Fin n))
    (g : Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    l2DirectionalPairing n z g =ᵐ[volume] fun x => ⟪z, g x⟫ := by
  exact (toDual ℝ (EuclideanSpace ℝ (Fin n)) z).coeFn_compLp g

theorem test_directional_translation_norm_sq_le (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖bridgeL2Translate n z (unweightedTestToL2 n φ) - unweightedTestToL2 n φ‖^2 ≤
      ‖l2DirectionalPairing n z (unweightedTestToL2 n (testFunctionGradient φ))‖^2 := by
  let f := unweightedTestToL2 n φ
  let g := unweightedTestToL2 n (testFunctionGradient φ)
  have hf : (f : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] φ :=
    unweightedTestToL2_coe n φ
  have htrans : bridgeL2Translate n z f =ᵐ[volume] fun x => φ (x+z) := by
    exact (bridgeL2Translate_coe n z f).trans
      ((measurePreserving_add_right volume z).quasiMeasurePreserving.ae_eq_comp hf)
  calc
    _ = ∫ x, (φ (x+z) - φ x)^2 := by
      rw [l2_norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (bridgeL2Translate n z f) f, htrans, hf] with x hs ht hv
      rw [hs]
      simp only [Pi.sub_apply]
      rw [ht, hv, Real.norm_eq_abs, sq_abs]
    _ ≤ ∫ x, (⟪z, gradient φ x⟫)^2 := test_directional_translation_integral_sq_le n φ z
    _ = _ := by
      rw [l2_norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [l2DirectionalPairing_coe n z g,
        unweightedTestToL2_coe n (testFunctionGradient φ)] with x hp hg
      rw [hp, hg, testFunctionGradient_apply, Real.norm_eq_abs, sq_abs]

theorem h1_directional_translation_norm_sq_le (n : ℕ)
    (v : unweightedSobolevGraph n) (z : EuclideanSpace ℝ (Fin n)) :
    ‖bridgeL2Translate n z (unweightedValue n v) - unweightedValue n v‖^2 ≤
      ‖l2DirectionalPairing n z (unweightedGradient n v)‖^2 := by
  obtain ⟨φ, hval, hgrad⟩ := unweighted_approximating_tests n v
  have hleft := (((bridgeL2Translate n z).continuous.tendsto _).comp hval).sub hval
  have hright := ((l2DirectionalPairing n z).continuous.tendsto _).comp hgrad
  exact le_of_tendsto_of_tendsto (hleft.norm.pow 2) (hright.norm.pow 2)
    (Eventually.of_forall fun k => test_directional_translation_norm_sq_le n (φ k) z)

end AffineFKProof
