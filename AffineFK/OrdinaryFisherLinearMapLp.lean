module

public import AffineFK.OrdinaryFisherLinearMap
public import AffineFK.OrdinaryFisherLinearMapDensity
public import AffineFK.UnweightedSobolevGraph

/-!
# Continuous L2 pullback by an invertible linear map

The determinant change of variables bounds the changed measure by a
finite scalar multiple of volume. Mathlib's actual Lp measure-comparison
map followed by its measure-preserving pullback therefore gives a
continuous linear pullback on L2(volume). The representative equality is
proved almost everywhere; no unproved representative identity is used.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

theorem ordinaryFisherLinearMap_quasiMeasurePreserving (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Measure.QuasiMeasurePreserving A
      (volume : Measure (EuclideanSpace ℝ (Fin n))) volume := by
  refine ⟨A.continuous.measurable, ?_⟩
  rw [ordinaryFisherLinearMap_volume]
  exact Measure.smul_absolutelyContinuous

def ordinaryFisherLinearPullbackLp (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (Lp.compMeasurePreservingₗᵢ ℝ A.symm
    (A.symm.continuous.measurable.measurePreserving
      (volume : Measure (EuclideanSpace ℝ (Fin n))))).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (ordinaryFisherLinearMap_volume n A.symm).le)

theorem ordinaryFisherLinearPullbackLp_coe (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ordinaryFisherLinearPullbackLp n A F f =ᵐ[volume] fun z => f (A.symm z) := by
  have hA := A.symm.continuous.measurable.measurePreserving
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
  have hD := Lp.coeFn_LpToLpOfMeasureLeSMul (E := F) (p := 2)
    ENNReal.ofReal_ne_top (ordinaryFisherLinearMap_volume n A.symm).le f
  exact (Lp.coeFn_compMeasurePreserving _ hA).trans
    (hA.quasiMeasurePreserving.ae_eq_comp hD)

theorem ordinaryFisherLinearTest_gradient (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (ordinaryFisherLinearTest n A φ) x =
      A.toContinuousLinearMap.adjoint (gradient φ (A x)) := by
  apply ext_inner_right ℝ
  intro h
  rw [ordinaryFisherLinearTest_gradient_pairing, ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem ordinaryFisherLinearPullbackLp_test (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    ordinaryFisherLinearPullbackLp n A ℝ (unweightedTestToL2 n φ) =
      unweightedTestToL2 n (ordinaryFisherLinearTest n A.symm φ) := by
  apply Lp.ext
  have hA := ordinaryFisherLinearMap_quasiMeasurePreserving n A.symm
  filter_upwards [ordinaryFisherLinearPullbackLp_coe n A (unweightedTestToL2 n φ),
    hA.ae_eq_comp (unweightedTestToL2_coe n φ),
    unweightedTestToL2_coe n (ordinaryFisherLinearTest n A.symm φ)] with z hp hf ht
  change unweightedTestToL2 n φ (A.symm z) = φ (A.symm z) at hf
  rw [hp, hf, ht]
  rfl

theorem ordinaryFisherLinearPullbackLp_gradient_test (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    A.symm.toContinuousLinearMap.adjoint.compLp
      (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n))
        (unweightedTestToL2 n (testFunctionGradient φ))) =
      unweightedTestToL2 n (testFunctionGradient (ordinaryFisherLinearTest n A.symm φ)) := by
  apply Lp.ext
  have hA := ordinaryFisherLinearMap_quasiMeasurePreserving n A.symm
  filter_upwards [A.symm.toContinuousLinearMap.adjoint.coeFn_compLp'
      (ordinaryFisherLinearPullbackLp n A (EuclideanSpace ℝ (Fin n))
        (unweightedTestToL2 n (testFunctionGradient φ))),
    ordinaryFisherLinearPullbackLp_coe n A (unweightedTestToL2 n (testFunctionGradient φ)),
    hA.ae_eq_comp (unweightedTestToL2_coe n (testFunctionGradient φ)),
    unweightedTestToL2_coe n (testFunctionGradient (ordinaryFisherLinearTest n A.symm φ))]
      with z hc hp hf ht
  change unweightedTestToL2 n (testFunctionGradient φ) (A.symm z) =
    testFunctionGradient φ (A.symm z) at hf
  rw [hc, hp, hf, ht, testFunctionGradient_apply, testFunctionGradient_apply,
    ordinaryFisherLinearTest_gradient]

end AffineFKProof
