module

public import AffineFK.DirichletLinearTransport
public import AffineFK.DensityApproximationL1Translation
public import Mathlib.Topology.Algebra.Group.ContinuousDiv

/-! # Genuine compact-test and L2 translation for the Dirichlet domain -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Set Filter
open scoped Distributions RealInnerProductSpace Topology

def dirichletTranslatedOpen (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨(fun x => x-z) ⁻¹' (U : Set _),U.isOpen.preimage (by fun_prop)⟩

theorem dirichletTranslatedOpen_coe (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) :
    (dirichletTranslatedOpen n U z : Set (EuclideanSpace ℝ (Fin n))) =
      (fun x => x+z) '' (U : Set _) := by
  ext x
  change x-z ∈ (U : Set _) ↔ x ∈ (fun y => y+z) '' (U : Set _)
  constructor
  · intro hx
    exact ⟨x-z,hx,sub_add_cancel x z⟩
  · rintro ⟨y,hy,rfl⟩
    simpa only [add_sub_cancel_right] using hy

theorem dirichletTranslatedOpen_inverse (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) :
    dirichletTranslatedOpen n (dirichletTranslatedOpen n U z) (-z) = U := by
  ext x
  change (x-(-z))-z ∈ (U : Set _) ↔ x ∈ (U : Set _)
  simp only [sub_neg_eq_add,add_sub_cancel_right]

def dirichletTranslateLp (n : ℕ) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (z : EuclideanSpace ℝ (Fin n)) :
    Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗᵢ[ℝ]
      Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  Lp.compMeasurePreservingₗᵢ ℝ (densityApproximationTranslation n z)
    (densityApproximationTranslation_measurePreserving n z)

theorem dirichletTranslateLp_coe (n : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (z : EuclideanSpace ℝ (Fin n))
    (f : Lp F 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (dirichletTranslateLp n F z f : EuclideanSpace ℝ (Fin n) → F) =ᵐ[volume] fun x => f (x-z) := by
  unfold dirichletTranslateLp
  change (Lp.compMeasurePreserving (densityApproximationTranslation n z)
    (densityApproximationTranslation_measurePreserving n z) f : EuclideanSpace ℝ (Fin n) → F)
      =ᵐ[volume] fun x => f (x-z)
  simpa only [densityApproximationTranslation,ContinuousMap.coe_mk,
    Function.comp_def] using Lp.coeFn_compMeasurePreserving f
      (densityApproximationTranslation_measurePreserving n z)

def dirichletTranslationTest (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) (φ : 𝓓(U,ℝ)) :
    𝓓(dirichletTranslatedOpen n U z,ℝ) :=
  ⟨fun x => φ (x-z),φ.contDiff.comp (contDiff_id.sub contDiff_const),
    φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight z),
    (tsupport_comp_subset_preimage φ (by fun_prop : Continuous (fun x => x-z))).trans
      (preimage_mono φ.tsupport_subset)⟩

theorem dirichletTranslationTest_gradient (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (z x : EuclideanSpace ℝ (Fin n)) (φ : 𝓓(U,ℝ)) :
    gradient (fun y => φ (y-z)) x = gradient φ (x-z) := by
  have hs : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => y-z)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x :=
    (hasFDerivAt_id x).sub_const z
  have hc := ((φ.contDiff.differentiable (by simp)).differentiableAt
    (x := x-z)).hasFDerivAt.comp x hs
  apply (toDual ℝ (EuclideanSpace ℝ (Fin n))).injective
  simpa only [toDual_gradient,ContinuousLinearMap.comp_id,Function.comp_def] using hc.fderiv

theorem dirichletTranslationTest_value_Lp (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) (φ : 𝓓(U,ℝ)) :
    unweightedTestToL2 n (dirichletTestToTop n _ (dirichletTranslationTest n U z φ)) =
      dirichletTranslateLp n ℝ z (unweightedTestToL2 n (dirichletTestToTop n U φ)) := by
  apply Lp.ext
  have hs := (densityApproximationTranslation_measurePreserving n z).quasiMeasurePreserving.ae_eq_comp
    (unweightedTestToL2_coe n (dirichletTestToTop n U φ))
  filter_upwards [unweightedTestToL2_coe n (dirichletTestToTop n _ (dirichletTranslationTest n U z φ)),
    dirichletTranslateLp_coe n z (unweightedTestToL2 n (dirichletTestToTop n U φ)),hs] with x hv ht hsx
  rw [hv,ht]
  exact hsx.symm

theorem dirichletTranslationTest_gradient_Lp (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) (φ : 𝓓(U,ℝ)) :
    unweightedTestToL2 n (testFunctionGradient (dirichletTestToTop n _ (dirichletTranslationTest n U z φ))) =
      dirichletTranslateLp n (EuclideanSpace ℝ (Fin n)) z
        (unweightedTestToL2 n (testFunctionGradient (dirichletTestToTop n U φ))) := by
  apply Lp.ext
  have hs := (densityApproximationTranslation_measurePreserving n z).quasiMeasurePreserving.ae_eq_comp
    (unweightedTestToL2_coe n (testFunctionGradient (dirichletTestToTop n U φ)))
  filter_upwards [unweightedTestToL2_coe n (testFunctionGradient
      (dirichletTestToTop n _ (dirichletTranslationTest n U z φ))),
    dirichletTranslateLp_coe n z (unweightedTestToL2 n (testFunctionGradient (dirichletTestToTop n U φ))),hs]
      with x hv ht hsx
  rw [hv,ht]
  change unweightedTestToL2 n (testFunctionGradient (dirichletTestToTop n U φ)) (x-z) =
    testFunctionGradient (dirichletTestToTop n U φ) (x-z) at hsx
  rw [hsx,testFunctionGradient_apply,testFunctionGradient_apply]
  change gradient (fun y => φ (y-z)) x = gradient φ (x-z)
  exact dirichletTranslationTest_gradient n U z x φ

end AffineFKProof
