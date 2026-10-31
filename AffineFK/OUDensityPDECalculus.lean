module

public import AffineFK.GaussianSecondDensityRatioCalculus
public import AffineFK.OUDensityTimeWeakEquation

/-!
# The genuine spatial Fokker--Planck operator and compact duality

The operator is the divergence of the actual density gradient plus x*rho.
Two Haar integrations by parts identify its compact-test adjoint with the
proved OU test generator. The density need only be smooth for this
spatial identity; no desired time equation is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

def ouDensitySpatialOperator (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n,
    (fderiv ℝ (fun y => fderiv ℝ ρ y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) +
    fderiv ℝ (fun y => y i * ρ y) x (EuclideanSpace.basisFun (Fin n) ℝ i))

theorem ouDensitySpatialOperator_continuous (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ) :
    Continuous (ouDensitySpatialOperator n ρ) := by
  apply continuous_finsetSum
  intro i _
  have hdi : ContDiff ℝ ∞ (fun x => fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    (hρ.fderiv_right (by simp)).clm_apply contDiff_const
  have hprod : ContDiff ℝ ∞ (fun x => x i * ρ x) := by
    simpa only [Pi.mul_apply, coordinateFunctional_apply] using (coordinateFunctional n i).contDiff.mul hρ
  exact ((hdi.continuous_fderiv (by simp)).clm_apply continuous_const).add
    ((hprod.continuous_fderiv (by simp)).clm_apply continuous_const)

theorem smooth_second_partial_test_integration_by_parts (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (i j : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ ρ y
      (EuclideanSpace.basisFun (Fin n) ℝ i)) x (EuclideanSpace.basisFun (Fin n) ℝ j) * φ x) ∧
    Integrable (fun x => ρ x * partialTest n i (partialTest n j φ) x) ∧
    (∫ x, fderiv ℝ (fun y => fderiv ℝ ρ y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
      (EuclideanSpace.basisFun (Fin n) ℝ j) * φ x) =
        ∫ x, ρ x * partialTest n i (partialTest n j φ) x := by
  have hi : ContDiff ℝ ∞ (fun x => fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    (hρ.fderiv_right (by simp)).clm_apply contDiff_const
  have h1 := smooth_partial_test_integration_by_parts n _ hi j φ
  have h2 := smooth_partial_test_integration_by_parts n ρ hρ i (partialTest n j φ)
  exact ⟨h1.1, h2.2.1, by linarith [h1.2.2, h2.2.2]⟩

theorem ouDensitySpatialOperator_test_duality (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x => φ x * ouDensitySpatialOperator n ρ x) ∧
    Integrable (fun x => ouTestGenerator n φ x * ρ x) ∧
    (∫ x, φ x * ouDensitySpatialOperator n ρ x) = ∫ x, ouTestGenerator n φ x * ρ x := by
  let D (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :=
    fderiv ℝ (fun y => fderiv ℝ ρ y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
      (EuclideanSpace.basisFun (Fin n) ℝ i)
  let B (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :=
    fderiv ℝ (fun y => y i * ρ y) x (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hprod (i : Fin n) : ContDiff ℝ ∞ (fun x => x i * ρ x) := by
    simpa only [Pi.mul_apply, coordinateFunctional_apply] using (coordinateFunctional n i).contDiff.mul hρ
  have hD (i : Fin n) := smooth_second_partial_test_integration_by_parts n ρ hρ i i φ
  have hB (i : Fin n) := smooth_partial_test_integration_by_parts n _ (hprod i) i φ
  have hL (i : Fin n) : Integrable (fun x => φ x * (D i x + B i x)) := by
    have h := (hD i).1.add (hB i).1
    apply h.congr
    exact Filter.Eventually.of_forall fun x => by
      change D i x * φ x + B i x * φ x = φ x * (D i x + B i x)
      ring
  have hR (i : Fin n) : Integrable (fun x =>
      (partialTest n i (partialTest n i φ) x - x i * partialTest n i φ x) * ρ x) := by
    have h := (hD i).2.1.sub (hB i).2.1
    apply h.congr
    exact Filter.Eventually.of_forall fun x => by
      change ρ x * partialTest n i (partialTest n i φ) x - (x i * ρ x) * partialTest n i φ x = _
      ring
  have hrow (i : Fin n) : (∫ x, φ x * (D i x + B i x)) =
      ∫ x, (partialTest n i (partialTest n i φ) x - x i * partialTest n i φ x) * ρ x := by
    calc
      _ = (∫ x, D i x * φ x) + ∫ x, B i x * φ x := by
        rw [← integral_add (hD i).1 (hB i).1]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change φ x * (D i x + B i x) = D i x * φ x + B i x * φ x
          ring
      _ = (∫ x, ρ x * partialTest n i (partialTest n i φ) x) -
          ∫ x, (x i * ρ x) * partialTest n i φ x := by rw [(hD i).2.2, (hB i).2.2]; ring
      _ = _ := by
        rw [← integral_sub (hD i).2.1 (hB i).2.1]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
  have hleft : (fun x => φ x * ouDensitySpatialOperator n ρ x) =
      fun x => ∑ i, φ x * (D i x + B i x) := by
    funext x
    change φ x * (∑ i : Fin n, (D i x + B i x)) = _
    rw [Finset.mul_sum]
  have hright : (fun x => ouTestGenerator n φ x * ρ x) =
      fun x => ∑ i, (partialTest n i (partialTest n i φ) x - x i * partialTest n i φ x) * ρ x := by
    funext x
    rw [ouTestGenerator_apply, Finset.sum_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hleft]
    exact integrable_finsetSum Finset.univ fun i _ => hL i
  · rw [hright]
    exact integrable_finsetSum Finset.univ fun i _ => hR i
  · rw [hleft, hright, integral_finsetSum Finset.univ (fun i _ => hL i),
      integral_finsetSum Finset.univ (fun i _ => hR i)]
    exact Finset.sum_congr rfl fun i _ => hrow i

end AffineFKProof
