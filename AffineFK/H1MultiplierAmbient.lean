module

public import AffineFK.H1MultiplierCoefficients
public import AffineFK.DirichletSobolev
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The actual value-gradient product operator

An arbitrary globally smooth multiplier with bounded value and gradient
acts on the actual Lebesgue L2 value-gradient ambient space. On compact
smooth functions its image is the genuine pointwise product with its
actual derivative. These facts allow passage to H1 and H0^1 closures.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions ContDiff RealInnerProductSpace

def h1MultiplierAmbient (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1) :
    SobolevAmbient (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      SobolevAmbient (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  let V := Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))
  let G := Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))
  (WithLp.prodContinuousLinearEquiv 2 ℝ V G).symm.toContinuousLinearMap.comp
    (((h1ScalarCoefficient n m hm C0 hb0).comp (WithLp.fstL 2 ℝ V G)).prod
      (((h1VectorCoefficient n m hm C0 hb0).comp (WithLp.sndL 2 ℝ V G)) +
        ((h1CrossCoefficient n m hm C1 hb1).comp (WithLp.fstL 2 ℝ V G))))

theorem h1MultiplierAmbient_value (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1)
    (v : SobolevAmbient (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (WithLp.fstL 2 ℝ
      (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (h1MultiplierAmbient n m hm C0 C1 hb0 hb1 v) :
      EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => m x * (WithLp.fstL 2 ℝ _ _ v) x := by
  change h1ScalarCoefficient n m hm C0 hb0 (WithLp.fstL 2 ℝ _ _ v) =ᵐ[volume] _
  exact h1ScalarCoefficient_coe n m hm C0 hb0 _

theorem h1MultiplierAmbient_gradient (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1)
    (v : SobolevAmbient (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (WithLp.sndL 2 ℝ
      (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (h1MultiplierAmbient n m hm C0 C1 hb0 hb1 v) :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
      fun x => m x • (WithLp.sndL 2 ℝ _ _ v) x +
        (WithLp.fstL 2 ℝ _ _ v) x • gradient m x := by
  change h1VectorCoefficient n m hm C0 hb0 (WithLp.sndL 2 ℝ _ _ v) +
    h1CrossCoefficient n m hm C1 hb1 (WithLp.fstL 2 ℝ _ _ v) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add
      (h1VectorCoefficient n m hm C0 hb0 (WithLp.sndL 2 ℝ _ _ v))
      (h1CrossCoefficient n m hm C1 hb1 (WithLp.fstL 2 ℝ _ _ v)),
    h1VectorCoefficient_coe n m hm C0 hb0 (WithLp.sndL 2 ℝ _ _ v),
    h1CrossCoefficient_coe n m hm C1 hb1 (WithLp.fstL 2 ℝ _ _ v)] with x ha hb hc
  rw [ha]
  simp only [Pi.add_apply]
  rw [hb, hc]

def h1MultiplyTest (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → ℝ) (hm : ContDiff ℝ ∞ m) (φ : 𝓓(U, ℝ)) : 𝓓(U, ℝ) :=
  ⟨(fun x => m x * φ x), hm.mul φ.contDiff, φ.hasCompactSupport.mul_left,
    tsupport_mul_subset_right.trans φ.tsupport_subset⟩

theorem h1MultiplyTest_gradient (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → ℝ) (hm : ContDiff ℝ ∞ m)
    (φ : 𝓓(U, ℝ)) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (h1MultiplyTest n U m hm φ) x = m x • gradient φ x + φ x • gradient m x := by
  change (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ (fun y => m y * φ y) x) = _
  rw [fderiv_fun_mul (hm.differentiable (by simp)).differentiableAt
    (φ.contDiff.differentiable (by simp)).differentiableAt, map_add, map_smul, map_smul]
  rfl

theorem h1MultiplierAmbient_smooth_pair (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    h1MultiplierAmbient n m hm C0 C1 hb0 hb1 (unweightedSmoothPair n φ) =
      unweightedSmoothPair n (h1MultiplyTest n ⊤ m hm φ) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))).injective
  apply Prod.ext
  · apply Lp.ext
    have h := h1MultiplierAmbient_value n m hm C0 C1 hb0 hb1 (unweightedSmoothPair n φ)
    change (WithLp.fstL 2 ℝ _ _ (h1MultiplierAmbient n m hm C0 C1 hb0 hb1
      (unweightedSmoothPair n φ))) =ᵐ[volume] unweightedTestToL2 n (h1MultiplyTest n ⊤ m hm φ)
    filter_upwards [h, unweightedTestToL2_coe n φ,
      unweightedTestToL2_coe n (h1MultiplyTest n ⊤ m hm φ)] with x hx hf hp
    rw [hx, hp]
    change m x * unweightedTestToL2 n φ x = m x * φ x
    rw [hf]
  · apply Lp.ext
    have h := h1MultiplierAmbient_gradient n m hm C0 C1 hb0 hb1 (unweightedSmoothPair n φ)
    change (WithLp.sndL 2 ℝ _ _ (h1MultiplierAmbient n m hm C0 C1 hb0 hb1
      (unweightedSmoothPair n φ))) =ᵐ[volume]
        unweightedTestToL2 n (testFunctionGradient (h1MultiplyTest n ⊤ m hm φ))
    filter_upwards [h, unweightedTestToL2_coe n φ,
      unweightedTestToL2_coe n (testFunctionGradient φ),
      unweightedTestToL2_coe n (testFunctionGradient (h1MultiplyTest n ⊤ m hm φ))]
      with x hx hf hg hp
    rw [hx, hp, testFunctionGradient_apply, h1MultiplyTest_gradient]
    change m x • unweightedTestToL2 n (testFunctionGradient φ) x +
      unweightedTestToL2 n φ x • gradient m x = _
    rw [hf, hg, testFunctionGradient_apply]

end AffineFKProof
