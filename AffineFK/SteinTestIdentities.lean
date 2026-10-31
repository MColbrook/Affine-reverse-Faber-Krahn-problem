module

public import AffineFK.SecondPoisson
public import AffineFK.IsotropicCoordinates

/-!
# The componentwise second-order Stein identity

The first and second Poisson equations are tested on genuine compactly
supported smooth functions and their genuine partial derivatives. Finite
dimensional Parseval supplies the contraction identity in the L2 spaces.
Reflection and centring of the third-order coefficients remain separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

theorem l2Coordinate_inner_sum
    {X : Type*} [MeasurableSpace X] (n : ℕ) (ν : Measure X)
    (g h : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    (∑ j : Fin n, ⟪l2Coordinate n ν j g, l2Coordinate n ν j h⟫) = ⟪g, h⟫ := by
  have ha := l2Coordinate_norm_sq_sum n ν (g + h)
  simp_rw [map_add, norm_add_sq_real, Finset.sum_add_distrib, ← Finset.mul_sum] at ha
  rw [l2Coordinate_norm_sq_sum n ν g, l2Coordinate_norm_sq_sum n ν h] at ha
  linarith

def partialTest
    (n : ℕ) (j : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  TestFunction.postcompCLM (coordinateFunctional n j) (testFunctionGradient φ)

theorem partialTest_apply
    (n : ℕ) (j : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    partialTest n j φ x = (gradient φ x) j := by
  change coordinateFunctional n j (testFunctionGradient φ x) = _
  rw [coordinateFunctional_apply, testFunctionGradient_apply]

theorem partialTest_fderiv
    (n : ℕ) (j : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    partialTest n j φ x = fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  rw [partialTest_apply, ← inner_gradient_left]
  rw [real_inner_comm]
  exact (EuclideanSpace.basisFun_inner (Fin n) ℝ (gradient φ x) j).symm

theorem partialTest_toL2
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (j : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    testFunctionToL2 ν (partialTest n j φ) =
      l2Coordinate n ν j (testFunctionToL2 ν (testFunctionGradient φ)) := by
  apply Lp.ext
  filter_upwards [testFunctionToL2_coe ν (partialTest n j φ),
    l2Coordinate_coe n ν j (testFunctionToL2 ν (testFunctionGradient φ)),
    testFunctionToL2_coe ν (testFunctionGradient φ)] with x hp hc hg
  rw [hp, hc, hg, testFunctionGradient_apply, partialTest_apply]

/-- The exact contraction of the centred first-kernel row with a gradient
equals the sum of its scalar sources tested on genuine partials. -/
theorem firstSteinSource_partial_sum
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (u : Fin n → weightedSobolevGraph ν) (i : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∑ j : Fin n, ⟪firstSteinSource n ν u i j, testFunctionToL2 ν (partialTest n j φ)⟫) =
      ⟪sobolevGradient ν (u i) - Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i),
        testFunctionToL2 ν (testFunctionGradient φ)⟫ := by
  simp_rw [firstSteinSource, partialTest_toL2]
  exact l2Coordinate_inner_sum n ν _ _

/-- The scalar component of the second-order identity, with actual Bochner
integrals and actual partial derivatives. The Poisson premises are the
equations proved for the constructed solutions in the preceding modules. -/
theorem second_stein_component_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i : Fin n) (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (u : Fin n → weightedSobolevGraph ν)
    (v : Fin n → Fin n → weightedSobolevGraph ν)
    (hfirst : ∀ f : weightedSobolevGraph ν,
      ⟪sobolevGradient ν (u i), sobolevGradient ν f⟫ =
        ⟪hxi.toLp (fun x : EuclideanSpace ℝ (Fin n) => x i), sobolevValue ν f⟫)
    (hsecond : ∀ j (f : weightedSobolevGraph ν),
      ⟪sobolevGradient ν (v i j), sobolevGradient ν f⟫ =
        ⟪firstSteinSource n ν u i j, sobolevValue ν f⟫)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν) =
      ∑ j : Fin n, ∫ x,
        ⟪sobolevGradient ν (v i j) x, gradient (partialTest n j φ) x⟫ ∂ν := by
  have hscalar : ⟪hxi.toLp (fun x : EuclideanSpace ℝ (Fin n) => x i),
      testFunctionToL2 ν φ⟫ = ∫ x, x i * φ x ∂ν := by
    rw [l2_real_inner_integral]
    apply integral_congr_ae
    filter_upwards [hxi.coeFn_toLp, testFunctionToL2_coe ν φ] with x hx hf
    rw [hx, hf]
  have hfirsttest := hfirst ⟨smoothGradientPair ν φ, smoothGradientPair_mem ν φ⟩
  change ⟪sobolevGradient ν (u i), testFunctionToL2 ν (testFunctionGradient φ)⟫ =
    ⟪hxi.toLp (fun x : EuclideanSpace ℝ (Fin n) => x i), testFunctionToL2 ν φ⟫ at hfirsttest
  have hdiagonal : ⟪Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ i),
      testFunctionToL2 ν (testFunctionGradient φ)⟫ = ∫ x, partialTest n i φ x ∂ν := by
    rw [real_inner_comm, ← l2Coordinate_mean, ← partialTest_toL2,
      testFunctionToL2_mean]
  have hsecondtest (j : Fin n) :
      ⟪sobolevGradient ν (v i j), testFunctionToL2 ν (testFunctionGradient (partialTest n j φ))⟫ =
        ⟪firstSteinSource n ν u i j, testFunctionToL2 ν (partialTest n j φ)⟫ :=
    hsecond j ⟨smoothGradientPair ν (partialTest n j φ), smoothGradientPair_mem ν (partialTest n j φ)⟩
  have hsum : (∑ j : Fin n, ⟪sobolevGradient ν (v i j),
      testFunctionToL2 ν (testFunctionGradient (partialTest n j φ))⟫) =
      (∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν) := by
    simp_rw [hsecondtest]
    rw [firstSteinSource_partial_sum, inner_sub_left, hfirsttest, hscalar, hdiagonal]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [testFunctionToL2_coe ν (testFunctionGradient (partialTest n j φ))] with x hx
  rw [hx, testFunctionGradient_apply]

/-- The second-order component identity and its exact energy follow from
the original centred isotropic moments and Poincare inequality, without any
assumed Poisson solution or Stein identity. Parity is not asserted here. -/
theorem second_stein_exists_components
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ) (hPnonneg : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (hmean : ∀ i : Fin n, ∫ x, x i ∂ν = 0)
    (hcov : ∀ i j : Fin n, (∫ x, x i * x j ∂ν) = if i = j then 1 else 0) :
    ∃ v : Fin n → Fin n → weightedSobolevGraph ν,
      (∀ i j, l2Mean ν (sobolevValue ν (v i j)) = 0) ∧
      ((∑ i : Fin n, ∑ j : Fin n, ‖sobolevGradient ν (v i j)‖ ^ 2) ≤ P * (P - 1) * n) ∧
      (∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
        (∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν) =
          ∑ j : Fin n, ∫ x,
            ⟪sobolevGradient ν (v i j) x, gradient (partialTest n j φ) x⟫ ∂ν) := by
  let hxi := fun i => isotropic_coordinate_memLp n ν hcov i
  obtain ⟨u, _humean, hfirst, _huenergy, hpair, hrow⟩ :=
    first_poisson_solutions n ν P hPnonneg hP hxi hmean hcov
  obtain ⟨v, hvmean, hsecond, _hvenergy, hvsum⟩ :=
    second_poisson_solutions n ν P hPnonneg hP u hpair hrow
  exact ⟨v, hvmean, hvsum, fun i φ =>
    second_stein_component_identity n ν i (hxi i) u v (hfirst i) (hsecond i) φ⟩

end AffineFKProof
