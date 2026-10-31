module

public import AffineFK.GaussianKilledL2
public import AffineFK.DirichletGaussianIterationFinite
public import AffineFK.GaussianKernelDerivativeBounds

/-! # Actual Gaussian kernel representatives of the compressed L2 operator -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

theorem gaussianFreeHeat_kernel_eq (n : ℕ) (h : ℝ) (hh : 0 < h)
    (x y : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledKernel n h x univ y = dirichletGaussianKernel n (Real.sqrt h) (x-y) := by
  rw [bridgeKilledKernel_univ n h hh]
  unfold bridgeFreeHeatDensity
  rw [ENNReal.ofReal_mul (by positivity)]
  change dirichletGaussianKernel n (Real.sqrt h) (y-x) = _
  rw [show y-x=-(x-y) by abel,dirichletGaussianKernel_neg]

theorem gaussianFreeHeatL2_density_coe (n : ℕ) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (bridgeFreeHeatL2 n h hh f : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => ∫ y, (dirichletGaussianKernel n (Real.sqrt h) (x-y)).toReal*f y := by
  unfold bridgeFreeHeatL2
  filter_upwards [bridgeKilledL2Operator_coe n h hh univ isOpen_univ f] with x hx
  rw [hx,bridgeKilledIntegral_eq_density_integral]
  simp_rw [gaussianFreeHeat_kernel_eq n h hh]

theorem gaussianKilledL2_density_coe (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (gaussianKilledL2 n U hU h hh f : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      U.indicator (fun x => ∫ y,
        (dirichletGaussianKernel n (Real.sqrt h) (x-y)).toReal * U.indicator f y) := by
  have hi (x : EuclideanSpace ℝ (Fin n)) :
      (∫ y, (dirichletGaussianKernel n (Real.sqrt h) (x-y)).toReal * gaussianKillL2 n U hU f y) =
      ∫ y, (dirichletGaussianKernel n (Real.sqrt h) (x-y)).toReal * U.indicator f y := by
    apply integral_congr_ae
    filter_upwards [gaussianKillL2_coe n U hU f] with y hy
    rw [hy]
  filter_upwards [gaussianKillL2_coe n U hU (bridgeFreeHeatL2 n h hh (gaussianKillL2 n U hU f)),
    gaussianFreeHeatL2_density_coe n h hh (gaussianKillL2 n U hU f)] with x hx hQ
  change gaussianKillL2 n U hU (bridgeFreeHeatL2 n h hh (gaussianKillL2 n U hU f)) x = _
  rw [hx]
  by_cases hm : x ∈ U
  · rw [indicator_of_mem hm,indicator_of_mem hm,hQ,hi]
  · rw [indicator_of_notMem hm,indicator_of_notMem hm]

theorem gaussianKilledL2_nonneg (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hf : ∀ᵐ x ∂volume, 0 ≤ f x) : ∀ᵐ x ∂volume, 0 ≤ gaussianKilledL2 n U hU h hh f x := by
  filter_upwards [gaussianKilledL2_density_coe n U hU h hh f] with x hx
  rw [hx]
  by_cases hm : x ∈ U
  · rw [indicator_of_mem hm]
    apply integral_nonneg_of_ae
    filter_upwards [hf] with y hy
    apply mul_nonneg ENNReal.toReal_nonneg
    by_cases hym : y ∈ U
    · rw [indicator_of_mem hym]
      exact hy
    · rw [indicator_of_notMem hym]
  · rw [indicator_of_notMem hm]

theorem gaussianKernel_toReal_uniform_bound (n : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : EuclideanSpace ℝ (Fin n),
      (dirichletGaussianKernel n b z).toReal ≤ B := by
  obtain ⟨C,hC,hbound⟩ := standardGaussianDensity_weighted_bound n 0
  refine ⟨(b^n)⁻¹*C,by positivity,?_⟩
  intro z
  simp only [pow_zero,one_mul] at hbound
  rw [dirichletGaussianKernel,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (standardGaussianDensity_pos n _).le]
  exact mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (hbound _)) (by positivity)

end AffineFKProof
