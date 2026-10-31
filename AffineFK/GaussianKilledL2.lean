module

public import AffineFK.GaussianKilledProjection
public import AffineFK.GaussianL2Semigroup

/-!
# The actual Gaussian convolution followed by domain killing on L2

The two domain projections are genuine multiplication by the domain
indicator. Quadratic positivity follows from the proved Gaussian
half-time composition, separately from positivity of the kernel.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Filter
open scoped RealInnerProductSpace

def gaussianKilledL2 (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (h : ℝ) (hh : 0 < h) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (gaussianKillL2 n U hU).comp ((bridgeFreeHeatL2 n h hh).comp (gaussianKillL2 n U hU))

theorem gaussianFreeHeatL2_norm_le (n : ℕ) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖bridgeFreeHeatL2 n h hh f‖ ≤ ‖f‖ := by
  rw [← gaussianL2Average_eq_heat n h hh f]
  exact bridgeGaussianL2Average_norm_le n (Real.sqrt h) f

theorem gaussianKilledL2_norm_le (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖gaussianKilledL2 n U hU h hh f‖ ≤ ‖f‖ := by
  exact (gaussianKillL2_norm_le n U hU _).trans
    ((gaussianFreeHeatL2_norm_le n h hh _).trans (gaussianKillL2_norm_le n U hU f))

theorem gaussianKilledL2_inner (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (h : ℝ) (hh : 0 < h)
    (f g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ⟪gaussianKilledL2 n U hU h hh f,g⟫ = ⟪f,gaussianKilledL2 n U hU h hh g⟫ := by
  change ⟪gaussianKillL2 n U hU (bridgeFreeHeatL2 n h hh (gaussianKillL2 n U hU f)),g⟫ =
    ⟪f,gaussianKillL2 n U hU (bridgeFreeHeatL2 n h hh (gaussianKillL2 n U hU g))⟫
  rw [gaussianKillL2_inner, ← gaussianKillL2_inner n U hU f]
  exact (gaussianFreeHeatL2_selfAdjoint n h hh).isSymmetric _ _

theorem gaussianKilledL2_selfAdjoint (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (h : ℝ) (hh : 0 < h) :
    IsSelfAdjoint (gaussianKilledL2 n U hU h hh) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (gaussianKilledL2_inner n U hU h hh)

theorem gaussianKilledL2_quadratic_nonneg (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    0 ≤ ⟪gaussianKilledL2 n U hU h hh f,f⟫ := by
  change 0 ≤ ⟪gaussianKillL2 n U hU (bridgeFreeHeatL2 n h hh (gaussianKillL2 n U hU f)),f⟫
  rw [gaussianKillL2_inner]
  exact gaussianFreeHeatL2_quadratic_nonneg n h hh _

theorem gaussianKilledL2_zero_exterior (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∀ᵐ x ∂volume, x ∉ U → gaussianKilledL2 n U hU h hh f x=0 :=
  gaussianKillL2_zero_exterior n U hU _

theorem gaussianKilledL2_supported_pairing (n : ℕ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (h : ℝ) (hh : 0 < h)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hf : ∀ᵐ x ∂volume, x ∉ U → f x=0) :
    ⟪f,gaussianKilledL2 n U hU h hh f⟫ = ⟪f,bridgeFreeHeatL2 n h hh f⟫ := by
  change ⟪f,gaussianKillL2 n U hU (bridgeFreeHeatL2 n h hh (gaussianKillL2 n U hU f))⟫ = _
  rw [← gaussianKillL2_inner,gaussianKillL2_of_zero_exterior n U hU f hf]

end AffineFKProof
