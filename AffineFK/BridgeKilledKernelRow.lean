module

public import AffineFK.BridgeKilledPointwiseComposition
public import AffineFK.BridgeKilledKernelSymmetry
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Genuine L2 rows and the fixed killed-kernel diagonal

Pointwise composition and pointwise symmetry identify the squared L2 norm
of each actual density row with the particular diagonal at doubled time.
The row's integrability is derived from this finite diagonal, not assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

theorem bridgeKilledKernel_ne_top (n : ℕ) (T : ℝ) (x y : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : bridgeKilledKernel n T x Ω y ≠ ∞ := by
  intro htop
  have h := bridgeKilledKernel_le_free n T x y Ω
  rw [htop] at h
  exact ENNReal.ofReal_ne_top (top_le_iff.mp h)

theorem bridgeKilledKernel_diagonal_square (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeKilledKernel n (2*t) x Ω x = ∫⁻ y, (bridgeKilledKernel n t x Ω y)^2 ∂volume := by
  rw [two_mul,bridgeKilledKernel_pointwise_semigroup n t t ht ht x x Ω hΩ]
  apply lintegral_congr
  intro y
  rw [bridgeKilledKernel_symmetric n t ht y x Ω hΩ]
  exact (pow_two _).symm

theorem bridgeKilledKernel_row_memLp_and_square (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    MemLp (fun y => (bridgeKilledKernel n t x Ω y).toReal) 2 volume ∧
      (∫ y, ((bridgeKilledKernel n t x Ω y).toReal)^2 ∂volume) =
        (bridgeKilledKernel n (2*t) x Ω x).toReal := by
  have hm : Measurable (fun y => (bridgeKilledKernel n t x Ω y).toReal) :=
    (bridgeKilledKernel_measurable n t x Ω hΩ).ennreal_toReal
  have he : (∫⁻ y, ENNReal.ofReal (((bridgeKilledKernel n t x Ω y).toReal)^2) ∂volume) =
      bridgeKilledKernel n (2*t) x Ω x := by
    calc
      _ = ∫⁻ y, (bridgeKilledKernel n t x Ω y)^2 ∂volume := by
        apply lintegral_congr
        intro y
        rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (bridgeKilledKernel_ne_top n t x y Ω)]
      _ = _ := (bridgeKilledKernel_diagonal_square n t ht x Ω hΩ).symm
  have hi : Integrable (fun y => ((bridgeKilledKernel n t x Ω y).toReal)^2) volume :=
    (lintegral_ofReal_ne_top_iff_integrable (hm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => sq_nonneg _))).mp
        (by rw [he]; exact bridgeKilledKernel_ne_top n (2*t) x x Ω)
  refine ⟨(memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi, ?_⟩
  have hI := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun y => sq_nonneg ((bridgeKilledKernel n t x Ω y).toReal)))
  rw [he] at hI
  have h := congrArg ENNReal.toReal hI
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun y => sq_nonneg _))] using h

/-- The actual killed density row as a Lebesgue L2 class, with membership
derived from the finite selected doubled-time diagonal. -/
def bridgeKilledRowL2 (n : ℕ) (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (bridgeKilledKernel_row_memLp_and_square n t ht x Ω hΩ).1.toLp
    (fun y => (bridgeKilledKernel n t x Ω y).toReal)

theorem bridgeKilledRowL2_coe (n : ℕ) (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    (bridgeKilledRowL2 n t ht x Ω hΩ : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun y => (bridgeKilledKernel n t x Ω y).toReal :=
  MemLp.coeFn_toLp (bridgeKilledKernel_row_memLp_and_square n t ht x Ω hΩ).1

theorem bridgeKilledRowL2_norm_sq (n : ℕ) (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    ‖bridgeKilledRowL2 n t ht x Ω hΩ‖^2 = (bridgeKilledKernel n (2*t) x Ω x).toReal := by
  calc
    _ = ⟪bridgeKilledRowL2 n t ht x Ω hΩ, bridgeKilledRowL2 n t ht x Ω hΩ⟫ :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ y, ⟪bridgeKilledRowL2 n t ht x Ω hΩ y,bridgeKilledRowL2 n t ht x Ω hΩ y⟫ ∂volume :=
      L2.inner_def _ _
    _ = ∫ y, (bridgeKilledRowL2 n t ht x Ω hΩ y)^2 ∂volume := by
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = ∫ y, ((bridgeKilledKernel n t x Ω y).toReal)^2 ∂volume :=
      integral_congr_ae ((bridgeKilledRowL2_coe n t ht x Ω hΩ).fun_comp (fun a : ℝ => a^2))
    _ = _ := (bridgeKilledKernel_row_memLp_and_square n t ht x Ω hΩ).2

end AffineFKProof
