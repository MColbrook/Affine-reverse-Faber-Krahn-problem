module

public import AffineFK.DirichletGaussianIterationKernel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.Abel

/-!
# Genuine log-concave finite-grid Gaussian killing iterations

The recursion consists of the actual normalized Gaussian integral followed
by the actual domain indicator. Convexity implies pointwise log-concavity;
symmetry implies pointwise evenness. These are finite-grid integrals, not
an assumed Dirichlet heat semigroup or an assumed eigenfunction.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set
open scoped ENNReal

theorem dirichletGaussian_indicator_logConcave (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : Convex ℝ D) :
    LogConcaveDensity (D.indicator (fun _ => (1 : ℝ≥0∞))) := by
  intro t ht ht1 x y
  by_cases hzero : t = 0
  · subst t
    simp
  by_cases hone : t = 1
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
  have hsubpos : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 hone)
  by_cases hx : x ∈ D
  · by_cases hy : y ∈ D
    · have hz := hD hx hy (sub_nonneg.mpr ht1) ht (by ring : (1 - t) + t = 1)
      simp only [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hz,
        ENNReal.one_rpow, one_mul, le_refl]
    · simp only [indicator_of_notMem hy, ENNReal.zero_rpow_of_pos htpos, mul_zero, zero_le]
  · simp only [indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hsubpos, zero_mul, zero_le]

def dirichletGaussianStep (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n))) (b : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  D.indicator (fun z => ∫⁻ y, dirichletGaussianKernel n b (z - y) * f y) x

theorem dirichletGaussianStep_measurable (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : MeasurableSet D) (b : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f) :
    Measurable (dirichletGaussianStep n D b f) := by
  apply Measurable.indicator _ hD
  apply Measurable.lintegral_prod_right
  exact ((dirichletGaussianKernel_measurable n b).comp (measurable_fst.sub measurable_snd)).mul
    (hf.comp measurable_snd)

theorem dirichletGaussianStep_logConcave (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : Convex ℝ D) (b : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f) (hlf : LogConcaveDensity f) :
    LogConcaveDensity (dirichletGaussianStep n D b f) := by
  have hconv := logConcaveDensity_convolution_euclidean n _ _
    (dirichletGaussianKernel_measurable n b) hf (dirichletGaussianKernel_logConcave n b) hlf
  have hprod := logConcaveDensity_mul _ _ (dirichletGaussian_indicator_logConcave n D hD) hconv
  convert hprod using 1
  funext x
  by_cases hx : x ∈ D <;> simp [dirichletGaussianStep, hx]

theorem dirichletGaussianStep_le_one (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (b : ℝ) (hb : 0 < b)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : ∀ x, f x ≤ 1)
    (x : EuclideanSpace ℝ (Fin n)) : dirichletGaussianStep n D b f x ≤ 1 := by
  by_cases hx : x ∈ D
  · rw [dirichletGaussianStep, indicator_of_mem hx]
    calc
      _ ≤ ∫⁻ y, dirichletGaussianKernel n b (x - y) :=
        lintegral_mono (fun y => (mul_le_mul' le_rfl (hf y)).trans_eq (mul_one _))
      _ = 1 := dirichletGaussianKernel_translate_lintegral n b hb x
  · simp only [dirichletGaussianStep, indicator_of_notMem hx, zero_le]

theorem dirichletGaussianStep_even (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : ∀ x ∈ D, -x ∈ D) (b : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : ∀ x, f (-x) = f x)
    (x : EuclideanSpace ℝ (Fin n)) : dirichletGaussianStep n D b f (-x) = dirichletGaussianStep n D b f x := by
  have hm : -x ∈ D ↔ x ∈ D := ⟨fun h => by simpa only [neg_neg] using hD (-x) h, hD x⟩
  by_cases hx : x ∈ D
  · rw [dirichletGaussianStep, dirichletGaussianStep, indicator_of_mem hx, indicator_of_mem (hm.mpr hx)]
    calc
      _ = ∫⁻ y, dirichletGaussianKernel n b (-x - -y) * f (-y) :=
        (lintegral_neg_eq_self (fun y => dirichletGaussianKernel n b (-x - y) * f y)).symm
      _ = _ := by
        apply lintegral_congr
        intro y
        rw [show -x - -y = -(x - y) by abel, dirichletGaussianKernel_neg, hf]
  · simp only [dirichletGaussianStep, indicator_of_notMem hx, indicator_of_notMem (not_congr hm |>.mpr hx)]

def dirichletGaussianIterate (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n))) (b : ℝ) :
    ℕ → EuclideanSpace ℝ (Fin n) → ℝ≥0∞
  | 0 => D.indicator (fun _ => 1)
  | k + 1 => dirichletGaussianStep n D b (dirichletGaussianIterate n D b k)

theorem dirichletGaussianIterate_measurable (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : MeasurableSet D) (b : ℝ) (k : ℕ) :
    Measurable (dirichletGaussianIterate n D b k) := by
  induction k with
  | zero => exact measurable_const.indicator hD
  | succ k hk => exact dirichletGaussianStep_measurable n D hD b _ hk

theorem dirichletGaussianIterate_logConcave (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hDm : MeasurableSet D) (hD : Convex ℝ D)
    (b : ℝ) (k : ℕ) : LogConcaveDensity (dirichletGaussianIterate n D b k) := by
  induction k with
  | zero => exact dirichletGaussian_indicator_logConcave n D hD
  | succ k hk =>
      exact dirichletGaussianStep_logConcave n D hD b _
        (dirichletGaussianIterate_measurable n D hDm b k) hk

theorem dirichletGaussianIterate_le_one (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (b : ℝ) (hb : 0 < b) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : dirichletGaussianIterate n D b k x ≤ 1 := by
  induction k generalizing x with
  | zero => by_cases hx : x ∈ D <;> simp [dirichletGaussianIterate, hx]
  | succ k hk => exact dirichletGaussianStep_le_one n D b hb _ hk x

theorem dirichletGaussianIterate_even (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : ∀ x ∈ D, -x ∈ D)
    (b : ℝ) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    dirichletGaussianIterate n D b k (-x) = dirichletGaussianIterate n D b k x := by
  induction k generalizing x with
  | zero =>
    have hm : -x ∈ D ↔ x ∈ D := ⟨fun h => by simpa only [neg_neg] using hD (-x) h, hD x⟩
    by_cases hx : x ∈ D <;> simp [dirichletGaussianIterate, hx, hm]
  | succ k hk => exact dirichletGaussianStep_even n D hD b _ hk x

theorem dirichletGaussianIterate_zero_outside (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (b : ℝ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ D) : dirichletGaussianIterate n D b k x = 0 := by
  cases k <;> simp only [dirichletGaussianIterate, dirichletGaussianStep, indicator_of_notMem hx]

theorem dirichletGaussianIterate_mass_le (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : MeasurableSet D)
    (b : ℝ) (hb : 0 < b) (k : ℕ) :
    (∫⁻ x, dirichletGaussianIterate n D b k x) ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))) D := by
  calc
    _ ≤ ∫⁻ x, D.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ D
      · simpa only [indicator_of_mem hx] using dirichletGaussianIterate_le_one n D b hb k x
      · simp only [dirichletGaussianIterate_zero_outside n D b k x hx, indicator_of_notMem hx, le_refl]
    _ = _ := by rw [lintegral_indicator_const hD, one_mul]

end AffineFKProof
