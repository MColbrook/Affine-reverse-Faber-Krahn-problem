module

public import AffineFK.GroundstateGaussianEnergyAlgebra
public import AffineFK.DirichletMultiplier
public import AffineFK.DirichletWeakEigenfunction

/-!
# Gaussian-weighted energy of an actual weak Dirichlet eigenfunction

Both multipliers act on the genuine H0^1 closure. The weak eigen-equation
is tested by the squared Gaussian multiplier times the original element.
Its value and weak gradient are the proved product representatives, and
all three quadratic integrals below are genuinely integrable. No computed
energy identity, boundary regularity, or eigenfunction existence is a
premise. The equation holds for every weak eigenfunction, not just the
first one; existence and ground-state properties remain separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped RealInnerProductSpace

def gaussianDirichletFactor (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    dirichletSobolev n U →L[ℝ] dirichletSobolev n U :=
  dirichletMultiplier n U (groundstateGaussianFactor n) (groundstateGaussianFactor_smooth n)
    1 (5 / 2) (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (groundstateGaussianFactor_pos n x)]
      exact groundstateGaussianFactor_le_one n x)
    (groundstateGaussianFactor_gradient_bound n)

def gaussianDirichletWeight (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    dirichletSobolev n U →L[ℝ] dirichletSobolev n U :=
  dirichletMultiplier n U (groundstateGaussianWeight n) (groundstateGaussianWeight_smooth n)
    1 5 (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (groundstateGaussianWeight_bound n x).1]
      exact (groundstateGaussianWeight_bound n x).2)
    (groundstateGaussianWeight_gradient_bound n)

theorem gaussianDirichletFactor_value (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) :
    (dirichletValue n U (gaussianDirichletFactor n U ψ) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume] fun x => groundstateGaussianFactor n x * dirichletValue n U ψ x :=
  dirichletMultiplier_value n U _ _ _ _ _ _ ψ

theorem gaussianDirichletFactor_gradient (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) :
    (dirichletGradient n U (gaussianDirichletFactor n U ψ) :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
      fun x => groundstateGaussianFactor n x • dirichletGradient n U ψ x +
        dirichletValue n U ψ x • gradient (groundstateGaussianFactor n) x :=
  dirichletMultiplier_gradient n U _ _ _ _ _ _ ψ

theorem gaussianDirichletWeight_value (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) :
    (dirichletValue n U (gaussianDirichletWeight n U ψ) : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume] fun x => groundstateGaussianWeight n x * dirichletValue n U ψ x :=
  dirichletMultiplier_value n U _ _ _ _ _ _ ψ

theorem gaussianDirichletWeight_gradient (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) :
    (dirichletGradient n U (gaussianDirichletWeight n U ψ) :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
      fun x => groundstateGaussianWeight n x • dirichletGradient n U ψ x +
        dirichletValue n U ψ x • gradient (groundstateGaussianWeight n) x :=
  dirichletMultiplier_gradient n U _ _ _ _ _ _ ψ

set_option maxHeartbeats 1000000 in
theorem gaussian_dirichlet_groundstate_energy_of_representatives (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ell : ℝ) (ψ v w : dirichletSobolev n U)
    (hψ : IsDirichletWeakEigenfunction n U ell ψ)
    (hvval : (dirichletValue n U v : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => groundstateGaussianFactor n x * dirichletValue n U ψ x)
    (hwval : (dirichletValue n U w : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => groundstateGaussianWeight n x * dirichletValue n U ψ x)
    (hvgrad : (dirichletGradient n U v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
      fun x => groundstateGaussianFactor n x • dirichletGradient n U ψ x +
        dirichletValue n U ψ x • gradient (groundstateGaussianFactor n) x)
    (hwgrad : (dirichletGradient n U w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
      fun x => groundstateGaussianWeight n x • dirichletGradient n U ψ x +
        dirichletValue n U ψ x • gradient (groundstateGaussianWeight n) x) :
    Integrable (fun x => ‖dirichletGradient n U v x‖ ^ 2) ∧
    Integrable (fun x => (dirichletValue n U v x) ^ 2) ∧
    Integrable (fun x => ‖x‖ ^ 2 * (dirichletValue n U v x) ^ 2) ∧
    (∫ x, ‖dirichletGradient n U v x‖ ^ 2) =
      ell * (∫ x, (dirichletValue n U v x) ^ 2) +
        (1 / 4 : ℝ) * (∫ x, ‖x‖ ^ 2 * (dirichletValue n U v x) ^ 2) := by
  have hv2 : Integrable (fun x => (dirichletValue n U v x) ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (Lp.memLp (dirichletValue n U v)).aestronglyMeasurable).mp
        (Lp.memLp (dirichletValue n U v))
  have hg2 : Integrable (fun x => ‖dirichletGradient n U v x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp (dirichletGradient n U v)).aestronglyMeasurable).mp
      (Lp.memLp (dirichletGradient n U v))
  have hm0 := groundstate_gaussian_moment_integrable n volume (dirichletValue n U ψ)
    (Lp.memLp (dirichletValue n U ψ))
  have hmoment : Integrable (fun x => ‖x‖ ^ 2 * (dirichletValue n U v x) ^ 2) := by
    apply hm0.congr
    filter_upwards [hvval] with x hx
    exact congrArg (fun p : ℝ => ‖x‖ ^ 2 * p ^ 2) hx.symm
  have htest := dirichletWeakEigenfunction_integral n U ell ψ hψ w
  have hpoint : (fun x => ‖dirichletGradient n U v x‖ ^ 2) =ᵐ[volume]
      fun x => ⟪dirichletGradient n U ψ x, dirichletGradient n U w x⟫ +
        (1 / 4 : ℝ) * (‖x‖ ^ 2 * (dirichletValue n U v x) ^ 2) := by
    filter_upwards [hvgrad, hwgrad, hvval] with x hvx hwx hvalx
    calc
      _ = ‖groundstateGaussianFactor n x • dirichletGradient n U ψ x +
          dirichletValue n U ψ x • gradient (groundstateGaussianFactor n) x‖ ^ 2 :=
        congrArg (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2) hvx
      _ = ⟪dirichletGradient n U ψ x,
          groundstateGaussianWeight n x • dirichletGradient n U ψ x +
            dirichletValue n U ψ x • gradient (groundstateGaussianWeight n) x⟫ +
          (1 / 4 : ℝ) * (‖x‖ ^ 2 * (groundstateGaussianFactor n x * dirichletValue n U ψ x) ^ 2) := by
        simpa only [mul_assoc] using
          groundstate_gaussian_energy_pointwise n (dirichletValue n U ψ x) (dirichletGradient n U ψ x) x
      _ = _ := congrArg₂ (fun (z : EuclideanSpace ℝ (Fin n)) (p : ℝ) =>
        ⟪dirichletGradient n U ψ x, z⟫ + (1 / 4 : ℝ) * (‖x‖ ^ 2 * p ^ 2)) hwx.symm hvalx.symm
  have hvalues : (∫ x, dirichletValue n U ψ x * dirichletValue n U w x) =
      ∫ x, (dirichletValue n U v x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hwval, hvval] with x hwx hvx
    calc
      _ = dirichletValue n U ψ x * (groundstateGaussianWeight n x * dirichletValue n U ψ x) :=
        congrArg (fun p : ℝ => dirichletValue n U ψ x * p) hwx
      _ = groundstateGaussianWeight n x * (dirichletValue n U ψ x) ^ 2 := by ring
      _ = (groundstateGaussianFactor n x) ^ 2 * (dirichletValue n U ψ x) ^ 2 :=
        congrArg (fun p : ℝ => p * (dirichletValue n U ψ x) ^ 2) (groundstateGaussianFactor_sq n x).symm
      _ = (groundstateGaussianFactor n x * dirichletValue n U ψ x) ^ 2 := by ring
      _ = _ := congrArg (fun p : ℝ => p ^ 2) hvx.symm
  have he := integral_congr_ae hpoint
  rw [integral_add htest.1 (hmoment.const_mul (1 / 4 : ℝ)), integral_const_mul,
    htest.2.2, hvalues] at he
  exact ⟨hg2, hv2, hmoment, he⟩

theorem gaussian_dirichlet_groundstate_energy (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ell : ℝ) (ψ : dirichletSobolev n U)
    (hψ : IsDirichletWeakEigenfunction n U ell ψ) :
    let v := gaussianDirichletFactor n U ψ
    Integrable (fun x => ‖dirichletGradient n U v x‖ ^ 2) ∧
    Integrable (fun x => (dirichletValue n U v x) ^ 2) ∧
    Integrable (fun x => ‖x‖ ^ 2 * (dirichletValue n U v x) ^ 2) ∧
    (∫ x, ‖dirichletGradient n U v x‖ ^ 2) =
      ell * (∫ x, (dirichletValue n U v x) ^ 2) +
        (1 / 4 : ℝ) * (∫ x, ‖x‖ ^ 2 * (dirichletValue n U v x) ^ 2) :=
  gaussian_dirichlet_groundstate_energy_of_representatives n U ell ψ
    (gaussianDirichletFactor n U ψ) (gaussianDirichletWeight n U ψ) hψ
    (gaussianDirichletFactor_value n U ψ) (gaussianDirichletWeight_value n U ψ)
    (gaussianDirichletFactor_gradient n U ψ) (gaussianDirichletWeight_gradient n U ψ)

end AffineFKProof
