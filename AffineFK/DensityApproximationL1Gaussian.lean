module

public import AffineFK.DensityApproximationL1Convolution
public import AffineFK.OrdinaryFisherConvolutionDensity
public import AffineFK.GaussianSmoothingRegularity
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# Actual Gaussian density approximation in Lebesgue L1

The smooth Gaussian-mixture density is identified with the actual
translation average by two proved laws and uniqueness of density.
This transfers genuine L1 translation-average convergence to that
positive smooth density, without moment or pointwise-kernel-integrability
assumptions. The ENNReal convolution-density proof is reused with its
original authorship from OrdinaryFisherConvolutionDensity.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem densityApproximation_gaussian_sum_law (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] (b : ℝ) :
    (((stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun g => b • g)).prod ν).map
      (fun p => p.1 + p.2) =
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (fun p => p.1 + b • p.2) := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ := stdGaussian E
  have hprod : (γ.map (fun g => b • g)).prod ν =
      (γ.prod ν).map (Prod.map (fun g => b • g) id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map γ ν
      (show Measurable (fun g : E => b • g) by fun_prop) measurable_id
  have hswap : γ.prod ν = (ν.prod γ).map Prod.swap := Measure.prod_swap.symm
  rw [hprod, Measure.map_map (by fun_prop) (by fun_prop), hswap,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  change b • p.2 + p.1 = p.1 + b • p.2
  exact add_comm _ _

theorem densityApproximation_gaussian_density_ae_average (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)] (b : ℝ) (hb : 0 < b) :
    gaussianSmoothingDensity n (densityMeasure n ρ) 1 b =ᵐ[volume]
      densityApproximationAverage n (stdGaussian (EuclideanSpace ℝ (Fin n))) ρ b := by
  let E := EuclideanSpace ℝ (Fin n)
  let ν := densityMeasure n ρ
  let γ := stdGaussian E
  let η := γ.map (fun g => b • g)
  let κ := ordinaryFisherConvolutionDensity n η ρ
  have hbm : Measurable (fun g : E => b • g) := by fun_prop
  have hκm : Measurable κ :=
    (ordinaryFisherConvolutionDensityENNReal_measurable n η ρ hm).ennreal_toReal
  have hκ0 (x : E) : 0 ≤ κ x := ENNReal.toReal_nonneg
  have hκavg : κ =ᵐ[volume] densityApproximationAverage n γ ρ b := by
    filter_upwards [ordinaryFisherConvolutionDensity_integral_ae n η ρ hm hρ0] with x hx
    change ordinaryFisherConvolutionDensity n η ρ x = densityApproximationAverage n γ ρ b x
    rw [hx.2]
    exact integral_map hbm.aemeasurable
      (hm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hsum := densityApproximation_gaussian_sum_law n ν b
  have hG := gaussianSmoothingDensity_law n ν 1 b hb
  simp only [one_smul] at hG
  have hlaw : densityMeasure n (gaussianSmoothingDensity n ν 1 b) = densityMeasure n κ :=
    hG.symm.trans (hsum.symm.trans (ordinaryFisherConvolutionDensity_law n η ρ hm))
  have hENN : (fun x => ENNReal.ofReal (gaussianSmoothingDensity n ν 1 b x)) =ᵐ[volume]
      fun x => ENNReal.ofReal (κ x) :=
    (withDensity_eq_iff_of_sigmaFinite
      (gaussianSmoothingDensity_continuous n ν 1 b).measurable.ennreal_ofReal.aemeasurable
      hκm.ennreal_ofReal.aemeasurable).mp hlaw
  have hreal : gaussianSmoothingDensity n ν 1 b =ᵐ[volume] κ := by
    filter_upwards [hENN] with x hx
    have h := congrArg ENNReal.toReal hx
    simpa only [ENNReal.toReal_ofReal (gaussianSmoothingDensity_pos n ν 1 b hb x).le,
      ENNReal.toReal_ofReal (hκ0 x)] using h
  exact hreal.trans hκavg

theorem densityApproximation_gaussian_density_L1_tendsto (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ : Integrable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))))
    [IsProbabilityMeasure (densityMeasure n ρ)] :
    Tendsto (fun b : ℝ => ∫ x, ‖gaussianSmoothingDensity n (densityMeasure n ρ) 1 b x - ρ x‖)
      (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun b : ℝ => ∫ x,
      ‖densityApproximationAverage n (stdGaussian (EuclideanSpace ℝ (Fin n))) ρ b x - ρ x‖)
      (𝓝[>] 0) (𝓝 0) := (densityApproximationAverage_L1_tendsto n
        (stdGaussian (EuclideanSpace ℝ (Fin n))) ρ hm hρ).mono_left nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with b hb
  apply integral_congr_ae
  filter_upwards [densityApproximation_gaussian_density_ae_average n ρ hm hρ0 b hb] with x hx
  rw [hx]

end AffineFKProof
