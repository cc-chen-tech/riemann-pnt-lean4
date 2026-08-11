import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderPerronKernel

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform BigOperators

namespace PrimeNumberTheorem

example (a : ℂ) (ha : a.re < 0) :
    (∫ u : ℝ in Ioi 0, ((u : ℂ) ^ 2 / 2) * Complex.exp (a * u)) =
      -(1 / a ^ 3) :=
  integral_sq_div_two_mul_cexp_Ioi a ha

example (c u : ℝ) :
    thirdOrderPerronStep c u =
      (((max u 0) ^ 2 / 2 : ℝ) : ℂ) * Complex.exp (-c * max u 0) := rfl

example (c : ℝ) (hc : 0 < c) (w : ℝ) :
    𝓕 (thirdOrderPerronStep c) w =
      1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3 :=
  fourier_thirdOrderPerronStep c hc w

example (c : ℝ) (hc : 0 < c) :
    Integrable (thirdOrderPerronStep c) :=
  integrable_thirdOrderPerronStep c hc

example (c : ℝ) (hc : 0 < c) :
    Integrable (𝓕 (thirdOrderPerronStep c)) :=
  integrable_fourier_thirdOrderPerronStep c hc

example (c : ℝ) (hc : 0 < c) (u : ℝ) :
    (𝓕⁻ (fun w : ℝ =>
      (1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3 : ℂ))) u =
      thirdOrderPerronStep c u :=
  fourierInv_thirdOrderPerronKernel c hc u

example (c : ℝ) (hc : 0 < c) (u : ℝ) :
    (∫ w : ℝ, Complex.exp (2 * Real.pi * (w : ℂ) * u * Complex.I) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) =
      thirdOrderPerronStep c u :=
  integral_thirdOrderPerronKernel_eq c hc u

example (c : ℝ) (hc : 0 < c) (u : ℝ) :
    (∫ w : ℝ, Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) =
      (((max u 0) ^ 2 / 2 : ℝ) : ℂ) :=
  thirdOrderPerron_eq_sq c hc u

example {c u w W : ℝ} (hW : 0 < W) (hw : W ≤ |w|) :
    ‖Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3‖ ≤
      Real.exp (c * u) / (8 * Real.pi ^ 3 * |w| ^ 3) :=
  norm_thirdOrderPerronKernel_le hW hw

example {c u W : ℝ} (hW : 0 < W) :
    ‖∫ w : ℝ in Ioi W,
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3‖ ≤
      Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) :=
  norm_integral_thirdOrderPerronKernel_Ioi_le hW

example {c u W : ℝ} (hW : 0 < W) :
    ‖∫ w : ℝ in Iic (-W),
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3‖ ≤
      Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) :=
  norm_integral_thirdOrderPerronKernel_Iic_le hW

example (c : ℝ) (hc : 0 < c) (u : ℝ) :
    Integrable (fun w : ℝ =>
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) :=
  integrable_thirdOrderPerronKernel c hc u

example {c u W : ℝ} (hc : 0 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in -W..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) -
        (((max u 0) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      Real.exp (c * u) / (8 * Real.pi ^ 3 * W ^ 2) :=
  norm_truncated_thirdOrderPerron_sub_sq_le hc hW

example {ι : Type*} (S : Finset ι) (a : ι → ℂ) (u : ι → ℝ)
    (c : ℝ) (hc : 0 < c) :
    (∫ w : ℝ, ∑ i ∈ S, a i *
      (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3)) =
      ∑ i ∈ S, a i * ((((max (u i) 0) ^ 2 / 2 : ℝ) : ℂ)) :=
  integral_finset_thirdOrderPerron_eq S a u c hc

example (x : ℝ) :
    secondSmoothedChebyshevPsi x =
      ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
        vonMangoldt n * (max (Real.log (x / n)) 0) ^ 2 / 2 := rfl

example (x c : ℝ) (hc : 0 < c) :
    (∫ w : ℝ,
      ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
        (vonMangoldt n : ℂ) *
          (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) *
              Real.log (x / n)) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3)) =
      (secondSmoothedChebyshevPsi x : ℂ) :=
  integral_vonMangoldt_thirdOrderPerron_eq x c hc

end PrimeNumberTheorem
