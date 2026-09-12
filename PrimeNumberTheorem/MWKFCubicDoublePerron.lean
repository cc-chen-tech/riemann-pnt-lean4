import HardyTheorem.SelbergPerronKernel
import PrimeNumberTheorem.MWKFCubicDiagonalLogKernel

open Complex MeasureTheory
open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Exact double Perron representation of the cubic diagonal forms

The logarithmic taper in the actual cubic Möbius coefficient is exactly the
full vertical Perron kernel `1 / s^2`.  This file records that equality before
any contour shift, and then substitutes it into the two reciprocal-LCM forms.

All sums are finite and both vertical integrals are absolutely convergent.
No Selberg--Perron asymptotic, zeta zero-free region, or off-diagonal estimate
is asserted here.
-/

/-- The real logarithmic Perron weight at the exact cubic cutoff. -/
noncomputable def cubicPerronLogWeight (T : ℝ) (n : ℕ) : ℝ :=
  Real.posLog
    (((n : ℝ) / (cubicMollifierLength T : ℝ))⁻¹)

/-- The normalized full vertical Perron integral for one natural index. -/
noncomputable def cubicPerronVerticalIntegral
    (T sigma : ℝ) (n : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ t : ℝ,
      (((cubicMollifierLength T : ℝ) : ℂ) ^
            ((sigma : ℂ) + t * I) /
          (n : ℂ) ^ ((sigma : ℂ) + t * I)) *
        (1 / (((sigma : ℂ) + t * I) ^ 2))

/-- The full vertical integral is exactly the real logarithmic cutoff. -/
theorem cubicPerronVerticalIntegral_eq_logWeight
    {T sigma : ℝ} {n : ℕ}
    (hsigma : 0 < sigma) (hN : 0 < cubicMollifierLength T)
    (hn : 0 < n) :
    cubicPerronVerticalIntegral T sigma n =
      (cubicPerronLogWeight T n : ℂ) := by
  simpa [cubicPerronVerticalIntegral, cubicPerronLogWeight,
    HardyTheorem.perronLogCutoff] using
      (HardyTheorem.perronKernel_ratio_integral_eq
        (sigma := sigma) (Y := (cubicMollifierLength T : ℝ))
        (n := (n : ℝ)) hsigma (by exact_mod_cast hN)
        (by exact_mod_cast hn))

private theorem cubicPerronLogWeight_eq_log_div
    {T : ℝ} {n : ℕ}
    (hN : 0 < cubicMollifierLength T) (hn : 0 < n)
    (hnN : n ≤ cubicMollifierLength T) :
    cubicPerronLogWeight T n =
      Real.log ((cubicMollifierLength T : ℝ) / (n : ℝ)) := by
  have h := HardyTheorem.perronLogCutoff_nat_div_eq_log
    (n := n) (Y := cubicMollifierLength T) hn hN hnN
  apply Complex.ofReal_injective
  simpa [cubicPerronLogWeight, HardyTheorem.perronLogCutoff] using h

/-- On the exact finite support, the actual cubic coefficient is the raw
Möbius value times the Perron logarithmic weight, divided by `log N`. -/
theorem cubicMollifierCoefficient_eq_moebius_mul_perronLogWeight_div
    {T : ℝ} {n : ℕ} (hN : 2 ≤ cubicMollifierLength T)
    (hn : n ∈ cubicMollifierSupport T) :
    cubicMollifierCoefficient T n =
      (ArithmeticFunction.moebius n : ℝ) * cubicPerronLogWeight T n /
        Real.log (cubicMollifierLength T : ℝ) := by
  have hnBox := Finset.mem_Icc.mp hn
  have hnPos : 0 < n := hnBox.1
  have hNPos : 0 < cubicMollifierLength T := by omega
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hNR : (cubicMollifierLength T : ℝ) ≠ 0 := by positivity
  have hlogN : Real.log (cubicMollifierLength T : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < cubicMollifierLength T by omega)))
  rw [cubicPerronLogWeight_eq_log_div hNPos hnPos hnBox.2,
    Real.log_div hNR hnR]
  unfold cubicMollifierCoefficient HardyTheorem.selbergMoebiusCoeff
    HardyTheorem.selbergMoebiusWeight
  field_simp [hlogN]

/-- The product of the two full Perron integrals with the raw Möbius and
reciprocal-LCM coefficients. -/
noncomputable def cubicDoublePerronQuadratic
    (T sigma : ℝ) : ℂ :=
  ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
    (ArithmeticFunction.moebius d : ℂ) *
      (ArithmeticFunction.moebius e : ℂ) *
      (Nat.lcm d e : ℂ)⁻¹ *
      cubicPerronVerticalIntegral T sigma d *
      cubicPerronVerticalIntegral T sigma e

/-- The same exact double Perron sum with the differentiated diagonal
logarithmic kernel retained term by term. -/
noncomputable def cubicDoublePerronLogKernel
    (T sigma c : ℝ) : ℂ :=
  ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
    (ArithmeticFunction.moebius d : ℂ) *
      (ArithmeticFunction.moebius e : ℂ) *
      (Nat.lcm d e : ℂ)⁻¹ *
      cubicPerronVerticalIntegral T sigma d *
      cubicPerronVerticalIntegral T sigma e *
      ((c + 2 * Real.log (Nat.gcd d e) - Real.log d - Real.log e : ℝ) : ℂ)

/-- Exact double Perron representation of the actual reciprocal-LCM
quadratic form. -/
theorem cubicReciprocalLcmQuadratic_eq_doublePerron
    {T sigma : ℝ} (hsigma : 0 < sigma)
    (hN : 2 ≤ cubicMollifierLength T) :
    (cubicReciprocalLcmQuadratic T : ℂ) =
      cubicDoublePerronQuadratic T sigma /
        (Real.log (cubicMollifierLength T : ℝ) : ℂ) ^ 2 := by
  have hNPos : 0 < cubicMollifierLength T := by omega
  unfold cubicReciprocalLcmQuadratic cubicDoublePerronQuadratic
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  rw [cubicPerronVerticalIntegral_eq_logWeight hsigma hNPos
      (Finset.mem_Icc.mp hd).1,
    cubicPerronVerticalIntegral_eq_logWeight hsigma hNPos
      (Finset.mem_Icc.mp he).1,
    cubicMollifierCoefficient_eq_moebius_mul_perronLogWeight_div hN hd,
    cubicMollifierCoefficient_eq_moebius_mul_perronLogWeight_div hN he]
  push_cast
  ring

/-- Exact double Perron representation of the differentiated logarithmic
reciprocal-LCM kernel. -/
theorem cubicReciprocalLcmLogKernel_eq_doublePerron
    {T sigma c : ℝ} (hsigma : 0 < sigma)
    (hN : 2 ≤ cubicMollifierLength T) :
    (cubicReciprocalLcmLogKernel T c : ℂ) =
      cubicDoublePerronLogKernel T sigma c /
        (Real.log (cubicMollifierLength T : ℝ) : ℂ) ^ 2 := by
  have hNPos : 0 < cubicMollifierLength T := by omega
  unfold cubicReciprocalLcmLogKernel cubicDoublePerronLogKernel
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  rw [cubicPerronVerticalIntegral_eq_logWeight hsigma hNPos
      (Finset.mem_Icc.mp hd).1,
    cubicPerronVerticalIntegral_eq_logWeight hsigma hNPos
      (Finset.mem_Icc.mp he).1,
    cubicMollifierCoefficient_eq_moebius_mul_perronLogWeight_div hN hd,
    cubicMollifierCoefficient_eq_moebius_mul_perronLogWeight_div hN he]
  push_cast
  ring

end PrimeNumberTheorem.MWKFCubic
