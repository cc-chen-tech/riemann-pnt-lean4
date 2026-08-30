import HardyTheorem.ConreyCoprimeMobiusPerron
import HardyTheorem.SelbergS12RightLine
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open Complex MeasureTheory Set Filter
open scoped BigOperators Interval ArithmeticFunction.zeta LSeries.notation

namespace HardyTheorem

/-! Absolute convergence bounds the whole coprime inverse on the right line.
The two omitted tails and the normalized finite-line error are uniform in the
modulus; no separately estimated finite Euler factor is needed here. -/

theorem norm_conreyCoprimeMobiusEulerInverse_le {d : ℕ} [NeZero d] {s : ℂ}
    (hs : 1 < s.re) :
    ‖(riemannZeta s * ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-s)))⁻¹‖ ≤
      s.re / (s.re - 1) := by
  rw [← LSeries_conreyCoprimeMobiusCoeff_eq hs]
  have hf := LSeriesSummable_conreyCoprimeMobiusCoeff (d := d) hs
  have hz : LSeriesSummable ↗ζ s := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hsr : 1 < ((s.re : ℂ)).re := by simpa using hs
  have hzr : LSeriesSummable ↗ζ (s.re : ℂ) :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hsr
  have hterm (n : ℕ) :
      ‖LSeries.term (conreyCoprimeMobiusCoeff d) s n‖ ≤ ‖LSeries.term ↗ζ s n‖ := by
    apply LSeries.norm_term_le
    rcases eq_or_ne n 0 with rfl | hn
    · simp [conreyCoprimeMobiusCoeff_eq]
    · rw [conreyCoprimeMobiusCoeff_eq]
      split_ifs
      · simpa [hn, ArithmeticFunction.zeta_apply] using
          (show ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 by
            rw [Complex.norm_intCast]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n))
      · simp [hn, ArithmeticFunction.zeta_apply]
  calc
    ‖L (conreyCoprimeMobiusCoeff d) s‖ ≤
        ∑' n, ‖LSeries.term (conreyCoprimeMobiusCoeff d) s n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, ‖LSeries.term ↗ζ s n‖ := hf.norm.tsum_le_tsum hterm hz.norm
    _ = (L ↗ζ (s.re : ℂ)).re := by
      rw [LSeries, re_tsum hzr]
      apply tsum_congr
      intro n
      calc
        ‖LSeries.term ↗ζ s n‖ = ‖LSeries.term ↗ζ (s.re : ℂ) n‖ := by
          simp [LSeries.norm_term_eq]
        _ = (LSeries.term ↗ζ (s.re : ℂ) n).re := by
          rcases eq_or_ne n 0 with rfl | hn
          · simp [LSeries.term]
          · rw [LSeries.term_of_ne_zero hn]
            simp only [hn, ArithmeticFunction.zeta_apply, if_false]
            have hpow : (n : ℂ) ^ (s.re : ℂ) = (((n : ℝ) ^ s.re : ℝ) : ℂ) :=
              (Complex.ofReal_cpow (Nat.cast_nonneg n) s.re).symm
            rw [hpow]
            simp
            positivity
    _ = (riemannZeta (s.re : ℂ)).re := by
      rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hsr]
    _ ≤ s.re / (s.re - 1) := ZeroFreeRegion.riemannZeta_re_le_sigma_div_sub s.re hs

private theorem integral_Ioi_norm_le_inverse_square {f : ℝ → ℂ} {A K : ℝ}
    (hK : 0 < K) (hf : ∀ t ∈ Ioi K, ‖f t‖ ≤ A / t ^ 2) :
    (∫ t in Ioi K, ‖f t‖) ≤ A / K := by
  have hi : IntegrableOn (fun t : ℝ => A * t ^ (-2 : ℝ)) (Ioi K) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hK).const_mul A
  calc
    _ ≤ ∫ t in Ioi K, A * t ^ (-2 : ℝ) := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa [Real.rpow_neg (hK.trans ht).le, Real.rpow_two, div_eq_mul_inv] using hf t ht
    _ = A / K := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hK]
      norm_num [Real.rpow_neg_one, div_eq_mul_inv]

private theorem norm_conreyCoprimeMobiusPerronIntegrand_le {d : ℕ} [NeZero d]
    (α : ℂ) {X u t : ℝ} (hX : 0 < X) (hα : 0 < α.re + u) (ht : t ≠ 0) :
    ‖(X : ℂ) ^ selbergPerronLine u t *
      (riemannZeta (1 + α + selbergPerronLine u t) *
        ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + selbergPerronLine u t))))⁻¹ *
      (1 / selbergPerronLine u t ^ 2)‖ ≤
      X ^ u * ((1 + α.re + u) / (α.re + u)) / t ^ 2 := by
  have hre : (selbergPerronLine u t).re = u := by simp [selbergPerronLine]
  have hs : 1 < (1 + α + selbergPerronLine u t).re := by
    simp only [add_re, one_re, hre]
    linarith
  have hE := norm_conreyCoprimeMobiusEulerInverse_le (d := d) hs
  simp only [add_re, one_re, hre] at hE
  have hden : 1 + α.re + u - 1 = α.re + u := by ring
  rw [hden] at hE
  have hk : ‖(1 : ℂ) / selbergPerronLine u t ^ 2‖ ≤ 1 / t ^ 2 := by
    have hsq : t ^ 2 ≤ ‖selbergPerronLine u t‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [selbergPerronLine, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, sub_self, add_zero, add_im, mul_im, zero_add, mul_one]
      nlinarith only [sq_nonneg u]
    rw [norm_div, norm_one, norm_pow]
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_ne_zero ht) hsq
  have hnum : 0 < 1 + α.re + u := by linarith
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, hre]
  calc
    _ ≤ X ^ u * ((1 + α.re + u) / (α.re + u)) * (1 / t ^ 2) := by
      gcongr
    _ = _ := by ring

theorem conrey_coprime_mobius_perron_tail_bound {d : ℕ} [NeZero d] (α : ℂ)
    {X u K : ℝ} (hX : 0 < X) (_hu : 0 < u) (hα : 0 < α.re + u) (hK : 0 < K) :
    let f : ℝ → ℂ := fun t => (X : ℂ) ^ selbergPerronLine u t *
      (riemannZeta (1 + α + selbergPerronLine u t) *
        ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + selbergPerronLine u t))))⁻¹ *
      (1 / selbergPerronLine u t ^ 2)
    (∫ t in Ioi K, ‖f t‖) ≤ X ^ u * ((1 + α.re + u) / (α.re + u)) / K ∧
    (∫ t in Iic (-K), ‖f t‖) ≤ X ^ u * ((1 + α.re + u) / (α.re + u)) / K := by
  dsimp only
  constructor
  · apply integral_Ioi_norm_le_inverse_square hK
    intro t ht
    exact norm_conreyCoprimeMobiusPerronIntegrand_le α hX hα (hK.trans ht).ne'
  · rw [← integral_comp_neg_Ioi]
    apply integral_Ioi_norm_le_inverse_square hK
    intro t ht
    simpa only [neg_sq] using
      norm_conreyCoprimeMobiusPerronIntegrand_le (d := d) α hX hα (neg_ne_zero.mpr (hK.trans ht).ne')

theorem conrey_coprime_mobius_log_perron_truncated {d : ℕ} [NeZero d] (α : ℂ)
    {X u K : ℝ} (hX : 0 < X) (hu : 0 < u) (hα : 0 < α.re + u) (hK : 0 < K) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        (if n.Coprime d then (ArithmeticFunction.moebius n : ℂ) else 0) *
          (n : ℂ) ^ (-(1 + α)) * (Real.log (X / (n : ℝ)) : ℂ)) -
      (1 / (2 * Real.pi) : ℂ) *
        (∫ t in (-K)..K, (X : ℂ) ^ selbergPerronLine u t *
          (riemannZeta (1 + α + selbergPerronLine u t) *
            ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + selbergPerronLine u t))))⁻¹ *
          (1 / selbergPerronLine u t ^ 2))‖ ≤
        X ^ u * ((1 + α.re + u) / (α.re + u)) / (Real.pi * K) := by
  let f : ℝ → ℂ := fun t => (X : ℂ) ^ selbergPerronLine u t *
    (riemannZeta (1 + α + selbergPerronLine u t) *
      ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + selbergPerronLine u t))))⁻¹ *
    (1 / selbergPerronLine u t ^ 2)
  let A := X ^ u * ((1 + α.re + u) / (α.re + u))
  obtain ⟨hi, heq⟩ := conrey_coprime_mobius_log_perron (d := d) α hX hu hα
  change Integrable f at hi
  rw [← heq, ← mul_sub]
  change ‖(1 / (2 * Real.pi) : ℂ) * ((∫ t, f t) - ∫ t in (-K)..K, f t)‖ ≤ _
  have hsplit : (∫ t, f t) - (∫ t in (-K)..K, f t) =
      (∫ t in Iic (-K), f t) + ∫ t in Ioi K, f t := by
    have h₁ := intervalIntegral.integral_Iic_add_Ioi (hi.integrableOn (s := Iic (-K)))
      (hi.integrableOn (s := Ioi (-K)))
    have h₂ := intervalIntegral.integral_interval_add_Ioi (hi.integrableOn (s := Ioi (-K)))
      (hi.integrableOn (s := Ioi K))
    rw [← h₁, ← h₂]
    ring
  have ht := conrey_coprime_mobius_perron_tail_bound (d := d) α hX hu hα hK
  change (∫ t in Ioi K, ‖f t‖) ≤ A / K ∧ (∫ t in Iic (-K), ‖f t‖) ≤ A / K at ht
  have htail : ‖(∫ t, f t) - ∫ t in (-K)..K, f t‖ ≤ 2 * A / K := by
    rw [hsplit]
    calc
      _ ≤ ‖∫ t in Iic (-K), f t‖ + ‖∫ t in Ioi K, f t‖ := norm_add_le _ _
      _ ≤ (∫ t in Iic (-K), ‖f t‖) + ∫ t in Ioi K, ‖f t‖ :=
        add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _)
      _ ≤ A / K + A / K := add_le_add ht.2 ht.1
      _ = _ := by ring
  rw [norm_mul]
  have hnorm : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    norm_cast
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (2 * A / K) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by dsimp [A]; field_simp

end HardyTheorem
