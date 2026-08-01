import PrimeNumberTheorem.QPowerDetectorMass

open Polynomial
open scoped BigOperators

namespace PrimeNumberTheorem
namespace PrimeSideDetector

noncomputable section

/-!
# Scale barrier for finite q-power detectors

A real polynomial detector normalized to have response one at `s0` must
carry a definite weighted coefficient mass at the main-pole node.  If it
also cancels the main pole, exactly half of that mass is negative.  When the
largest q-power in the detector remains below the observation scale `x`, the
resulting elementary prime-side loss is already at least `x ^ re(s0) / 2`.

This is a no-go theorem for estimates which bound the negative coefficients
only by positivity of the von Mangoldt sum.  It does not rule out a signed
correlation estimate, smoothing cancellation, or a different arithmetic
detector.
-/

/-- Polynomial evaluation at a complex point is bounded by the coefficient
`L1` mass weighted at the norm of that point. -/
theorem norm_evalRealPolynomial_le_polynomialWeightedL1At_norm
    (p : Polynomial Real) (z : Complex) :
    ‖evalRealPolynomial p z‖ ≤ polynomialWeightedL1At ‖z‖ p := by
  unfold evalRealPolynomial polynomialWeightedL1At
  rw [← Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_sum]
  calc
    ‖∑ k ∈ p.support, (p.coeff k : Complex) * z ^ k‖ ≤
        ∑ k ∈ p.support, ‖(p.coeff k : Complex) * z ^ k‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ p.support, |p.coeff k| * ‖z‖ ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- Changing a nonnegative coefficient weight from `r` to `R` costs at most
the `N`-th power of `R / r` for a polynomial of degree at most `N`. -/
theorem polynomialWeightedL1At_le_ratio_pow_of_natDegree_le
    {r R : Real} (p : Polynomial Real) (N : Nat)
    (hr : 0 < r) (hrR : r ≤ R) (hdeg : p.natDegree ≤ N) :
    polynomialWeightedL1At R p ≤
      (R / r) ^ N * polynomialWeightedL1At r p := by
  have hratio : 1 ≤ R / r := (le_div_iff₀ hr).2 (by simpa using hrR)
  have hRfactor : R = (R / r) * r := by
    field_simp
  unfold polynomialWeightedL1At
  calc
    (∑ k ∈ p.support, |p.coeff k| * R ^ k) ≤
        ∑ k ∈ p.support,
          (R / r) ^ N * (|p.coeff k| * r ^ k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN : k ≤ N :=
        (Polynomial.le_natDegree_of_ne_zero
          (Polynomial.mem_support_iff.mp hk)).trans hdeg
      have hpow : (R / r) ^ k ≤ (R / r) ^ N :=
        pow_le_pow_right₀ hratio hkN
      have hRpow : R ^ k = (R / r) ^ k * r ^ k := by
        calc
          R ^ k = ((R / r) * r) ^ k :=
            congrArg (fun u : Real => u ^ k) hRfactor
          _ = (R / r) ^ k * r ^ k := mul_pow _ _ _
      rw [hRpow]
      calc
        |p.coeff k| * ((R / r) ^ k * r ^ k) =
            (R / r) ^ k * (|p.coeff k| * r ^ k) := by ring
        _ ≤ (R / r) ^ N * (|p.coeff k| * r ^ k) :=
          mul_le_mul_of_nonneg_right hpow
            (mul_nonneg (abs_nonneg _) (pow_nonneg hr.le _))
    _ = (R / r) ^ N *
        ∑ k ∈ p.support, |p.coeff k| * r ^ k := by
      rw [Finset.mul_sum]

/-- Exact modulus of the q-power node. -/
theorem norm_qPowerNode {q : Nat} (s : Complex) (hq : 0 < q) :
    ‖qPowerNode q s‖ = (q : Real) ^ (-s.re) := by
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  change
    ‖Complex.exp
        (-(s * (((Real.log (q : Real)) : Real) : Complex)))‖ =
      (q : Real) ^ (-s.re)
  rw [Complex.norm_exp, Real.rpow_def_of_pos hqReal]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- Unit target response forces a weighted `L1` mass at the main-pole node.
The result is independent of how the polynomial was constructed. -/
theorem qPowerDetector_weightedL1At_one_lower
    {q N : Nat} {p : Polynomial Real} {s0 : Complex}
    (hq : 1 < q) (hbeta : s0.re ≤ 1) (hdeg : p.natDegree ≤ N)
    (htarget : qPowerDetector q p s0 = 1) :
    (((q : Real)⁻¹ / ‖qPowerNode q s0‖) ^ N) ≤
      polynomialWeightedL1At ((q : Real)⁻¹) p := by
  have hqNat : 0 < q := Nat.zero_lt_of_lt hq
  have hqReal : (1 : Real) < q := by exact_mod_cast hq
  have hqPos : (0 : Real) < q := lt_trans zero_lt_one hqReal
  have hr : (0 : Real) < (q : Real)⁻¹ := inv_pos.mpr hqPos
  have hR : 0 < ‖qPowerNode q s0‖ := by
    rw [norm_qPowerNode s0 hqNat]
    exact Real.rpow_pos_of_pos hqPos _
  have hrR : (q : Real)⁻¹ ≤ ‖qPowerNode q s0‖ := by
    rw [norm_qPowerNode s0 hqNat, Real.rpow_def_of_pos hqPos]
    calc
      (q : Real)⁻¹ = Real.exp (-Real.log (q : Real)) := by
        rw [Real.exp_neg, Real.exp_log hqPos]
      _ ≤ Real.exp (Real.log (q : Real) * (-s0.re)) := by
        apply Real.exp_le_exp.mpr
        have hlog : 0 ≤ Real.log (q : Real) := (Real.log_pos hqReal).le
        nlinarith
  have htargetNorm :
      1 ≤ polynomialWeightedL1At ‖qPowerNode q s0‖ p := by
    have hbound :=
      norm_evalRealPolynomial_le_polynomialWeightedL1At_norm
        p (qPowerNode q s0)
    rw [← qPowerDetector_eq_polynomial_eval] at hbound
    simpa [htarget] using hbound
  have hscaled :=
    polynomialWeightedL1At_le_ratio_pow_of_natDegree_le
      p N hr hrR hdeg
  have hproduct :
      1 ≤
        (‖qPowerNode q s0‖ / (q : Real)⁻¹) ^ N *
          polynomialWeightedL1At ((q : Real)⁻¹) p :=
    htargetNorm.trans hscaled
  have hfactor :
      0 < (‖qPowerNode q s0‖ / (q : Real)⁻¹) ^ N := by
    positivity
  have hdiv :
      1 / (‖qPowerNode q s0‖ / (q : Real)⁻¹) ^ N ≤
        polynomialWeightedL1At ((q : Real)⁻¹) p :=
    (div_le_iff₀ hfactor).2 (by simpa [mul_comm] using hproduct)
  have hratioInv :
      (((q : Real)⁻¹ / ‖qPowerNode q s0‖) ^ N) =
        1 / (‖qPowerNode q s0‖ / (q : Real)⁻¹) ^ N := by
    rw [← inv_div, inv_pow, one_div]
  rw [hratioInv]
  exact hdiv

private theorem evalRealPolynomial_ofReal_eq
    (p : Polynomial Real) (r : Real) :
    evalRealPolynomial p r = p.eval r := by
  rw [evalRealPolynomial, ← Polynomial.eval₂_eq_eval_map]
  change p.eval₂ Complex.ofRealHom (Complex.ofRealHom r) =
    Complex.ofRealHom (p.eval r)
  rw [Polynomial.eval₂_at_apply]

/-- If the detector also cancels the main pole, one half of the forced
weighted mass is necessarily negative. -/
theorem qPowerDetector_negativeMassAt_one_lower
    {q N : Nat} {p : Polynomial Real} {s0 : Complex}
    (hq : 1 < q) (hbeta : s0.re ≤ 1) (hdeg : p.natDegree ≤ N)
    (htarget : qPowerDetector q p s0 = 1)
    (hmain : qPowerDetector q p 1 = 0) :
    (1 / 2 : Real) *
        (((q : Real)⁻¹ / ‖qPowerNode q s0‖) ^ N) ≤
      polynomialNegativeMassAt ((q : Real)⁻¹) p := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hq)
  have hzero : p.eval ((q : Real)⁻¹) = 0 := by
    have hmain' :
        evalRealPolynomial p (((q : Real)⁻¹ : Real) : Complex) = 0 := by
      rw [qPowerDetector, qPowerNode_one hq0] at hmain
      simpa using hmain
    rw [evalRealPolynomial_ofReal_eq] at hmain'
    exact_mod_cast hmain'
  have hhalf := polynomialNegativeMassAt_eq_half_weightedL1At
    (show (0 : Real) ≤ (q : Real)⁻¹ by positivity) hzero
  have hlower := qPowerDetector_weightedL1At_one_lower
    hq hbeta hdeg htarget
  rw [hhalf]
  nlinarith

private theorem qPower_support_ratio_pow_eq
    {q N : Nat} {s0 : Complex} (hq : 1 < q) :
    (((q : Real)⁻¹ / ‖qPowerNode q s0‖) ^ N) =
      ((q : Real) ^ N) ^ (s0.re - 1) := by
  have hqNat : 0 < q := Nat.zero_lt_of_lt hq
  have hqReal : (1 : Real) < q := by exact_mod_cast hq
  have hqPos : (0 : Real) < q := lt_trans zero_lt_one hqReal
  rw [norm_qPowerNode s0 hqNat, Real.rpow_def_of_pos hqPos]
  have hratio :
      (q : Real)⁻¹ /
          Real.exp (Real.log (q : Real) * (-s0.re)) =
        Real.exp ((s0.re - 1) * Real.log (q : Real)) := by
    calc
      (q : Real)⁻¹ /
            Real.exp (Real.log (q : Real) * (-s0.re)) =
          Real.exp (-Real.log (q : Real)) /
            Real.exp (Real.log (q : Real) * (-s0.re)) := by
        rw [Real.exp_neg, Real.exp_log hqPos]
      _ = Real.exp
          (-Real.log (q : Real) -
            Real.log (q : Real) * (-s0.re)) := by
        rw [Real.exp_sub]
      _ = Real.exp ((s0.re - 1) * Real.log (q : Real)) := by
        congr 1
        ring
  rw [hratio, ← Real.exp_nat_mul]
  rw [Real.rpow_def_of_pos (pow_pos hqPos N), Real.log_pow]
  congr 1
  ring

/-- A support-compatible q-power detector cannot beat the target scale by
bounding its negative coefficients only with positivity.  If `q^N ≤ x`, the
elementary loss `x * negativeMass` is already at least `x^re(s0) / 2`. -/
theorem qPowerDetector_supportCompatible_negativeMass_loss
    {q N : Nat} {p : Polynomial Real} {s0 : Complex} {x : Real}
    (hq : 1 < q) (hbeta1 : s0.re < 1)
    (hdeg : p.natDegree ≤ N)
    (htarget : qPowerDetector q p s0 = 1)
    (hmain : qPowerDetector q p 1 = 0)
    (hx : 0 < x) (hsupport : (q : Real) ^ N ≤ x) :
    x ^ s0.re / 2 ≤
      x * polynomialNegativeMassAt ((q : Real)⁻¹) p := by
  have hqReal : (0 : Real) < q := by
    exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hQpos : 0 < (q : Real) ^ N := pow_pos hqReal N
  have hexponent : s0.re - 1 ≤ 0 := by linarith
  have hscale :
      x ^ (s0.re - 1) ≤ ((q : Real) ^ N) ^ (s0.re - 1) :=
    Real.rpow_le_rpow_of_nonpos hQpos hsupport hexponent
  have hmass := qPowerDetector_negativeMassAt_one_lower
    hq hbeta1.le hdeg htarget hmain
  rw [qPower_support_ratio_pow_eq hq] at hmass
  have hscaledMass :
      x * (x ^ (s0.re - 1) / 2) ≤
        x * polynomialNegativeMassAt ((q : Real)⁻¹) p := by
    apply mul_le_mul_of_nonneg_left
    · nlinarith
    · exact hx.le
  calc
    x ^ s0.re / 2 = x * (x ^ (s0.re - 1) / 2) := by
      rw [show s0.re = (s0.re - 1) + 1 by ring,
        Real.rpow_add hx, Real.rpow_one]
      ring_nf
    _ ≤ x * polynomialNegativeMassAt ((q : Real)⁻¹) p := hscaledMass

end

end PrimeSideDetector
end PrimeNumberTheorem
