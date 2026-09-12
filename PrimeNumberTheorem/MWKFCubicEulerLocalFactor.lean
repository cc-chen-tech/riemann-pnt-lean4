import PrimeNumberTheorem.MWKFCubicDoublePerron

open Complex

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The exact prime-local factor of the cubic Möbius--LCM series

This file computes the four squarefree prime-power contributions in the
three-variable Dirichlet series used by the Selberg--Perron evaluation of the
cubic diagonal.  It then proves the exact algebraic extraction of the three
local zeta factors.  No infinite Euler product or convergence claim occurs
here.
-/

/-- One pair contribution in the three-variable Möbius--LCM Dirichlet
series.  This is stated for arbitrary positive natural indices so that the
prime-local calculation below is visibly a specialization of the original
arithmetic kernel. -/
noncomputable def mwkfPrimePowerPairTerm
    (s t w : ℂ) (d e : ℕ) : ℂ :=
  (ArithmeticFunction.moebius d : ℂ) *
    (ArithmeticFunction.moebius e : ℂ) *
    (Nat.lcm d e : ℂ)⁻¹ *
    ((d : ℂ) ^ s)⁻¹ *
    ((e : ℂ) ^ t)⁻¹ *
    ((((Nat.gcd d e : ℂ) ^ 2) / ((d : ℂ) * (e : ℂ))) ^ w)

/-- The four squarefree exponent choices at one prime. -/
noncomputable def mwkfPrimePowerPairLocalSum
    (p : ℕ) (s t w : ℂ) : ℂ :=
  mwkfPrimePowerPairTerm s t w 1 1 +
    mwkfPrimePowerPairTerm s t w p 1 +
    mwkfPrimePowerPairTerm s t w 1 p +
    mwkfPrimePowerPairTerm s t w p p

/-- The separated-power form of the expected local factor.  Keeping the
three inverse powers separate avoids any branch convention in the local
calculation; for positive primes it is the usual
`1 - p^(-1-s-w) - p^(-1-t-w) + p^(-1-s-t)`. -/
noncomputable def mwkfPrimeLocalFactor
    (p : ℕ) (s t w : ℂ) : ℂ :=
  1 - (p : ℂ)⁻¹ * ((p : ℂ) ^ s)⁻¹ * ((p : ℂ)⁻¹ ^ w) -
      (p : ℂ)⁻¹ * ((p : ℂ) ^ t)⁻¹ * ((p : ℂ)⁻¹ ^ w) +
    (p : ℂ)⁻¹ * ((p : ℂ) ^ s)⁻¹ * ((p : ℂ) ^ t)⁻¹

/-- The same local factor in the combined-exponent notation used by the
Selberg--Perron Euler product. -/
noncomputable def mwkfPrimeLocalFactorStandard
    (p : ℕ) (s t w : ℂ) : ℂ :=
  1 - (p : ℂ) ^ (-(1 + s + w)) -
      (p : ℂ) ^ (-(1 + t + w)) +
    (p : ℂ) ^ (-(1 + s + t))

/-- For a positive prime base, the branch-safe separated-power factor is
exactly the usual combined-exponent local factor. -/
theorem mwkfPrimeLocalFactor_eq_standard
    {p : ℕ} (hp : p.Prime) (s t w : ℂ) :
    mwkfPrimeLocalFactor p s t w =
      mwkfPrimeLocalFactorStandard p s t w := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hinvCpow (u : ℂ) : ((p : ℂ)⁻¹) ^ u = ((p : ℂ) ^ u)⁻¹ := by
    simpa using
      (Complex.inv_cpow_ofReal_nonneg (a := (p : ℝ)) (Nat.cast_nonneg p) u)
  have hcombine (u v : ℂ) :
      (p : ℂ)⁻¹ * ((p : ℂ) ^ u)⁻¹ * ((p : ℂ) ^ v)⁻¹ =
        (p : ℂ) ^ (-(1 + u + v)) := by
    rw [Complex.cpow_neg, Complex.cpow_add (1 + u) v hp0,
      Complex.cpow_add 1 u hp0, Complex.cpow_one]
    simp only [mul_inv_rev]
    ring
  unfold mwkfPrimeLocalFactor mwkfPrimeLocalFactorStandard
  rw [hinvCpow w, hcombine s w, hcombine t w, hcombine s t]

/-- Direct computation of the four prime-power cases gives the local Euler
factor of the Möbius--LCM series. -/
theorem mwkfPrimePowerPairLocalSum_eq_factor
    {p : ℕ} (hp : p.Prime) (s t w : ℂ) :
    mwkfPrimePowerPairLocalSum p s t w =
      mwkfPrimeLocalFactor p s t w := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [mwkfPrimePowerPairLocalSum, mwkfPrimePowerPairTerm,
    mwkfPrimePowerPairTerm, mwkfPrimePowerPairTerm,
    mwkfPrimePowerPairTerm]
  simp only [ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp, Int.cast_one,
    Int.cast_neg, Nat.lcm_one_left, Nat.lcm_one_right, Nat.lcm_self,
    Nat.gcd_one_left, Nat.gcd_one_right, Nat.gcd_self, Nat.cast_one,
    one_mul, one_pow, inv_one, mul_one, neg_mul, one_div]
  have hratio : (p : ℂ) ^ 2 / ((p : ℂ) * (p : ℂ)) = 1 := by
    field_simp [hp0]
  rw [hratio]
  simp only [Complex.one_cpow, inv_one, mul_one]
  unfold mwkfPrimeLocalFactor
  ring

/-- The direct four-state calculation in the standard combined-exponent
notation of the global Euler product. -/
theorem mwkfPrimePowerPairLocalSum_eq_standard
    {p : ℕ} (hp : p.Prime) (s t w : ℂ) :
    mwkfPrimePowerPairLocalSum p s t w =
      mwkfPrimeLocalFactorStandard p s t w := by
  rw [mwkfPrimePowerPairLocalSum_eq_factor hp,
    mwkfPrimeLocalFactor_eq_standard hp]

/-- The correction factor left after extracting the two reciprocal-zeta
factors and the numerator zeta factor prime by prime. -/
noncomputable def mwkfPrimeCorrectionFactor
    (p : ℕ) (s t w : ℂ) : ℂ :=
  mwkfPrimeLocalFactorStandard p s t w *
      (1 - (p : ℂ) ^ (-(1 + s + t))) /
    ((1 - (p : ℂ) ^ (-(1 + s + w))) *
      (1 - (p : ℂ) ^ (-(1 + t + w))))

/-- Exact local algebra for
`F = zeta(1+s+t)/(zeta(1+s+w) zeta(1+t+w)) * H`.
The nonvanishing hypotheses are precisely the three local denominators that
are divided by in this identity. -/
theorem mwkfPrimeLocalFactor_eq_zetaRatio_mul_correction
    {p : ℕ} {s t w : ℂ}
    (hp : p.Prime)
    (hsw : 1 - (p : ℂ) ^ (-(1 + s + w)) ≠ 0)
    (htw : 1 - (p : ℂ) ^ (-(1 + t + w)) ≠ 0)
    (hst : 1 - (p : ℂ) ^ (-(1 + s + t)) ≠ 0) :
    mwkfPrimeLocalFactor p s t w =
      ((1 - (p : ℂ) ^ (-(1 + s + w))) *
          (1 - (p : ℂ) ^ (-(1 + t + w))) /
        (1 - (p : ℂ) ^ (-(1 + s + t)))) *
      mwkfPrimeCorrectionFactor p s t w := by
  rw [mwkfPrimeLocalFactor_eq_standard hp]
  let A : ℂ := (p : ℂ) ^ (-(1 + s + w))
  let B : ℂ := (p : ℂ) ^ (-(1 + t + w))
  let C : ℂ := (p : ℂ) ^ (-(1 + s + t))
  let L : ℂ := mwkfPrimeLocalFactorStandard p s t w
  have hA : 1 - A ≠ 0 := by simpa [A] using hsw
  have hB : 1 - B ≠ 0 := by simpa [B] using htw
  have hC : 1 - C ≠ 0 := by simpa [C] using hst
  have hAB : (1 - A) * (1 - B) ≠ 0 := mul_ne_zero hA hB
  have hprod : (1 - C) * ((1 - A) * (1 - B)) ≠ 0 :=
    mul_ne_zero hC hAB
  change L = ((1 - A) * (1 - B) / (1 - C)) *
    (L * (1 - C) / ((1 - A) * (1 - B)))
  rw [div_mul_div_comm]
  rw [show (1 - A) * (1 - B) * (L * (1 - C)) =
      L * ((1 - C) * ((1 - A) * (1 - B))) by ring]
  rw [mul_div_cancel_right₀ L hprod]

end PrimeNumberTheorem.MWKFCubic
