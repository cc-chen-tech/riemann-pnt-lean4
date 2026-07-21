import HardyTheorem.SelbergShortLowRangeArithmetic

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Prime coefficients obstruct the naive short Selberg error estimate

For the linear Moebius mollifier, the all-negative-frequency polynomial
`P_N M_X^2` does not approximate the constant function in square mean.  The
exact prime coefficient below records the elementary obstruction without
asserting any asymptotic prime-sum estimate.
-/

/-- At a prime in the complete low range, the unnormalised coefficient of
`P_N M_X^2` is `-1 + 2 log p / log X`.  In particular, the second mollifier
copy does not create the cancellation that one would obtain from a genuine
square-root mollifier. -/
theorem selbergShortCollectedDirichletConvolution_eq_primeCoefficient
    {N X p : ℕ} (hp : p.Prime) (hpN : p ≤ N) (hpX : p ≤ X) :
    selbergShortCollectedDirichletConvolution N X p =
      -1 + 2 * Real.log p / Real.log X := by
  rw [selbergShortCollectedDirichletConvolution_eq_lowRange
    hp.one_lt hpN hpX]
  unfold selbergShortLowRangeVonMangoldtConvolution
  rw [hp.divisors]
  simp [selbergMoebiusCoeff, selbergMoebiusWeight,
    ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.vonMangoldt_apply_prime hp,
    Nat.div_self hp.pos]
  ring

/-- The corresponding critical-line coefficient retains the common
`1 / sqrt p` normalisation. -/
theorem selbergShortDirichletCollectedCoeff_eq_primeCoefficient
    {N X p : ℕ} (hp : p.Prime) (hpN : p ≤ N) (hpX : p ≤ X) :
    selbergShortDirichletCollectedCoeff N X p =
      ((-1 + 2 * Real.log p / Real.log X : ℝ) : ℂ) *
        (Real.sqrt (p : ℝ) : ℂ)⁻¹ := by
  rw [selbergShortDirichletCollectedCoeff_eq_convolution,
    selbergShortCollectedDirichletConvolution_eq_primeCoefficient hp hpN hpX]

/-- Primes with `p^4 <= X` already have an unnormalised coefficient at most
`-1/2`.  This finite statement is the local obstruction behind the divergent
prime diagonal in the naive square-mean strategy. -/
theorem selbergShortCollectedDirichletConvolution_prime_le_neg_half
    {N X p : ℕ} (hX : 2 ≤ X) (hp : p.Prime) (hpN : p ≤ N)
    (hp4X : p ^ 4 ≤ X) :
    selbergShortCollectedDirichletConvolution N X p ≤ -(1 / 2 : ℝ) := by
  have hpX : p ≤ X := by
    calc
      p ≤ p ^ 4 := by
        exact le_self_pow hp.one_le (by norm_num)
      _ ≤ X := hp4X
  rw [selbergShortCollectedDirichletConvolution_eq_primeCoefficient hp hpN hpX]
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hcast : ((p ^ 4 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hp4X
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogpow : Real.log ((p ^ 4 : ℕ) : ℝ) = 4 * Real.log p := by
    norm_num [Nat.cast_pow, Real.log_pow]
  have hlogle : 4 * Real.log p ≤ Real.log X := by
    rw [← hlogpow]
    exact Real.log_le_log (by exact_mod_cast pow_pos hp.pos 4) hcast
  have hratio : 2 * Real.log p / Real.log X ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hlogX).2
    nlinarith
  linarith

end HardyTheorem
