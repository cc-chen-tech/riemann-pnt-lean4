import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Real.Basic

namespace HardyTheorem

/-!
# The local square-root zeta mollifier

Selberg's positive-proportion argument uses the Euler-factor coefficients of
`ζ(s)⁻¹ᐟ²`, rather than the Möbius coefficients of `ζ(s)⁻¹`.  The local
generating series is `(1 - X)^(1/2)`.  This file constructs that formal power
series and proves the square identity needed to globalize its coefficients.
-/

/-- The formal power series `(1 - X)^(1/2)`. -/
noncomputable def selbergSqrtZetaEulerFactor : PowerSeries ℝ :=
  PowerSeries.rescale (-1 : ℝ)
    (PowerSeries.binomialSeries ℝ (1 / 2 : ℝ))

/-- The coefficient of `X^k` in `(1 - X)^(1/2)`. -/
noncomputable def selbergSqrtZetaLocalCoeff (k : ℕ) : ℝ :=
  PowerSeries.coeff k selbergSqrtZetaEulerFactor

@[simp] theorem selbergSqrtZetaLocalCoeff_zero :
    selbergSqrtZetaLocalCoeff 0 = 1 := by
  simp [selbergSqrtZetaLocalCoeff, selbergSqrtZetaEulerFactor]

@[simp] theorem selbergSqrtZetaLocalCoeff_one :
    selbergSqrtZetaLocalCoeff 1 = -(1 / 2 : ℝ) := by
  simp [selbergSqrtZetaLocalCoeff, selbergSqrtZetaEulerFactor]

/-- Squaring the local Euler factor recovers the Möbius Euler factor. -/
theorem selbergSqrtZetaEulerFactor_sq :
    selbergSqrtZetaEulerFactor * selbergSqrtZetaEulerFactor =
      1 - PowerSeries.X := by
  rw [selbergSqrtZetaEulerFactor, ← map_mul,
    ← PowerSeries.binomialSeries_add]
  norm_num
  rw [show PowerSeries.binomialSeries ℝ (1 : ℝ) =
      (1 + PowerSeries.X) ^ (1 : ℕ) by
        simpa using (PowerSeries.binomialSeries_nat (A := ℝ) 1)]
  simp [sub_eq_add_neg]

/-- The self-convolution of the local coefficients is `1, -1, 0, ...`. -/
theorem sum_antidiagonal_selbergSqrtZetaLocalCoeff_mul
    (k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
        selbergSqrtZetaLocalCoeff ij.1 *
          selbergSqrtZetaLocalCoeff ij.2) =
      if k = 0 then 1 else if k = 1 then -1 else 0 := by
  unfold selbergSqrtZetaLocalCoeff
  rw [← PowerSeries.coeff_mul, selbergSqrtZetaEulerFactor_sq]
  by_cases hk0 : k = 0
  · subst k
    simp
  by_cases hk1 : k = 1
  · subst k
    simp
  simp [hk0, hk1, PowerSeries.coeff_X]

/-- The Euler operator `X d/dX` applied to the local square-root factor.  Its
`k`-th coefficient is `k * selbergSqrtZetaLocalCoeff k`. -/
noncomputable def selbergSqrtZetaEulerWeightedDerivative :
    PowerSeries ℝ :=
  PowerSeries.X *
    PowerSeries.derivative ℝ selbergSqrtZetaEulerFactor

private theorem two_mul_powerSeries_C_half :
    (2 : PowerSeries ℝ) *
        PowerSeries.C (1 / 2 : ℝ) = 1 := by
  change PowerSeries.C (2 : ℝ) *
      PowerSeries.C (1 / 2 : ℝ) = 1
  rw [← map_mul]
  norm_num

private theorem powerSeries_C_four :
    PowerSeries.C (4 : ℝ) = (4 : PowerSeries ℝ) := by
  simpa using
    (map_natCast (PowerSeries.C : ℝ →+* PowerSeries ℝ) 4)

theorem selbergSqrtZetaEulerFactor_mul_derivative :
    selbergSqrtZetaEulerFactor *
        PowerSeries.derivative ℝ selbergSqrtZetaEulerFactor =
      -PowerSeries.C (1 / 2 : ℝ) := by
  have hderiv := congrArg (PowerSeries.derivative ℝ)
    selbergSqrtZetaEulerFactor_sq
  rw [Derivation.leibniz, map_sub,
    PowerSeries.derivative_X] at hderiv
  have htwo :
      selbergSqrtZetaEulerFactor *
          PowerSeries.derivative ℝ selbergSqrtZetaEulerFactor +
        selbergSqrtZetaEulerFactor *
          PowerSeries.derivative ℝ selbergSqrtZetaEulerFactor =
        -(1 : PowerSeries ℝ) := by
    simpa [mul_comm] using hderiv
  calc
    selbergSqrtZetaEulerFactor *
          PowerSeries.derivative ℝ selbergSqrtZetaEulerFactor =
        ((2 : PowerSeries ℝ) *
          PowerSeries.C (1 / 2 : ℝ)) *
          (selbergSqrtZetaEulerFactor *
            PowerSeries.derivative ℝ
              selbergSqrtZetaEulerFactor) := by
      rw [two_mul_powerSeries_C_half, one_mul]
    _ = PowerSeries.C (1 / 2 : ℝ) *
        (selbergSqrtZetaEulerFactor *
            PowerSeries.derivative ℝ selbergSqrtZetaEulerFactor +
          selbergSqrtZetaEulerFactor *
            PowerSeries.derivative ℝ
              selbergSqrtZetaEulerFactor) := by ring
    _ = PowerSeries.C (1 / 2 : ℝ) *
        (-(1 : PowerSeries ℝ)) := by rw [htwo]
    _ = -PowerSeries.C (1 / 2 : ℝ) := by ring

theorem coeff_selbergSqrtZetaEulerWeightedDerivative
    (k : ℕ) :
    PowerSeries.coeff k
        selbergSqrtZetaEulerWeightedDerivative =
      (k : ℝ) * selbergSqrtZetaLocalCoeff k := by
  cases k with
  | zero =>
      simp [selbergSqrtZetaEulerWeightedDerivative,
        selbergSqrtZetaLocalCoeff]
  | succ k =>
      rw [selbergSqrtZetaEulerWeightedDerivative]
      have hshift :
          PowerSeries.coeff (k + 1)
              (PowerSeries.X *
                PowerSeries.derivative ℝ
                  selbergSqrtZetaEulerFactor) =
            PowerSeries.coeff k
              (PowerSeries.derivative ℝ
                selbergSqrtZetaEulerFactor) := by
        simpa [Nat.add_comm] using
          (PowerSeries.coeff_X_pow_mul
            (PowerSeries.derivative ℝ
              selbergSqrtZetaEulerFactor) 1 k)
      rw [hshift, PowerSeries.coeff_derivative]
      unfold selbergSqrtZetaLocalCoeff
      norm_cast
      ring

/-- The square of the Euler derivative satisfies a geometric-series
recurrence. -/
theorem selbergSqrtZetaEulerWeightedDerivative_sq_identity :
    PowerSeries.C (4 : ℝ) *
        ((1 - PowerSeries.X) *
          (selbergSqrtZetaEulerWeightedDerivative ^
            (2 : ℕ))) =
      PowerSeries.X ^ (2 : ℕ) := by
  rw [selbergSqrtZetaEulerWeightedDerivative,
    ← selbergSqrtZetaEulerFactor_sq]
  have h := selbergSqrtZetaEulerFactor_mul_derivative
  calc
    PowerSeries.C (4 : ℝ) *
          ((selbergSqrtZetaEulerFactor *
              selbergSqrtZetaEulerFactor) *
            ((PowerSeries.X *
              PowerSeries.derivative ℝ
                selbergSqrtZetaEulerFactor) ^ (2 : ℕ))) =
        ((2 : PowerSeries ℝ) *
          selbergSqrtZetaEulerFactor *
          PowerSeries.derivative ℝ
            selbergSqrtZetaEulerFactor) ^ (2 : ℕ) *
          PowerSeries.X ^ (2 : ℕ) := by
      rw [powerSeries_C_four]
      ring
    _ = (-(1 : PowerSeries ℝ)) ^ (2 : ℕ) *
          PowerSeries.X ^ (2 : ℕ) := by
      rw [show (2 : PowerSeries ℝ) *
          selbergSqrtZetaEulerFactor *
          PowerSeries.derivative ℝ
            selbergSqrtZetaEulerFactor =
          -(1 : PowerSeries ℝ) by
        calc
          (2 : PowerSeries ℝ) *
              selbergSqrtZetaEulerFactor *
              PowerSeries.derivative ℝ
                selbergSqrtZetaEulerFactor =
              (2 : PowerSeries ℝ) *
                (selbergSqrtZetaEulerFactor *
                  PowerSeries.derivative ℝ
                    selbergSqrtZetaEulerFactor) := by ring
          _ = -(1 : PowerSeries ℝ) := by
            rw [h]
            calc
              (2 : PowerSeries ℝ) *
                    (-PowerSeries.C (1 / 2 : ℝ)) =
                  -((2 : PowerSeries ℝ) *
                    PowerSeries.C (1 / 2 : ℝ)) := by ring
              _ = -(1 : PowerSeries ℝ) := by
                rw [two_mul_powerSeries_C_half]]
    _ = PowerSeries.X ^ (2 : ℕ) := by ring

theorem coeff_selbergSqrtZetaEulerWeightedDerivative_sq_recurrence
    (k : ℕ) :
    4 * (PowerSeries.coeff k
          (selbergSqrtZetaEulerWeightedDerivative ^ (2 : ℕ)) -
        if 1 ≤ k then
          PowerSeries.coeff (k - 1)
            (selbergSqrtZetaEulerWeightedDerivative ^ (2 : ℕ))
        else 0) =
      if k = 2 then 1 else 0 := by
  have hcoeff := congrArg (PowerSeries.coeff k)
    selbergSqrtZetaEulerWeightedDerivative_sq_identity
  rw [PowerSeries.coeff_C_mul] at hcoeff
  have hsub :
      PowerSeries.coeff k
          ((1 - PowerSeries.X) *
            (selbergSqrtZetaEulerWeightedDerivative ^ (2 : ℕ))) =
        PowerSeries.coeff k
            (selbergSqrtZetaEulerWeightedDerivative ^ (2 : ℕ)) -
          if 1 ≤ k then
            PowerSeries.coeff (k - 1)
              (selbergSqrtZetaEulerWeightedDerivative ^ (2 : ℕ))
          else 0 := by
    rw [sub_mul, one_mul, map_sub]
    rw [show (PowerSeries.X : PowerSeries ℝ) =
        PowerSeries.X ^ (1 : ℕ) by simp]
    rw [PowerSeries.coeff_X_pow_mul']
  rw [hsub, PowerSeries.coeff_X_pow] at hcoeff
  exact hcoeff

/-- The weighted local convolution is zero in degrees zero and one and is
constant `1/4` from degree two onward. -/
theorem coeff_selbergSqrtZetaEulerWeightedDerivative_sq
    (k : ℕ) :
    PowerSeries.coeff k
        (selbergSqrtZetaEulerWeightedDerivative ^ (2 : ℕ)) =
      if 2 ≤ k then (1 / 4 : ℝ) else 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      have hrec :=
        coeff_selbergSqrtZetaEulerWeightedDerivative_sq_recurrence k
      by_cases hk2 : 2 ≤ k
      · by_cases hkeq : k = 2
        · subst k
          have hprev := ih 1 (by omega)
          norm_num at hprev
          norm_num [hprev] at hrec ⊢
          linarith
        · have hlt : k - 1 < k := by omega
          have hprev := ih (k - 1) hlt
          have hprev2 : 2 ≤ k - 1 := by omega
          rw [if_pos hprev2] at hprev
          rw [if_pos hk2]
          simp [show 1 ≤ k by omega, hkeq, hprev] at hrec
          linarith
      · have hk : k = 0 ∨ k = 1 := by omega
        rcases hk with rfl | rfl
        · norm_num at hrec ⊢
          linarith
        · have hprev := ih 0 (by omega)
          norm_num at hprev
          norm_num [hprev] at hrec ⊢
          linarith

/-- Finite-sum form of the weighted local convolution identity. -/
theorem sum_antidiagonal_mul_selbergSqrtZetaLocalCoeff_mul
    (k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
        (ij.1 : ℝ) * selbergSqrtZetaLocalCoeff ij.1 *
          ((ij.2 : ℝ) * selbergSqrtZetaLocalCoeff ij.2)) =
      if 2 ≤ k then (1 / 4 : ℝ) else 0 := by
  have hcoeff (n : ℕ) :
      PowerSeries.coeff n selbergSqrtZetaEulerWeightedDerivative =
        (n : ℝ) * selbergSqrtZetaLocalCoeff n :=
    coeff_selbergSqrtZetaEulerWeightedDerivative n
  have h :=
    coeff_selbergSqrtZetaEulerWeightedDerivative_sq k
  rw [pow_two, PowerSeries.coeff_mul] at h
  simp_rw [hcoeff] at h
  exact h

/-- A local Euler-factor coefficient with a linear taper in the exponent. -/
noncomputable def selbergSqrtZetaLocalTaperedCoeff
    (L : ℝ) (k : ℕ) : ℝ :=
  selbergSqrtZetaLocalCoeff k * (1 - (k : ℝ) * L)

/-- Exact convolution formula for the linearly tapered local
`ζ⁻¹ᐟ²` coefficients. -/
theorem sum_antidiagonal_selbergSqrtZetaLocalTaperedCoeff_mul
    (L : ℝ) (k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
        selbergSqrtZetaLocalTaperedCoeff L ij.1 *
          selbergSqrtZetaLocalTaperedCoeff L ij.2) =
      if k = 0 then 1
      else if k = 1 then -1 + L
      else L ^ 2 / 4 := by
  have hpair (ij : ℕ × ℕ)
      (hij : ij ∈ Finset.antidiagonal k) :
      selbergSqrtZetaLocalTaperedCoeff L ij.1 *
          selbergSqrtZetaLocalTaperedCoeff L ij.2 =
        (1 - (k : ℝ) * L) *
            (selbergSqrtZetaLocalCoeff ij.1 *
              selbergSqrtZetaLocalCoeff ij.2) +
          L ^ 2 *
            ((ij.1 : ℝ) *
              selbergSqrtZetaLocalCoeff ij.1 *
                ((ij.2 : ℝ) *
                  selbergSqrtZetaLocalCoeff ij.2)) := by
    have hsum : ij.1 + ij.2 = k :=
      Finset.mem_antidiagonal.mp hij
    have hcast : (ij.1 : ℝ) + (ij.2 : ℝ) = k := by
      exact_mod_cast hsum
    unfold selbergSqrtZetaLocalTaperedCoeff
    rw [← hcast]
    ring
  calc
    (∑ ij ∈ Finset.antidiagonal k,
        selbergSqrtZetaLocalTaperedCoeff L ij.1 *
          selbergSqrtZetaLocalTaperedCoeff L ij.2) =
        ∑ ij ∈ Finset.antidiagonal k,
          ((1 - (k : ℝ) * L) *
              (selbergSqrtZetaLocalCoeff ij.1 *
                selbergSqrtZetaLocalCoeff ij.2) +
            L ^ 2 *
              ((ij.1 : ℝ) *
                selbergSqrtZetaLocalCoeff ij.1 *
                  ((ij.2 : ℝ) *
                    selbergSqrtZetaLocalCoeff ij.2))) := by
      apply Finset.sum_congr rfl
      intro ij hij
      exact hpair ij hij
    _ = (1 - (k : ℝ) * L) *
          (∑ ij ∈ Finset.antidiagonal k,
            selbergSqrtZetaLocalCoeff ij.1 *
              selbergSqrtZetaLocalCoeff ij.2) +
        L ^ 2 *
          (∑ ij ∈ Finset.antidiagonal k,
            (ij.1 : ℝ) * selbergSqrtZetaLocalCoeff ij.1 *
              ((ij.2 : ℝ) *
                selbergSqrtZetaLocalCoeff ij.2)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum,
        Finset.mul_sum]
    _ = if k = 0 then 1
        else if k = 1 then -1 + L
        else L ^ 2 / 4 := by
      rw [sum_antidiagonal_selbergSqrtZetaLocalCoeff_mul,
        sum_antidiagonal_mul_selbergSqrtZetaLocalCoeff_mul]
      by_cases hk0 : k = 0
      · subst k
        norm_num
      by_cases hk1 : k = 1
      · subst k
        norm_num
        ring
      have hk2 : 2 ≤ k := by omega
      simp [hk0, hk1, hk2]
      ring

/-- Summing the tapered convolution through degree `n + 1` gives the local
coefficient after multiplication by the zeta Euler factor. -/
theorem sum_range_selbergSqrtZetaLocalTaperedConvolution
    (L : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
        if k = 0 then 1
        else if k = 1 then -1 + L
        else L ^ 2 / 4) =
      L + (n : ℝ) * L ^ 2 / 4 := by
  induction n with
  | zero =>
      norm_num [Finset.sum_range_succ]
  | succ n ih =>
      rw [show n.succ + 2 = (n + 2) + 1 by omega,
        Finset.sum_range_succ, ih]
      have hn1 : n + 2 ≠ 1 := by omega
      simp [hn1]
      ring

end HardyTheorem
