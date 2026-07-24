import HardyTheorem.SelbergSqrtZetaArithmetic
import HardyTheorem.SelbergMollifier
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Selberg's tapered square-root zeta mollifier

The old short-mollifier experiment used tapered Möbius coefficients in both
mollifier copies.  Its prime coefficient stays of constant size and therefore
cannot prove Selberg's small-bad-window estimate.  Here the Möbius factor is
replaced by the coefficients of `ζ⁻¹ᐟ²`, as in Selberg's argument.
-/

/-- The linearly tapered coefficient of `ζ⁻¹ᐟ²`. -/
noncomputable def selbergSqrtZetaTaperedCoeff
    (X n : ℕ) : ℝ :=
  selbergSqrtZetaCoeff n * selbergMoebiusWeight X n

/-- The finite arithmetic function associated to the linearly tapered
square-root zeta mollifier. -/
noncomputable def selbergShortTaperedSqrtZeta
    (X : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n =>
      if n ∈ Finset.Icc 1 X
      then selbergSqrtZetaTaperedCoeff X n
      else 0,
    by simp⟩

@[simp] theorem selbergShortTaperedSqrtZeta_apply
    (X n : ℕ) :
    selbergShortTaperedSqrtZeta X n =
      if n ∈ Finset.Icc 1 X
      then selbergSqrtZetaTaperedCoeff X n
      else 0 :=
  rfl

@[simp] theorem selbergSqrtZetaTaperedCoeff_one
    (X : ℕ) :
    selbergSqrtZetaTaperedCoeff X 1 = 1 := by
  simp [selbergSqrtZetaTaperedCoeff, selbergMoebiusWeight]

@[simp] theorem selbergShortTaperedSqrtZeta_one
    {X : ℕ} (hX : 1 ≤ X) :
    selbergShortTaperedSqrtZeta X 1 = 1 := by
  simp [selbergShortTaperedSqrtZeta, hX]

theorem selbergSqrtZetaTaperedCoeff_prime
    {X p : ℕ} (hp : p.Prime) :
    selbergSqrtZetaTaperedCoeff X p =
      -(1 / 2 : ℝ) *
        (1 - Real.log p / Real.log X) := by
  rw [selbergSqrtZetaTaperedCoeff,
    show p = p ^ (1 : ℕ) by simp,
    selbergSqrtZetaCoeff_apply_prime_pow hp,
    selbergSqrtZetaLocalCoeff_one]
  rfl

/-- The convolution square has prime coefficient `-1 + log p / log X`.
Unlike the old Möbius-square coefficient, the logarithmic correction occurs
only once. -/
theorem selbergShortTaperedSqrtZeta_sq_apply_prime
    {X p : ℕ} (hX : 1 ≤ X) (hp : p.Prime) (hpX : p ≤ X) :
    (selbergShortTaperedSqrtZeta X *
      selbergShortTaperedSqrtZeta X) p =
        -1 + Real.log p / Real.log X := by
  have hB1 : selbergShortTaperedSqrtZeta X 1 = 1 :=
    selbergShortTaperedSqrtZeta_one hX
  have hBp :
      selbergShortTaperedSqrtZeta X p =
        -(1 / 2 : ℝ) *
          (1 - Real.log p / Real.log X) := by
    rw [selbergShortTaperedSqrtZeta_apply]
    simp [Finset.mem_Icc, hp.one_le, hpX,
      selbergSqrtZetaTaperedCoeff_prime hp]
  rw [ArithmeticFunction.mul_apply]
  change
    (∑ x ∈ p.divisorsAntidiagonal,
      (fun i j =>
        selbergShortTaperedSqrtZeta X i *
          selbergShortTaperedSqrtZeta X j) x.1 x.2) =
      -1 + Real.log p / Real.log X
  rw [Nat.sum_divisorsAntidiagonal
      (fun i j =>
        selbergShortTaperedSqrtZeta X i *
          selbergShortTaperedSqrtZeta X j),
    hp.divisors]
  rw [Finset.sum_insert, Finset.sum_singleton]
  · rw [Nat.div_one, Nat.div_self hp.pos, hB1, hBp]
    ring
  · simpa using hp.ne_one.symm

/-- After collecting against the zeta Euler factor, the prime coefficient is
exactly `log p / log X`.  This is the first cancellation that fails for the
naive Möbius-square mollifier. -/
theorem selbergShortTaperedSqrtZeta_sq_mul_zeta_apply_prime
    {X p : ℕ} (hX : 1 ≤ X) (hp : p.Prime) (hpX : p ≤ X) :
    (((selbergShortTaperedSqrtZeta X *
      selbergShortTaperedSqrtZeta X) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) p) =
      Real.log p / Real.log X := by
  have hsq1 :
      (selbergShortTaperedSqrtZeta X *
        selbergShortTaperedSqrtZeta X) 1 = 1 := by
    rw [ArithmeticFunction.mul_apply_one,
      selbergShortTaperedSqrtZeta_one hX]
    ring
  have hsqP :
      (selbergShortTaperedSqrtZeta X *
        selbergShortTaperedSqrtZeta X) p =
          -1 + Real.log p / Real.log X :=
    selbergShortTaperedSqrtZeta_sq_apply_prime hX hp hpX
  rw [ArithmeticFunction.coe_mul_zeta_apply, hp.divisors]
  rw [Finset.sum_insert, Finset.sum_singleton]
  · rw [hsq1, hsqP]
    ring
  · simpa using hp.ne_one.symm

end HardyTheorem
