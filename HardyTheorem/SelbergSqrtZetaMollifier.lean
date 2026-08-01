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

theorem selbergShortTaperedSqrtZeta_apply_prime_pow
    {X p i : ℕ} (hp : p.Prime) (hpiX : p ^ i ≤ X) :
    selbergShortTaperedSqrtZeta X (p ^ i) =
      selbergSqrtZetaLocalTaperedCoeff
        (Real.log p / Real.log X) i := by
  have hpi1 : 1 ≤ p ^ i :=
    Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero i hp.ne_zero)
  rw [selbergShortTaperedSqrtZeta_apply,
    if_pos (Finset.mem_Icc.mpr ⟨hpi1, hpiX⟩)]
  unfold selbergSqrtZetaTaperedCoeff
  unfold selbergSqrtZetaLocalTaperedCoeff
  rw [selbergSqrtZetaCoeff_apply_prime_pow hp]
  have hlog :
      Real.log ((p ^ i : ℕ) : ℝ) =
        (i : ℝ) * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [selbergMoebiusWeight, hlog]
  ring

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

/-- In the complete cutoff range, the convolution-square coefficient at
every prime power is the exact local tapered coefficient convolution. -/
theorem selbergShortTaperedSqrtZeta_sq_apply_prime_pow
    {X p k : ℕ} (hp : p.Prime) (hpkX : p ^ k ≤ X) :
    (selbergShortTaperedSqrtZeta X *
      selbergShortTaperedSqrtZeta X) (p ^ k) =
      if k = 0 then 1
      else if k = 1 then
        -1 + Real.log p / Real.log X
      else (Real.log p / Real.log X) ^ 2 / 4 := by
  rw [ArithmeticFunction.mul_apply]
  change
    (∑ x ∈ (p ^ k).divisorsAntidiagonal,
      (fun i j =>
        selbergShortTaperedSqrtZeta X i *
          selbergShortTaperedSqrtZeta X j) x.1 x.2) =
      _
  rw [Nat.sum_divisorsAntidiagonal
      (fun i j =>
        selbergShortTaperedSqrtZeta X i *
          selbergShortTaperedSqrtZeta X j),
    Nat.sum_divisors_prime_pow hp]
  calc
    (∑ i ∈ Finset.range (k + 1),
        selbergShortTaperedSqrtZeta X (p ^ i) *
          selbergShortTaperedSqrtZeta X
            (p ^ k / p ^ i)) =
        ∑ i ∈ Finset.range (k + 1),
          selbergSqrtZetaLocalTaperedCoeff
              (Real.log p / Real.log X) i *
            selbergSqrtZetaLocalTaperedCoeff
              (Real.log p / Real.log X) (k - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := by
        simpa only [Finset.mem_range,
          Nat.lt_add_one_iff] using hi
      have hpiX : p ^ i ≤ X :=
        (Nat.pow_le_pow_right hp.pos hik).trans hpkX
      have hpkiX : p ^ (k - i) ≤ X :=
        (Nat.pow_le_pow_right hp.pos
          (Nat.sub_le k i)).trans hpkX
      rw [selbergShortTaperedSqrtZeta_apply_prime_pow
          hp hpiX,
        Nat.pow_div hik hp.pos,
        selbergShortTaperedSqrtZeta_apply_prime_pow
          hp hpkiX]
    _ = if k = 0 then 1
        else if k = 1 then
          -1 + Real.log p / Real.log X
        else (Real.log p / Real.log X) ^ 2 / 4 := by
      have hlocal :=
        sum_antidiagonal_selbergSqrtZetaLocalTaperedCoeff_mul
          (Real.log p / Real.log X) k
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j =>
          selbergSqrtZetaLocalTaperedCoeff
              (Real.log p / Real.log X) i *
            selbergSqrtZetaLocalTaperedCoeff
              (Real.log p / Real.log X) j) k] at hlocal
      simpa [Nat.succ_eq_add_one] using hlocal

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

/-- Complete prime-power formula after collecting the squared mollifier
against the zeta Euler factor. -/
theorem selbergShortTaperedSqrtZeta_sq_mul_zeta_apply_prime_pow
    {X p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (hpkX : p ^ k ≤ X) :
    (((selbergShortTaperedSqrtZeta X *
      selbergShortTaperedSqrtZeta X) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
      (p ^ k)) =
      Real.log p / Real.log X +
        ((k - 1 : ℕ) : ℝ) *
          (Real.log p / Real.log X) ^ 2 / 4 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow hp]
  calc
    (∑ i ∈ Finset.range (k + 1),
        (selbergShortTaperedSqrtZeta X *
          selbergShortTaperedSqrtZeta X) (p ^ i)) =
        ∑ i ∈ Finset.range (k + 1),
          if i = 0 then 1
          else if i = 1 then
            -1 + Real.log p / Real.log X
          else (Real.log p / Real.log X) ^ 2 / 4 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i ≤ k := by
        simpa only [Finset.mem_range,
          Nat.lt_add_one_iff] using hi
      have hpiX : p ^ i ≤ X :=
        (Nat.pow_le_pow_right hp.pos hik).trans hpkX
      exact selbergShortTaperedSqrtZeta_sq_apply_prime_pow
        hp hpiX
    _ = Real.log p / Real.log X +
        ((k - 1 : ℕ) : ℝ) *
          (Real.log p / Real.log X) ^ 2 / 4 := by
      have hsum :=
        sum_range_selbergSqrtZetaLocalTaperedConvolution
          (Real.log p / Real.log X) (k - 1)
      have hidx : k - 1 + 2 = k + 1 := by omega
      rw [hidx] at hsum
      exact hsum

end HardyTheorem
