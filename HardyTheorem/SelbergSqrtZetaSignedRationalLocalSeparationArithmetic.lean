import HardyTheorem.SelbergSqrtZetaSignedRationalLocalSeparation
import HardyTheorem.SelbergSqrtZetaSignedRationalSeparation

/-!
# Arithmetic control of local rational-frequency separation

Distinct logarithmic frequencies in the actual signed Selberg support are
separated by at least `1 / (N * X^2)`.  Passing this pairwise arithmetic
bound through the finite infimum defining `localFrequencySeparation` gives a
pointwise lower bound at every supported rational key.  Consequently the
Montgomery--Vaughan local-separation energy is bounded by the finite collected
coefficient energy with the explicit factor `N * X^2`.

The factor is deliberately recorded rather than hidden in an asymptotic
constant.  It is a valid arithmetic input for the model mean-square budget,
although a scale-sharp Selberg estimate will need a finer reduced-ratio
energy argument.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-- Every actual collected rational frequency has nearest-neighbour
logarithmic separation at least `1 / (N * X^2)`. -/
theorem
    one_div_nat_mul_sq_le_localFrequencySeparation_of_mem_rationalSupport
    {N X : ℕ}
    (hS : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial)
    {q : ℚ} (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X) :
    1 / ((N * X ^ 2 : ℕ) : ℝ) ≤
      PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
        (selbergSqrtZetaSignedRationalSupport N X)
        selbergSqrtZetaSignedRationalFrequency q := by
  classical
  let Q := selbergSqrtZetaSignedRationalSupport N X
  have hErase : (Q.erase q).Nonempty := hS.erase_nonempty
  rw [PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation,
    dif_pos hErase, Finset.le_inf'_iff]
  intro r hr
  have hrQ : r ∈ selbergSqrtZetaSignedRationalSupport N X := by
    exact Finset.mem_of_mem_erase hr
  have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
  exact
    one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
      hq hrQ hrq.symm

/-- The complete local-separation weighted coefficient energy is bounded by
the explicit finite arithmetic factor `N * X^2` times the collected square
energy. -/
theorem sum_normSq_div_localFrequencySeparation_le_arithmeticEnergy
    {N X : ℕ} (hN : 0 < N) (hX : 0 < X)
    (hS : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q) ≤
      ((N * X ^ 2 : ℕ) : ℝ) *
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) := by
  classical
  let Q := selbergSqrtZetaSignedRationalSupport N X
  let omega := selbergSqrtZetaSignedRationalFrequency
  let M : ℝ := ((N * X ^ 2 : ℕ) : ℝ)
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast Nat.mul_pos hN (pow_pos hX 2)
  have hinj : Set.InjOn omega (Q : Set ℚ) := by
    simpa only [Q, omega] using
      selbergSqrtZetaSignedRationalFrequency_injOn N X
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  let delta :=
    PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
      Q omega q
  have hdelta : 0 < delta := by
    exact
      PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation_pos
        hS hq hinj
  have hlocal : 1 / M ≤ delta := by
    simpa only [Q, omega, M, delta] using
      one_div_nat_mul_sq_le_localFrequencySeparation_of_mem_rationalSupport
        hS hq
  have hrecip : 1 / delta ≤ M := by
    apply (div_le_iff₀ hdelta).2
    calc
      (1 : ℝ) = M * (1 / M) := by field_simp [hM.ne']
      _ ≤ M * delta := mul_le_mul_of_nonneg_left hlocal hM.le
  have hnorm :
      0 ≤ Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) :=
    Complex.normSq_nonneg _
  calc
    Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q =
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) *
          (1 / delta) := by
            change
              Complex.normSq
                    (selbergSqrtZetaSignedRationalCoeff N X q) *
                  delta⁻¹ =
                Complex.normSq
                    (selbergSqrtZetaSignedRationalCoeff N X q) *
                  (1 / delta)
            rw [one_div]
    _ ≤ Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) * M :=
      mul_le_mul_of_nonneg_left hrecip hnorm
    _ = M * Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X q) := by ring

/-- Substituting the arithmetic local-separation bound into the
Montgomery--Vaughan estimate leaves only the finite collected coefficient
energy. -/
theorem integral_normSq_rationalCollectedPolynomial_le_arithmeticEnergy
    (N X : ℕ) {a b : ℝ} (hab : a ≤ b)
    (hN : 0 < N) (hX : 0 < X)
    (hS : (selbergSqrtZetaSignedRationalSupport N X).Nontrivial) :
    (∫ t in a..b,
        Complex.normSq
          (selbergSqrtZetaSignedRationalCollectedPolynomial N X t)) ≤
      (b - a + 4 * Real.pi * ((N * X ^ 2 : ℕ) : ℝ)) *
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
          Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) := by
  have hmean :=
    integral_normSq_selbergSqrtZetaSignedRationalCollectedPolynomial_le_localSeparation
      N X hab hS
  have harithmetic :=
    sum_normSq_div_localFrequencySeparation_le_arithmeticEnergy hN hX hS
  have hfourPi : (0 : ℝ) ≤ 4 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  calc
    (∫ t in a..b,
        Complex.normSq
          (selbergSqrtZetaSignedRationalCollectedPolynomial N X t)) ≤
        (b - a) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff N X q) +
          4 * Real.pi *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
              Complex.normSq
                  (selbergSqrtZetaSignedRationalCoeff N X q) /
                PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                  (selbergSqrtZetaSignedRationalSupport N X)
                  selbergSqrtZetaSignedRationalFrequency q := hmean
    _ ≤ (b - a) *
            ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
              Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff N X q) +
          4 * Real.pi *
            (((N * X ^ 2 : ℕ) : ℝ) *
              ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
                Complex.normSq
                  (selbergSqrtZetaSignedRationalCoeff N X q)) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left harithmetic hfourPi)
    _ = (b - a + 4 * Real.pi * ((N * X ^ 2 : ℕ) : ℝ)) *
          ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X q) := by ring

end HardyTheorem
