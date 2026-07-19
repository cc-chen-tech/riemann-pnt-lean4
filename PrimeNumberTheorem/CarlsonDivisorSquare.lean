import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators ArithmeticFunction.sigma

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The fourfold divisor function, written as the Dirichlet convolution of
two ordinary divisor-counting functions. -/
def fourfoldDivisorCount (n : ℕ) : ℕ :=
  (ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0) n

/-- The threefold divisor function used in the summatory recurrence for the
fourfold divisor function. -/
def tripleDivisorCount (n : ℕ) : ℕ :=
  (ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta) n

/-- The explicit nested count of positive quadruples whose product is at
most `Y`; the last quotient counts the fourth factor. -/
def fourfoldDivisorPrefix (Y : ℕ) : ℕ :=
  ∑ a ∈ Finset.Ioc 0 Y,
    ∑ b ∈ Finset.Ioc 0 (Y / a),
      ∑ c ∈ Finset.Ioc 0 ((Y / a) / b), ((Y / a) / b) / c

/-- Divisor pairs and divisors have the same cardinality. -/
theorem card_divisorsAntidiagonal_eq_card_divisors (n : ℕ) :
    n.divisorsAntidiagonal.card = n.divisors.card := by
  have h := congrArg Finset.card (Nat.map_div_right_divisors (n := n))
  simpa using h.symm

/-- On every prime power, the square of the divisor count is bounded by the
fourfold divisor count. -/
theorem card_divisors_sq_le_fourfoldDivisorCount_prime_pow
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p ^ k).divisors.card ^ 2 ≤ fourfoldDivisorCount (p ^ k) := by
  have hfour :
      fourfoldDivisorCount (p ^ k) =
        ∑ j ∈ Finset.range (k + 1), (j + 1) * (k - j + 1) := by
    unfold fourfoldDivisorCount
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal
        (fun a b => ArithmeticFunction.sigma 0 a *
          ArithmeticFunction.sigma 0 b),
      Nat.sum_divisors_prime_pow hp]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp,
      Nat.pow_div hjk hp.pos,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  rw [show (p ^ k).divisors.card = k + 1 by
    simpa [Nat.divisors_prime_pow hp]]
  rw [hfour]
  calc
    (k + 1) ^ 2 = ∑ _j ∈ Finset.range (k + 1), (k + 1) := by
      simp [pow_two]
    _ ≤ ∑ j ∈ Finset.range (k + 1), (j + 1) * (k - j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hsub : k - j + j = k := Nat.sub_add_cancel hjk
      nlinarith [Nat.zero_le (j * (k - j))]

/-- For every positive integer, `d(n)^2` is bounded by the fourfold divisor
function.  This turns the Carlson coefficient problem into a fourfold-product
counting problem. -/
theorem card_divisorsAntidiagonal_sq_le_fourfoldDivisorCount
    {n : ℕ} (hn : n ≠ 0) :
    n.divisorsAntidiagonal.card ^ 2 ≤ fourfoldDivisorCount n := by
  let d : ArithmeticFunction ℕ := ArithmeticFunction.sigma 0
  let d4 : ArithmeticFunction ℕ := d * d
  have hd : d.IsMultiplicative := ArithmeticFunction.isMultiplicative_sigma
  have hd4 : d4.IsMultiplicative := hd.mul hd
  rw [card_divisorsAntidiagonal_eq_card_divisors,
    ← ArithmeticFunction.sigma_zero_apply]
  change d n ^ 2 ≤ d4 n
  rw [hd.multiplicative_factorization d hn,
    hd4.multiplicative_factorization d4 hn]
  simp only [Finsupp.prod]
  rw [← Finset.prod_pow]
  apply Finset.prod_le_prod
  · intro p hp
    exact Nat.zero_le _
  · intro p hp
    have hpPrime : p.Prime := by
      apply Nat.prime_of_mem_primeFactors
      simpa [Nat.support_factorization] using hp
    have hprime :=
      card_divisors_sq_le_fourfoldDivisorCount_prime_pow hpPrime
        (n.factorization p)
    rw [← ArithmeticFunction.sigma_zero_apply] at hprime
    simpa [d, d4, fourfoldDivisorCount] using hprime

/-- A weighted divisor-square sum is bounded termwise by the corresponding
fourfold-divisor sum. -/
theorem weightedDivisorSquareSum_le_fourfoldDivisorCount
    {L U : ℕ} (hL : 0 < L) (sigma : ℝ) :
    ∑ n ∈ Finset.Icc L U,
        ((n : ℝ) + 1) *
          ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 ≤
      ∑ n ∈ Finset.Icc L U,
        ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
          ((n : ℝ) ^ (-sigma)) ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le hL (Finset.mem_Icc.mp hn).1
  have hcardNat := card_divisorsAntidiagonal_sq_le_fourfoldDivisorCount hnpos.ne'
  have hcard :
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 ≤
        (fourfoldDivisorCount n : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((n : ℝ) + 1) *
        ((n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 =
      ((n : ℝ) + 1) *
        ((n.divisorsAntidiagonal.card : ℝ) ^ 2 *
          ((n : ℝ) ^ (-sigma)) ^ 2) := by ring
    _ ≤ ((n : ℝ) + 1) *
        ((fourfoldDivisorCount n : ℝ) * ((n : ℝ) ^ (-sigma)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
        ((n : ℝ) ^ (-sigma)) ^ 2 := by ring

/-- The prefix sum of the threefold divisor function is the divisor-count
sum weighted by integer quotients. -/
theorem sum_Ioc_tripleDivisorCount_eq_sum_div (Y : ℕ) :
    ∑ n ∈ Finset.Ioc 0 Y, tripleDivisorCount n =
      ∑ n ∈ Finset.Ioc 0 Y,
        ArithmeticFunction.sigma 0 n * (Y / n) := by
  unfold tripleDivisorCount
  exact ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.sigma 0) Y

/-- The prefix sum of the fourfold divisor function is the threefold-divisor
sum weighted by integer quotients. -/
theorem sum_Ioc_fourfoldDivisorCount_eq_sum_div (Y : ℕ) :
    ∑ n ∈ Finset.Ioc 0 Y, fourfoldDivisorCount n =
      ∑ n ∈ Finset.Ioc 0 Y, tripleDivisorCount n * (Y / n) := by
  have hsigma :
      ArithmeticFunction.sigma 0 =
        ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
    rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma,
      ArithmeticFunction.pow_zero_eq_zeta]
  have hfunctions :
      ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0 =
        (ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta) *
          ArithmeticFunction.zeta := by
    rw [hsigma]
    simp only [mul_assoc]
  unfold fourfoldDivisorCount tripleDivisorCount
  rw [hfunctions]
  exact ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.sigma 0 * ArithmeticFunction.zeta) Y

/-- The summatory fourfold-divisor function is exactly the nested positive
quadruple count. -/
theorem sum_Ioc_fourfoldDivisorCount_eq_fourfoldDivisorPrefix (Y : ℕ) :
    ∑ n ∈ Finset.Ioc 0 Y, fourfoldDivisorCount n =
      fourfoldDivisorPrefix Y := by
  have hsigma :
      ArithmeticFunction.sigma 0 =
        ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
    rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma,
      ArithmeticFunction.pow_zero_eq_zeta]
  have hfunctions :
      ArithmeticFunction.sigma 0 * ArithmeticFunction.sigma 0 =
        ArithmeticFunction.zeta *
          (ArithmeticFunction.zeta *
            (ArithmeticFunction.zeta * ArithmeticFunction.zeta)) := by
    rw [hsigma]
    simp only [mul_assoc]
  unfold fourfoldDivisorCount fourfoldDivisorPrefix
  rw [hfunctions,
    ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ha0 : a ≠ 0 := by
    have := (Finset.mem_Ioc.mp ha).1
    omega
  rw [ArithmeticFunction.zeta_apply_ne ha0, one_mul,
    ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hb0 : b ≠ 0 := by
    have := (Finset.mem_Ioc.mp hb).1
    omega
  rw [ArithmeticFunction.zeta_apply_ne hb0, one_mul, ← hsigma,
    ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div]

/-- The explicit fourfold-product prefix is bounded by three harmonic sums.
This is the elementary `Y log^3 Y` input behind the divisor-square mean
estimate used in Carlson's argument. -/
theorem fourfoldDivisorPrefix_le_mul_harmonic_cube (Y : ℕ) :
    (fourfoldDivisorPrefix Y : ℝ) ≤
      (Y : ℝ) * (harmonic Y : ℝ) ^ 3 := by
  let S : Finset ℕ := Finset.Ioc 0 Y
  have hquotient {a b c : ℕ} :
      ((((Y / a) / b) / c : ℕ) : ℝ) ≤
        (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ) := by
    calc
      ((((Y / a) / b) / c : ℕ) : ℝ) ≤
          (((Y / a) / b : ℕ) : ℝ) / (c : ℝ) := Nat.cast_div_le
      _ ≤ (((Y / a : ℕ) : ℝ) / (b : ℝ)) / (c : ℝ) := by
        gcongr
        exact Nat.cast_div_le
      _ ≤ (((Y : ℝ) / (a : ℝ)) / (b : ℝ)) / (c : ℝ) := by
        gcongr
        exact Nat.cast_div_le
  have hc_bound {a b : ℕ} :
      (∑ c ∈ Finset.Ioc 0 ((Y / a) / b),
          ((((Y / a) / b) / c : ℕ) : ℝ)) ≤
        ∑ c ∈ S, (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ) := by
    let C : Finset ℕ := Finset.Ioc 0 ((Y / a) / b)
    have hC : C ⊆ S := by
      intro c hc
      rcases Finset.mem_Ioc.mp hc with ⟨hc0, hcUpper⟩
      apply Finset.mem_Ioc.mpr
      exact ⟨hc0, hcUpper.trans ((Nat.div_le_self _ _).trans (Nat.div_le_self _ _))⟩
    calc
      (∑ c ∈ C, ((((Y / a) / b) / c : ℕ) : ℝ)) ≤
          ∑ c ∈ C, (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ) := by
        apply Finset.sum_le_sum
        intro c hc
        exact hquotient
      _ ≤ ∑ c ∈ S, (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hC
        intro c hcS hcC
        positivity
  have hb_bound {a : ℕ} :
      (∑ b ∈ Finset.Ioc 0 (Y / a),
          ∑ c ∈ Finset.Ioc 0 ((Y / a) / b),
            ((((Y / a) / b) / c : ℕ) : ℝ)) ≤
        ∑ b ∈ S, ∑ c ∈ S,
          (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ) := by
    let B : Finset ℕ := Finset.Ioc 0 (Y / a)
    have hB : B ⊆ S := by
      intro b hb
      rcases Finset.mem_Ioc.mp hb with ⟨hb0, hbUpper⟩
      exact Finset.mem_Ioc.mpr ⟨hb0, hbUpper.trans (Nat.div_le_self _ _)⟩
    calc
      (∑ b ∈ B, ∑ c ∈ Finset.Ioc 0 ((Y / a) / b),
          ((((Y / a) / b) / c : ℕ) : ℝ)) ≤
          ∑ b ∈ B, ∑ c ∈ S,
            (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ) := by
        apply Finset.sum_le_sum
        intro b hb
        exact hc_bound
      _ ≤ ∑ b ∈ S, ∑ c ∈ S,
          (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hB
        intro b hbS hbB
        apply Finset.sum_nonneg
        intro c hc
        positivity
  have hprefix :
      (fourfoldDivisorPrefix Y : ℝ) ≤
        ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S,
          (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ) := by
    simp only [fourfoldDivisorPrefix, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro a ha
    exact hb_bound
  have hharmonic :
      (∑ n ∈ S, (n : ℝ)⁻¹) = (harmonic Y : ℝ) := by
    have hS : S = Finset.Icc 1 Y := by
      ext n
      simp only [S, Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hS, harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc
    (fourfoldDivisorPrefix Y : ℝ) ≤
        ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S,
          (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ) := hprefix
    _ = (Y : ℝ) *
        (∑ n ∈ S, (n : ℝ)⁻¹) ^ 3 := by
      let H : ℝ := ∑ n ∈ S, (n : ℝ)⁻¹
      have hc_factor (a b : ℕ) :
          (∑ c ∈ S, (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ)) =
            ((Y : ℝ) / (a : ℝ) / (b : ℝ)) * H := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        simp only [div_eq_mul_inv]
      have hb_factor (a : ℕ) :
          (∑ b ∈ S, ∑ c ∈ S,
              (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ)) =
            ((Y : ℝ) / (a : ℝ)) * H ^ 2 := by
        have hsingle :
            (∑ b ∈ S, (Y : ℝ) / (a : ℝ) / (b : ℝ)) =
              ((Y : ℝ) / (a : ℝ)) * H := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          simp only [div_eq_mul_inv]
        calc
          (∑ b ∈ S, ∑ c ∈ S,
              (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ)) =
              ∑ b ∈ S, ((Y : ℝ) / (a : ℝ) / (b : ℝ)) * H := by
            apply Finset.sum_congr rfl
            intro b hb
            exact hc_factor a b
          _ = (∑ b ∈ S, (Y : ℝ) / (a : ℝ) / (b : ℝ)) * H := by
            rw [Finset.sum_mul]
          _ = (((Y : ℝ) / (a : ℝ)) * H) * H := by rw [hsingle]
          _ = ((Y : ℝ) / (a : ℝ)) * H ^ 2 := by ring
      have ha_factor :
          (∑ a ∈ S, (Y : ℝ) / (a : ℝ)) = (Y : ℝ) * H := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        simp only [div_eq_mul_inv]
      calc
        (∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S,
            (Y : ℝ) / (a : ℝ) / (b : ℝ) / (c : ℝ)) =
            ∑ a ∈ S, ((Y : ℝ) / (a : ℝ)) * H ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hb_factor a
        _ = (∑ a ∈ S, (Y : ℝ) / (a : ℝ)) * H ^ 2 := by
          rw [Finset.sum_mul]
        _ = ((Y : ℝ) * H) * H ^ 2 := by rw [ha_factor]
        _ = (Y : ℝ) * H ^ 3 := by ring
    _ = (Y : ℝ) * (harmonic Y : ℝ) ^ 3 := by rw [hharmonic]

/-- The summatory fourfold divisor count has the elementary
`Y * (1 + log Y)^3` upper bound needed before partial summation. -/
theorem sum_Ioc_fourfoldDivisorCount_le_mul_one_add_log_cube (Y : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Y, (fourfoldDivisorCount n : ℝ)) ≤
      (Y : ℝ) * (1 + Real.log Y) ^ 3 := by
  calc
    (∑ n ∈ Finset.Ioc 0 Y, (fourfoldDivisorCount n : ℝ)) =
        (fourfoldDivisorPrefix Y : ℝ) := by
      rw [← Nat.cast_sum, sum_Ioc_fourfoldDivisorCount_eq_fourfoldDivisorPrefix]
    _ ≤ (Y : ℝ) * (harmonic Y : ℝ) ^ 3 :=
      fourfoldDivisorPrefix_le_mul_harmonic_cube Y
    _ ≤ (Y : ℝ) * (1 + Real.log Y) ^ 3 := by
      have hharmonic_nonneg : 0 ≤ (harmonic Y : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        positivity
      gcongr
      exact harmonic_le_one_add_log Y

/-- On an interval starting at `L`, the negative power in the Carlson weight
is bounded by its value at `L`.  Combining this with the summatory `d₄` bound
reduces the weighted tail to an explicit endpoint expression. -/
theorem weightedFourfoldDivisorSum_le_prefix_bound
    {L U : ℕ} (hL : 0 < L) {sigma : ℝ} (hsigma : 1 / 2 < sigma) :
    ∑ n ∈ Finset.Icc L U,
        ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
          ((n : ℝ) ^ (-sigma)) ^ 2 ≤
      2 * (L : ℝ) ^ (1 - 2 * sigma) *
        ((U : ℝ) * (1 + Real.log U) ^ 3) := by
  have hexponent : 1 - 2 * sigma ≤ 0 := by linarith
  have hweight {n : ℕ} (hn : n ∈ Finset.Icc L U) :
      ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2 ≤
        2 * (L : ℝ) ^ (1 - 2 * sigma) := by
    have hnL : L ≤ n := (Finset.mem_Icc.mp hn).1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hL.trans_le hnL
    have hnlinear : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      exact_mod_cast (show n + 1 ≤ 2 * n by omega)
    have hsquare :
        ((n : ℝ) ^ (-sigma)) ^ 2 = (n : ℝ) ^ (-2 * sigma) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hnpos)]
      congr 1
      ring
    have hpower :
        (n : ℝ) ^ (1 - 2 * sigma) ≤
          (L : ℝ) ^ (1 - 2 * sigma) := by
      exact Real.rpow_le_rpow_of_nonpos
        (by exact_mod_cast hL) (by exact_mod_cast hnL) hexponent
    calc
      ((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2 ≤
          (2 * (n : ℝ)) * ((n : ℝ) ^ (-sigma)) ^ 2 :=
        mul_le_mul_of_nonneg_right hnlinear (sq_nonneg _)
      _ = 2 * (n : ℝ) ^ (1 - 2 * sigma) := by
        rw [hsquare]
        calc
          (2 * (n : ℝ)) * (n : ℝ) ^ (-2 * sigma) =
              2 * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-2 * sigma)) := by
            rw [Real.rpow_one]
            ring
          _ = 2 * (n : ℝ) ^ ((1 : ℝ) + (-2 * sigma)) := by
            rw [Real.rpow_add hnpos]
          _ = 2 * (n : ℝ) ^ (1 - 2 * sigma) := by ring_nf
      _ ≤ 2 * (L : ℝ) ^ (1 - 2 * sigma) := by gcongr
  have hsubset : Finset.Icc L U ⊆ Finset.Ioc 0 U := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hnL, hnU⟩
    exact Finset.mem_Ioc.mpr ⟨hL.trans_le hnL, hnU⟩
  calc
    (∑ n ∈ Finset.Icc L U,
        ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
          ((n : ℝ) ^ (-sigma)) ^ 2) ≤
        ∑ n ∈ Finset.Icc L U,
          (2 * (L : ℝ) ^ (1 - 2 * sigma)) *
            (fourfoldDivisorCount n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        ((n : ℝ) + 1) * (fourfoldDivisorCount n : ℝ) *
            ((n : ℝ) ^ (-sigma)) ^ 2 =
            (fourfoldDivisorCount n : ℝ) *
              (((n : ℝ) + 1) * ((n : ℝ) ^ (-sigma)) ^ 2) := by ring
        _ ≤ (fourfoldDivisorCount n : ℝ) *
            (2 * (L : ℝ) ^ (1 - 2 * sigma)) := by
          exact mul_le_mul_of_nonneg_left (hweight hn) (Nat.cast_nonneg _)
        _ = (2 * (L : ℝ) ^ (1 - 2 * sigma)) *
            (fourfoldDivisorCount n : ℝ) := by ring
    _ = (2 * (L : ℝ) ^ (1 - 2 * sigma)) *
        (∑ n ∈ Finset.Icc L U, (fourfoldDivisorCount n : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * (L : ℝ) ^ (1 - 2 * sigma)) *
        (∑ n ∈ Finset.Ioc 0 U, (fourfoldDivisorCount n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro n hnU hnLU
        positivity
      · positivity
    _ ≤ 2 * (L : ℝ) ^ (1 - 2 * sigma) *
        ((U : ℝ) * (1 + Real.log U) ^ 3) := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_Ioc_fourfoldDivisorCount_le_mul_one_add_log_cube U
      · positivity

end CarlsonZeroDensity
end PrimeNumberTheorem
