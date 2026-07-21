import HardyTheorem.SelbergMollifiedTripleMainTerm
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Chebyshev

open Finset
open scoped BigOperators

namespace HardyTheorem

/-!
# Mertens-type upper bound for the prime logarithm sum

This file proves the elementary Mertens first-theorem upper bound

```
∑_{p ≤ N, p prime} log p / p ≤ log N + (log 4 + 5)
```

with a fully explicit constant.  The proof is the classical one: the exact
factorial identity `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) * ⌊N/d⌋`, Chebyshev's
upper bound `ψ(x) ≤ (log 4 + 4) * x` from Mathlib, and an integral
comparison for `∑ log n`.  Only the upper bound is proved; no lower
Mertens bound is claimed.

This is the arithmetic input for the lower bound on Selberg's main
coefficient in `SelbergMollifiedTripleMainTerm.lean`.
-/

/-- Integral comparison, increasing side: the factorial log sum up to `N` is
at most `(N+1) log (N+1) - N`. -/
theorem log_sum_Icc_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log n ≤ ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - N := by
  have hmono : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    rw [Nat.cast_one] at hx
    exact Real.log_le_log (zero_lt_one.trans_le hx.1) hxy
  have hIco : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have h := MonotoneOn.sum_le_integral_Ico (by omega : (1 : ℕ) ≤ N + 1) hmono
  rw [hIco] at h
  have h2 : (∫ x in ((1 : ℕ) : ℝ)..((N + 1 : ℕ) : ℝ), Real.log x) =
      ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - N := by
    rw [integral_log]
    push_cast
    rw [Real.log_one]
    ring
  rw [h2] at h
  exact h

/-- Integral comparison, decreasing side: `N log N - N + 1` is at most the
factorial log sum up to `N`. -/
theorem le_log_sum_Icc {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * Real.log N - N + 1 ≤ ∑ n ∈ Finset.Icc 1 N, Real.log n := by
  have hmono : MonotoneOn Real.log (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    rw [Nat.cast_one] at hx
    exact Real.log_le_log (zero_lt_one.trans_le hx.1) hxy
  have h := MonotoneOn.integral_le_sum_Ico hN hmono
  have h2 : (∫ x in ((1 : ℕ) : ℝ)..((N : ℕ) : ℝ), Real.log x) =
      (N : ℝ) * Real.log N - N + 1 := by
    rw [integral_log]
    push_cast
    rw [Real.log_one]
    ring
  rw [h2] at h
  have hreindex : (∑ i ∈ Finset.Ico 1 N, Real.log ((i + 1 : ℕ) : ℝ)) =
      ∑ n ∈ Finset.Icc 2 N, Real.log n := by
    have himg : Finset.Icc 2 N = (Finset.Ico 1 N).image (· + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_Ico]
      constructor
      · rintro ⟨h2n, hnN⟩
        exact ⟨n - 1, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨i, ⟨hi1, hiN⟩, rfl⟩
        exact ⟨by omega, by omega⟩
    rw [himg, Finset.sum_image (fun a _ b _ hab => Nat.add_right_cancel hab)]
  have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert (by simp), Nat.cast_one, Real.log_one, zero_add,
    ← hreindex]
  exact h

/-- The multiples of `d` in `[1, N]` are counted by `N / d`. -/
theorem card_Icc_filter_dvd {N d : ℕ} (hd : 1 ≤ d) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  have hbij : (Finset.Icc 1 N).filter (fun n => d ∣ n) =
      (Finset.Icc 1 (N / d)).image (fun m => d * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, ⟨m, rfl⟩⟩
      refine ⟨m, ⟨?_, ?_⟩, rfl⟩
      · by_contra hm0
        rw [not_le, Nat.lt_one_iff] at hm0
        rw [hm0, Nat.mul_zero] at hn1
        omega
      · rw [Nat.le_div_iff_mul_le hd, Nat.mul_comm]
        exact hnN
    · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hd hm1, ?_⟩, m, rfl⟩
      rw [Nat.le_div_iff_mul_le hd] at hmN
      rw [Nat.mul_comm]
      exact hmN
  rw [hbij, Finset.card_image_of_injective _ (fun a b hab =>
    Nat.mul_left_cancel (by omega : 0 < d) hab), Nat.card_Icc, Nat.add_sub_cancel]

/-- The exact factorial identity: `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`,
with the floor kept as the natural division `N / d`. -/
theorem log_sum_Icc_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log n =
      ∑ d ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := by
  classical
  have hdiv : ∀ n ∈ Finset.Icc 1 N,
      n.divisors = (Finset.Icc 1 N).filter (· ∣ n) := by
    intro n hn
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩
    constructor
    · rintro ⟨hdvd, -⟩
      have hd1 : 1 ≤ d := by
        by_contra h
        rw [not_le, Nat.lt_one_iff] at h
        rw [h, Nat.zero_dvd] at hdvd
        omega
      exact ⟨⟨hd1, (Nat.le_of_dvd (by omega) hdvd).trans hnN⟩, hdvd⟩
    · rintro ⟨⟨-, -⟩, hdvd⟩
      exact ⟨hdvd, by omega⟩
  calc
    ∑ n ∈ Finset.Icc 1 N, Real.log n
        = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
            ArithmeticFunction.vonMangoldt d := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [ArithmeticFunction.vonMangoldt_sum]
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
          (if d ∣ n then ArithmeticFunction.vonMangoldt d else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hdiv n hn, Finset.sum_filter]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if d ∣ n then ArithmeticFunction.vonMangoldt d else 0) :=
          Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 N,
          ArithmeticFunction.vonMangoldt d *
            (((Finset.Icc 1 N).filter (fun n => d ∣ n)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
            mul_comm]
    _ = ∑ d ∈ Finset.Icc 1 N,
          ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [card_Icc_filter_dvd (Finset.mem_Icc.mp hd).1]

/-- Mertens' first theorem, upper-bound half, with an explicit constant:
the von-Mangoldt sum `∑_{n ≤ N} Λ(n)/n` is at most `log N + (log 4 + 5)`. -/
theorem vonMangoldt_sum_div_le_log_add {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
      Real.log N + (Real.log 4 + 5) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hid := log_sum_Icc_eq_sum_vonMangoldt_mul_div N
  have hpsi : Chebyshev.psi (N : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d := by
    rw [Chebyshev.psi, Nat.floor_natCast]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hfloor : ∀ d ∈ Finset.Icc 1 N,
      (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    have h1 : N < d * (N / d) + d := by
      have h2 := Nat.div_add_mod N d
      have h3 := Nat.mod_lt N (by omega : 0 < d)
      omega
    have hlt : (N : ℝ) < (d : ℝ) * ((N / d : ℕ) : ℝ) + d := by
      exact_mod_cast h1
    have h5 : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hdpos]
      linarith
    linarith
  have hA : ∑ d ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt d * ((N : ℝ) / d) =
      (N : ℝ) * ∑ d ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt d / (d : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd1)
    field_simp
  have hB : ∑ d ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt d * ((N : ℝ) / d - 1) =
      (N : ℝ) * ∑ d ∈ Finset.Icc 1 N,
          ArithmeticFunction.vonMangoldt d / (d : ℝ) -
        ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d := by
    have hterm : ∀ d ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt d * ((N : ℝ) / d - 1) =
          ArithmeticFunction.vonMangoldt d * ((N : ℝ) / d) -
            ArithmeticFunction.vonMangoldt d := by
      intro d hd
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hA]
  have hmain : (N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 N, Real.log n + Chebyshev.psi (N : ℝ) := by
    calc
      (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n /
          (n : ℝ)
          = ∑ d ∈ Finset.Icc 1 N,
              ArithmeticFunction.vonMangoldt d * ((N : ℝ) / d - 1) +
            Chebyshev.psi (N : ℝ) := by
            rw [hB, hpsi]
            ring
      _ ≤ ∑ d ∈ Finset.Icc 1 N,
              ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) +
            Chebyshev.psi (N : ℝ) :=
            add_le_add
              (Finset.sum_le_sum fun d hd =>
                mul_le_mul_of_nonneg_left (hfloor d hd)
                  ArithmeticFunction.vonMangoldt_nonneg)
              le_rfl
      _ = ∑ n ∈ Finset.Icc 1 N, Real.log n + Chebyshev.psi (N : ℝ) := by
            rw [← hid]
  have hbound : (N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
      ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - N + (Real.log 4 + 4) * N :=
    hmain.trans
      (add_le_add (log_sum_Icc_le N)
        (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)))
  have hlogle : Real.log ((N : ℝ) + 1) ≤ N := by
    calc Real.log ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
      _ = N := by ring
  have hmain' : ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - N ≤
      (N : ℝ) * Real.log ((N : ℝ) + 1) := by
    have hexpand : ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) =
        (N : ℝ) * Real.log ((N : ℝ) + 1) + Real.log ((N : ℝ) + 1) := by ring
    linarith [hlogle, hexpand]
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hmul : (N : ℝ) * (1 + 1 / (N : ℝ)) = (N : ℝ) + 1 := by
    rw [mul_add, mul_one_div_cancel hN0, mul_one]
  have heq : Real.log ((N : ℝ) + 1) =
      Real.log (N : ℝ) + Real.log (1 + 1 / (N : ℝ)) := by
    rw [← Real.log_mul hN0 (by positivity), hmul]
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ Real.log (N : ℝ) + 1 / (N : ℝ) := by
    rw [heq]
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + 1 / (N : ℝ) by positivity)
    have hsimpl : (1 : ℝ) + 1 / (N : ℝ) - 1 = 1 / (N : ℝ) := by ring
    linarith [h, hsimpl]
  have hNmult : (N : ℝ) * Real.log ((N : ℝ) + 1) ≤
      (N : ℝ) * Real.log (N : ℝ) + 1 := by
    have hmul' := mul_le_mul_of_nonneg_left hlogN1 hNpos.le
    have hNdiv : (N : ℝ) * (1 / (N : ℝ)) = 1 := mul_one_div_cancel hN0
    have hexpand : (N : ℝ) * (Real.log (N : ℝ) + 1 / (N : ℝ)) =
        (N : ℝ) * Real.log (N : ℝ) + (N : ℝ) * (1 / (N : ℝ)) := by ring
    linarith [hmul', hNdiv, hexpand]
  have hfinal : (N : ℝ) * ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
      (N : ℝ) * (Real.log (N : ℝ) + (Real.log 4 + 5)) := by
    calc (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n /
          (n : ℝ)
        ≤ ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) - N +
            (Real.log 4 + 4) * N := hbound
      _ ≤ (N : ℝ) * Real.log ((N : ℝ) + 1) + (Real.log 4 + 4) * N := by
          linarith [hmain']
      _ ≤ ((N : ℝ) * Real.log (N : ℝ) + 1) + (Real.log 4 + 4) * N := by
          linarith [hNmult]
      _ ≤ (N : ℝ) * (Real.log (N : ℝ) + (Real.log 4 + 5)) := by
          have hexp : (N : ℝ) * (Real.log (N : ℝ) + (Real.log 4 + 5)) =
              (N : ℝ) * Real.log (N : ℝ) + (Real.log 4 + 5) * N := by ring
          nlinarith [hN1r, hexp]
  exact le_of_mul_le_mul_left hfinal hNpos

/-- Mertens' first theorem for primes, upper-bound half: the prime sum
`∑_{p ≤ N} log p / p` is at most `log N + (log 4 + 5)`. -/
theorem primeLogSum_div_le_log_add {N : ℕ} (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.Icc 2 N).filter Nat.Prime, Real.log p / (p : ℝ) ≤
      Real.log N + (Real.log 4 + 5) := by
  have hterm : ∀ p ∈ (Finset.Icc 2 N).filter Nat.Prime,
      Real.log p / (p : ℝ) =
        ArithmeticFunction.vonMangoldt p / (p : ℝ) := by
    intro p hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime
      (Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hterm]
  have hsub : (Finset.Icc 2 N).filter Nat.Prime ⊆ Finset.Icc 1 N := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpI, -⟩
    rcases Finset.mem_Icc.mp hpI with ⟨hp2, hpN⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hpN⟩
  have hnonneg : ∀ n ∈ Finset.Icc 1 N,
      n ∉ (Finset.Icc 2 N).filter Nat.Prime →
        0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
    intro n hn hnot
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (by positivity)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg).trans
    (vonMangoldt_sum_div_le_log_add hN)

end HardyTheorem
