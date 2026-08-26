import HardyTheorem.SelbergJordanWeight
import HardyTheorem.SelbergSqrtZetaArithmetic
import Mathlib.NumberTheory.SmoothNumbers

open scoped BigOperators
open Nat

namespace HardyTheorem

/-!
# The smooth/coprime decomposition in Selberg's arithmetic square

For a positive integer `n`, split its factorization according as the prime
lies in `rho.primeFactors` or outside it.  The two resulting products are
the `rho`-supported part and the part coprime to `rho`.  This is the exact
decomposition used after Titchmarsh (10.11.1).
-/

noncomputable def selbergSupportedPart (rho n : ℕ) : ℕ :=
  (n.factorization.filter fun p => p ∈ rho.primeFactors).prod (fun p k => p ^ k)

noncomputable def selbergCoprimePart (rho n : ℕ) : ℕ :=
  (n.factorization.filter fun p => p ∉ rho.primeFactors).prod (fun p k => p ^ k)

private theorem selbergFilteredFactorization_le
    (rho n : ℕ) :
    n.factorization.filter (fun p => p ∈ rho.primeFactors) ≤ n.factorization := by
  intro p
  simp only [Finsupp.filter_apply]
  split_ifs <;> simp

private theorem selbergComplementFactorization_le
    (rho n : ℕ) :
    n.factorization.filter (fun p => p ∉ rho.primeFactors) ≤ n.factorization := by
  intro p
  simp only [Finsupp.filter_apply]
  split_ifs <;> simp

theorem selbergSupportedPart_mul_coprimePart
    (rho : ℕ) {n : ℕ} (hn : n ≠ 0) :
    selbergSupportedPart rho n * selbergCoprimePart rho n = n := by
  unfold selbergSupportedPart selbergCoprimePart
  rw [Finsupp.prod_filter_mul_prod_filter_not]
  exact Nat.prod_factorization_pow_eq_self hn

private theorem selbergSupportedPart_ne_zero
    (rho : ℕ) {n : ℕ} (hn : n ≠ 0) :
    selbergSupportedPart rho n ≠ 0 := by
  exact ne_zero_of_dvd_ne_zero hn
    (Nat.prod_pow_dvd_of_le_factorization (selbergFilteredFactorization_le rho n))

private theorem selbergCoprimePart_ne_zero
    (rho : ℕ) {n : ℕ} (hn : n ≠ 0) :
    selbergCoprimePart rho n ≠ 0 := by
  exact ne_zero_of_dvd_ne_zero hn
    (Nat.prod_pow_dvd_of_le_factorization (selbergComplementFactorization_le rho n))

private theorem factorization_selbergSupportedPart
    (rho n : ℕ) :
    (selbergSupportedPart rho n).factorization =
      n.factorization.filter (fun p => p ∈ rho.primeFactors) := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (selbergFilteredFactorization_le rho n)

private theorem factorization_selbergCoprimePart
    (rho n : ℕ) :
    (selbergCoprimePart rho n).factorization =
      n.factorization.filter (fun p => p ∉ rho.primeFactors) := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (selbergComplementFactorization_le rho n)

theorem selbergSupportedPart_mem_factoredNumbers
    (rho : ℕ) {n : ℕ} (hn : n ≠ 0) :
    selbergSupportedPart rho n ∈ factoredNumbers rho.primeFactors := by
  apply mem_factoredNumbers_of_primeFactors_subset
    (selbergSupportedPart_ne_zero rho hn)
  rw [← Nat.support_factorization, factorization_selbergSupportedPart,
    Finsupp.support_filter]
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem selbergCoprimePart_coprime
    {rho : ℕ} (hrho : rho ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    (selbergCoprimePart rho n).Coprime rho := by
  rw [← Nat.disjoint_primeFactors (selbergCoprimePart_ne_zero rho hn) hrho]
  rw [← Nat.support_factorization, factorization_selbergCoprimePart,
    Finsupp.support_filter]
  rw [Finset.disjoint_left]
  intro p hp hprho
  exact (Finset.mem_filter.mp hp).2 hprho

theorem selbergSmoothCoprime_decomposition_unique
    (rho : ℕ) {n d k : ℕ} (hn : n ≠ 0)
    (hd : d ∈ factoredNumbers rho.primeFactors)
    (hk : k.Coprime rho) (hdk : d * k = n) :
    d = selbergSupportedPart rho n ∧ k = selbergCoprimePart rho n := by
  have hmulne : d * k ≠ 0 := by simpa only [hdk] using hn
  have hdne : d ≠ 0 := fun hd0 => hmulne (by simp [hd0])
  have hkne : k ≠ 0 := fun hk0 => hmulne (by simp [hk0])
  have hdsubset : d.primeFactors ⊆ rho.primeFactors :=
    primeFactors_subset_of_mem_factoredNumbers hd
  have hdkcop : d.Coprime k := by
    rw [← Nat.disjoint_primeFactors hdne hkne]
    exact hk.disjoint_primeFactors.symm.mono hdsubset (fun _ h => h)
  have hfac : n.factorization = d.factorization + k.factorization := by
    rw [← hdk, Nat.factorization_mul_of_coprime hdkcop]
  have hdfac : d.factorization =
      n.factorization.filter (fun p => p ∈ rho.primeFactors) := by
    ext p
    simp only [Finsupp.filter_apply]
    split_ifs with hp
    · have hkzero : k.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        intro hpk
        exact Finset.disjoint_left.mp hk.disjoint_primeFactors hpk hp
      have hpoint := congrArg (fun f : ℕ →₀ ℕ => f p) hfac
      simpa only [Finsupp.add_apply, hkzero, add_zero] using hpoint.symm
    · rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      intro hpd
      exact hp (hdsubset hpd)
  have hdEq : d = selbergSupportedPart rho n := by
    apply Nat.eq_of_factorization_eq' hdne (selbergSupportedPart_ne_zero rho hn)
    exact hdfac.trans (factorization_selbergSupportedPart rho n).symm
  refine ⟨hdEq, ?_⟩
  apply mul_left_cancel₀ hdne
  calc
    d * k = n := hdk
    _ = selbergSupportedPart rho n * selbergCoprimePart rho n :=
      (selbergSupportedPart_mul_coprimePart rho hn).symm
    _ = d * selbergCoprimePart rho n := by rw [hdEq]

theorem selbergSqrtZetaCoeff_supportedPart_mul_coprimePart
    (rho : ℕ) {n : ℕ} (hn : n ≠ 0) :
    selbergSqrtZetaCoeff n =
      selbergSqrtZetaCoeff (selbergSupportedPart rho n) *
        selbergSqrtZetaCoeff (selbergCoprimePart rho n) := by
  have hdisj :
      Disjoint (selbergSupportedPart rho n).primeFactors
        (selbergCoprimePart rho n).primeFactors := by
    rw [Finset.disjoint_left]
    intro p hps hpc
    have hps' : p ∈ rho.primeFactors := by
      rw [← Nat.support_factorization, factorization_selbergSupportedPart,
        Finsupp.support_filter] at hps
      exact (Finset.mem_filter.mp hps).2
    have hpc' : p ∉ rho.primeFactors := by
      rw [← Nat.support_factorization, factorization_selbergCoprimePart,
        Finsupp.support_filter] at hpc
      exact (Finset.mem_filter.mp hpc).2
    exact hpc' hps'
  have hcop : (selbergSupportedPart rho n).Coprime
      (selbergCoprimePart rho n) :=
    (Nat.disjoint_primeFactors
      (selbergSupportedPart_ne_zero rho hn)
      (selbergCoprimePart_ne_zero rho hn)).mp hdisj
  calc
    selbergSqrtZetaCoeff n =
        selbergSqrtZetaCoeff
          (selbergSupportedPart rho n * selbergCoprimePart rho n) := by
      rw [selbergSupportedPart_mul_coprimePart rho hn]
    _ = selbergSqrtZetaCoeff (selbergSupportedPart rho n) *
        selbergSqrtZetaCoeff (selbergCoprimePart rho n) :=
      selbergSqrtZetaCoeff_isMultiplicative.map_mul_of_coprime hcop

end HardyTheorem
