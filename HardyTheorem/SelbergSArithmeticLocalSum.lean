import HardyTheorem.SelbergSArithmeticPairSplit
import HardyTheorem.SelbergS12RealCutoff

open Complex Nat
open scoped BigOperators

namespace HardyTheorem

/-!
# The local coprime fiber is exactly the real-cutoff S12 sum

The finite split index is presented as a dependent sum over its smooth
part.  The inner finite sum has no omitted tail: the Perron cutoff kills
every term beyond `d * k ≤ X` exactly.
-/

def selbergSmoothOuterIndex (rho X : ℕ) :=
  {d : ℕ // d ∈ Finset.Icc 1 X ∧ d ∈ factoredNumbers rho.primeFactors}

def selbergCoprimeFiberIndex
    (rho X : ℕ) (d : selbergSmoothOuterIndex rho X) :=
  {k : ℕ // k ∈ Finset.Icc 1 X ∧ k.Coprime rho ∧ d.1 * k ≤ X}

noncomputable instance selbergSmoothOuterIndexFintype (rho X : ℕ) :
    Fintype (selbergSmoothOuterIndex rho X) :=
  Set.Finite.fintype
    ((Finset.finite_toSet (Finset.Icc 1 X)).subset
      (fun _ h => h.1))

noncomputable instance selbergCoprimeFiberIndexFintype
    (rho X : ℕ) (d : selbergSmoothOuterIndex rho X) :
    Fintype (selbergCoprimeFiberIndex rho X d) :=
  Set.Finite.fintype
    ((Finset.finite_toSet (Finset.Icc 1 X)).subset
      (fun _ h => h.1))

def selbergSplitIndexSigmaEquiv (rho X : ℕ) :
    selbergSmoothCoprimeIndex rho X ≃
      (d : selbergSmoothOuterIndex rho X) ×
        selbergCoprimeFiberIndex rho X d where
  toFun p :=
    ⟨⟨p.1.1.1, p.1.1.2, p.2.1⟩,
      ⟨p.1.2.1, p.1.2.2, p.2.2.1, p.2.2.2⟩⟩
  invFun p :=
    ⟨(⟨p.1.1, p.1.2.1⟩, ⟨p.2.1, p.2.2.1⟩),
      p.1.2.2, p.2.2.2.1, p.2.2.2.2⟩
  left_inv p := by rfl
  right_inv p := by rfl

theorem selbergCoprimeFiberSum_eq_weightedCoprimeSumReal
    {rho X : ℕ} (d : selbergSmoothOuterIndex rho X)
    (theta : ℝ) (hX : 0 < X) :
    (∑ k : selbergCoprimeFiberIndex rho X d,
        selbergCoprimeLocalFactor rho X theta d.1 k.1) =
      selbergS12WeightedCoprimeSumReal rho theta
        ((X : ℝ) / (d.1 : ℝ)) := by
  let S : Finset ℕ :=
    (Finset.Icc 1 X).filter
      (fun k => k.Coprime rho ∧ d.1 * k ≤ X)
  have hsumSubtype :
      (∑ n ∈ S,
          selbergCoprimeLocalFactor rho X theta d.1 n) =
        ∑ k : selbergCoprimeFiberIndex rho X d,
          selbergCoprimeLocalFactor rho X theta d.1 k.1 := by
    apply Finset.sum_subtype S
    intro n
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
  rw [← hsumSubtype]
  unfold selbergS12WeightedCoprimeSumReal
  rw [tsum_eq_sum (s := S)]
  · apply Finset.sum_congr rfl
    intro n hn
    rfl
  · intro n hnS
    by_cases hn0 : n = 0
    · subst n
      simp [selbergS12ShiftedCoprimeCoeff, selbergS12CoprimeCoeff,
        selbergCoprimeLocalFactor]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    by_cases hcop : n.Coprime rho
    · by_cases hdnX : d.1 * n ≤ X
      · have hnle : n ≤ X := by
          have hdpos : 0 < d.1 :=
            Nat.zero_lt_of_lt (Finset.mem_Icc.mp d.2.1).1
          exact (Nat.le_mul_of_pos_left n hdpos).trans hdnX
        exact False.elim (hnS (by
          simp only [S, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hn0, hnle⟩, hcop, hdnX⟩))
      · have hXdn : X ≤ d.1 * n := (Nat.le_of_not_ge hdnX)
        have hdpos : 0 < d.1 :=
          Nat.zero_lt_of_lt (Finset.mem_Icc.mp d.2.1).1
        have hcut := perronLogCutoff_nat_div_eq_zero
          (n := d.1 * n) (Y := X) (Nat.mul_pos hdpos hnpos) hX hXdn
        have hlocal := perronLogCutoff_mul_div_eq_localCutoff
          (X := (X : ℝ)) (d := d.1) (k := n)
          (by exact_mod_cast hX)
        rw [← hlocal, hcut]
        simp
    · rw [selbergS12ShiftedCoprimeCoeff]
      rw [selbergS12CoprimeCoeff_of_not_coprime hcop]
      simp

end HardyTheorem
