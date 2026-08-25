import HardyTheorem.SelbergTaperPerronBridge

open Nat

namespace HardyTheorem

/-! # Finite reindexing by the smooth/coprime decomposition -/

def selbergTaperIndex (X : ℕ) :=
  {n : ℕ // n ∈ Finset.Icc 1 X}

def selbergSmoothCoprimeIndex (rho X : ℕ) :=
  {p : selbergTaperIndex X × selbergTaperIndex X //
    p.1.1 ∈ factoredNumbers rho.primeFactors ∧
      p.2.1.Coprime rho ∧ p.1.1 * p.2.1 ≤ X}

noncomputable instance selbergTaperIndexFintype (X : ℕ) :
    Fintype (selbergTaperIndex X) :=
  Set.Finite.fintype (Finset.finite_toSet (Finset.Icc 1 X))

noncomputable def selbergSmoothCoprimeEquiv
    {rho X : ℕ} (hrho : rho ≠ 0) :
    selbergTaperIndex X ≃ selbergSmoothCoprimeIndex rho X where
  toFun n := by
    have hnpos : 0 < n.1 := Nat.zero_lt_of_lt (Finset.mem_Icc.mp n.2).1
    let d := selbergSupportedPart rho n.1
    let k := selbergCoprimePart rho n.1
    have hprod : d * k = n.1 := selbergSupportedPart_mul_coprimePart rho hnpos.ne'
    have hdne : d ≠ 0 := by
      intro hd0
      rw [hd0, zero_mul] at hprod
      exact hnpos.ne' hprod.symm
    have hkne : k ≠ 0 := by
      intro hk0
      rw [hk0, mul_zero] at hprod
      exact hnpos.ne' hprod.symm
    have hdle : d ≤ n.1 := Nat.le_of_dvd hnpos ⟨k, hprod.symm⟩
    have hkle : k ≤ n.1 :=
      Nat.le_of_dvd hnpos ⟨d, by simpa [mul_comm] using hprod.symm⟩
    have hnX : n.1 ≤ X := (Finset.mem_Icc.mp n.2).2
    have hdIcc : d ∈ Finset.Icc 1 X :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hdne, hdle.trans hnX⟩
    have hkIcc : k ∈ Finset.Icc 1 X :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hkne, hkle.trans hnX⟩
    exact ⟨(⟨d, hdIcc⟩, ⟨k, hkIcc⟩),
      selbergSupportedPart_mem_factoredNumbers rho hnpos.ne',
      selbergCoprimePart_coprime hrho hnpos.ne', hprod.le.trans hnX⟩
  invFun p := by
    have hd1 : 1 ≤ p.1.1.1 := (Finset.mem_Icc.mp p.1.1.2).1
    have hk1 : 1 ≤ p.1.2.1 := (Finset.mem_Icc.mp p.1.2.2).1
    exact ⟨p.1.1.1 * p.1.2.1,
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero
          (Nat.one_le_iff_ne_zero.mp hd1)
          (Nat.one_le_iff_ne_zero.mp hk1)), p.2.2.2⟩⟩
  left_inv n := by
    apply Subtype.ext
    exact selbergSupportedPart_mul_coprimePart rho
      (Nat.zero_lt_of_lt (Finset.mem_Icc.mp n.2).1).ne'
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact (selbergSmoothCoprime_decomposition_unique rho
        (Nat.mul_ne_zero
          (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp p.1.1.2).1)
          (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp p.1.2.2).1))
        p.2.1 p.2.2.1 rfl).1.symm
    · apply Subtype.ext
      exact (selbergSmoothCoprime_decomposition_unique rho
        (Nat.mul_ne_zero
          (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp p.1.1.2).1)
          (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp p.1.2.2).1))
        p.2.1 p.2.2.1 rfl).2.symm

noncomputable instance selbergSmoothCoprimeIndexFintype
    (rho X : ℕ) [NeZero rho] : Fintype (selbergSmoothCoprimeIndex rho X) :=
  Fintype.ofEquiv (selbergTaperIndex X)
    (selbergSmoothCoprimeEquiv (NeZero.ne rho))

theorem selbergSmoothCoprimeEquiv_apply_product
    {rho X : ℕ} (hrho : rho ≠ 0) (n : selbergTaperIndex X) :
    (selbergSmoothCoprimeEquiv hrho n).1.1.1 *
        (selbergSmoothCoprimeEquiv hrho n).1.2.1 = n.1 := by
  exact selbergSupportedPart_mul_coprimePart rho
    (Nat.zero_lt_of_lt (Finset.mem_Icc.mp n.2).1).ne'

end HardyTheorem
