import HardyTheorem.SelbergJReverseBridge

namespace HardyTheorem

/-! # The exact positive gcd-ray parametrization of the diagonal equation -/

theorem selberg_diagonal_equation_iff_unique_gcd_ray
    {A B m n : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hm : 1 ≤ m) (_hn : 1 ≤ n) :
    m * A = n * B ↔
      ∃! r : ℕ, 1 ≤ r ∧
        m = r * (B / Nat.gcd A B) ∧
        n = r * (A / Nat.gcd A B) := by
  let g := Nat.gcd A B
  let A' := A / g
  let B' := B / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left B (zero_lt_one.trans_le hA)
  have hgA : g * A' = A := by
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)
  have hgB : g * B' = B := by
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)
  have hA' : 0 < A' := by
    have hgA_le : g ≤ A := Nat.le_of_dvd (zero_lt_one.trans_le hA)
      (Nat.gcd_dvd_left A B)
    exact Nat.div_pos hgA_le hg
  have hB' : 0 < B' := by
    have hgB_le : g ≤ B := Nat.le_of_dvd (zero_lt_one.trans_le hB)
      (Nat.gcd_dvd_right A B)
    exact Nat.div_pos hgB_le hg
  have hcop : A'.Coprime B' := by
    exact Nat.coprime_div_gcd_div_gcd hg
  constructor
  · intro heq
    have hreduced : m * A' = n * B' := by
      apply Nat.eq_of_mul_eq_mul_left hg
      calc
        g * (m * A') = m * (g * A') := by ring
        _ = m * A := by rw [hgA]
        _ = n * B := heq
        _ = n * (g * B') := by rw [hgB]
        _ = g * (n * B') := by ring
    have hBdvd : B' ∣ m := by
      apply hcop.symm.dvd_of_dvd_mul_right
      rw [hreduced]
      exact Nat.dvd_mul_left B' n
    let r := m / B'
    have hmFactor : m = r * B' := by
      simpa only [r, Nat.mul_comm] using (Nat.mul_div_cancel' hBdvd).symm
    have hnFactor : n = r * A' := by
      apply Nat.eq_of_mul_eq_mul_right hB'
      calc
        n * B' = m * A' := hreduced.symm
        _ = (r * A') * B' := by rw [hmFactor]; ring
    have hr : 1 ≤ r := by
      have hr0 : r ≠ 0 := by
        intro hrzero
        rw [hrzero, zero_mul] at hmFactor
        omega
      exact Nat.one_le_iff_ne_zero.mpr hr0
    refine ⟨r, ⟨hr, hmFactor, hnFactor⟩, ?_⟩
    intro s hs
    apply Nat.eq_of_mul_eq_mul_right hB'
    rw [← hmFactor, hs.2.1]
  · rintro ⟨r, ⟨hr, hmFactor, hnFactor⟩, hunique⟩
    have hmFactor' : m = r * B' := by
      simpa only [B', g] using hmFactor
    have hnFactor' : n = r * A' := by
      simpa only [A', g] using hnFactor
    calc
      m * A = (r * B') * (g * A') := by rw [hmFactor', hgA]
      _ = (r * A') * (g * B') := by ring
      _ = n * B := by rw [← hnFactor', hgB]

end HardyTheorem
