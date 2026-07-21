import Mathlib

namespace MathlibAux

/-- Every real scale at least one lies in a half-open dyadic interval. -/
theorem exists_nat_pow_two_le_lt_pow_two {r : ℝ} (hr : 1 ≤ r) :
    ∃ K : ℕ, (2 : ℝ) ^ K ≤ r ∧ r < (2 : ℝ) ^ (K + 1) := by
  let n : ℕ := ⌊r⌋₊
  have hnpos : 0 < n := Nat.floor_pos.mpr hr
  refine ⟨n.log2, ?_, ?_⟩
  · have hpow : 2 ^ n.log2 ≤ n := Nat.log2_self_le (Nat.ne_of_gt hnpos)
    have hpowReal : (2 : ℝ) ^ n.log2 ≤ (n : ℝ) := by
      exact_mod_cast hpow
    have hfloor : (n : ℝ) ≤ r := Nat.floor_le (by linarith)
    exact hpowReal.trans hfloor
  · have hpow : n + 1 ≤ 2 ^ (n.log2 + 1) := Nat.succ_le_iff.mpr Nat.lt_log2_self
    have hpowReal : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (n.log2 + 1) := by
      exact_mod_cast hpow
    have hfloor : r < (n : ℝ) + 1 := Nat.lt_floor_add_one r
    exact hfloor.trans_le hpowReal

end MathlibAux
