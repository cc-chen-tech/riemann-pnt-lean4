import HardyTheorem.AFECriticalCanonical

/-!
# Stability of the square-root AFE cutoff on short height windows

The sharp square-root cutoff is not literally constant in the height.  The
right finite decomposition is nevertheless uniform on a short window: if
the coordinate `sqrt (t / (2*pi))` moves by less than one, its natural floor
can take at most two adjacent values.  This file proves that statement with
all floor and endpoint normalizations explicit.
-/

open Set

namespace HardyTheorem
namespace AFE

/-- A nonnegative real lying in the half-open unit window `[a,a+1)` has
natural floor equal to `floor a` or its successor. -/
theorem natFloor_eq_floor_or_succ_of_mem_unitWindow
    {a y : ℝ} (ha : 0 ≤ a) (hay : a ≤ y) (hya : y < a + 1) :
    Nat.floor y = Nat.floor a ∨ Nat.floor y = Nat.floor a + 1 := by
  have hy : 0 ≤ y := ha.trans hay
  have hlower : Nat.floor a ≤ Nat.floor y := Nat.floor_mono hay
  have haFloor : a < (Nat.floor a : ℝ) + 1 := Nat.lt_floor_add_one a
  have hyUpper : y < ((Nat.floor a + 2 : ℕ) : ℝ) := by
    calc
      y < a + 1 := hya
      _ < ((Nat.floor a : ℝ) + 1) + 1 := by linarith
      _ = ((Nat.floor a + 2 : ℕ) : ℝ) := by push_cast; ring
  have hupperLt : Nat.floor y < Nat.floor a + 2 :=
    (Nat.floor_lt hy).2 hyUpper
  omega

/-- On a height interval whose square-root AFE coordinate has width less
than one, every cutoff is the left-end cutoff or its successor. -/
theorem criticalAfeCutoff_eq_left_or_succ_of_mem_interval
    {L U t : ℝ} (_hL : 0 ≤ L) (ht : t ∈ Icc L U)
    (hwidth :
      Real.sqrt (U / (2 * Real.pi)) <
        Real.sqrt (L / (2 * Real.pi)) + 1) :
    criticalAfeCutoff t = criticalAfeCutoff L ∨
      criticalAfeCutoff t = criticalAfeCutoff L + 1 := by
  have hc : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hLt : L / (2 * Real.pi) ≤ t / (2 * Real.pi) :=
    (div_le_div_iff_of_pos_right hc).2 ht.1
  have htU : t / (2 * Real.pi) ≤ U / (2 * Real.pi) :=
    (div_le_div_iff_of_pos_right hc).2 ht.2
  have ha : 0 ≤ Real.sqrt (L / (2 * Real.pi)) := Real.sqrt_nonneg _
  have hlow :
      Real.sqrt (L / (2 * Real.pi)) ≤
        Real.sqrt (t / (2 * Real.pi)) :=
    Real.sqrt_le_sqrt hLt
  have hupp :
      Real.sqrt (t / (2 * Real.pi)) <
        Real.sqrt (L / (2 * Real.pi)) + 1 :=
    (Real.sqrt_le_sqrt htU).trans_lt hwidth
  simpa [criticalAfeCutoff] using
    natFloor_eq_floor_or_succ_of_mem_unitWindow ha hlow hupp

end AFE
end HardyTheorem
