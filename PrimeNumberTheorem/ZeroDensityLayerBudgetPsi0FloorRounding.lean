import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTUnnormalizedTargetAmplitudeTransfer

namespace PrimeNumberTheorem

/--
The right-continuous Chebyshev function is unchanged when its real argument is
replaced by its natural floor.
-/
theorem chebyshevPsi_eq_natFloor (x : ℝ) :
    chebyshevPsi x = chebyshevPsi (Nat.floor x : ℝ) := by
  simp [chebyshevPsi]

/--
Explicit loss incurred by replacing a real point with its natural floor in
the midpoint-convention PNT error.

The first two terms are the possible half jumps at the two endpoints; the
last term is the change in the identity main term.
-/
noncomputable def chebyshevPsi0FloorRoundingBudget (x : ℝ) : ℝ :=
  |jumpVonMangoldt x| / 2 +
    |jumpVonMangoldt (Nat.floor x : ℝ)| / 2 +
      |x - (Nat.floor x : ℝ)|

theorem chebyshevPsi0FloorRoundingBudget_nonneg (x : ℝ) :
    0 ≤ chebyshevPsi0FloorRoundingBudget x := by
  unfold chebyshevPsi0FloorRoundingBudget
  positivity

/--
The actual midpoint PNT error changes by at most the explicit floor-rounding
budget.
-/
theorem abs_chebyshevPsi0Error_sub_natFloor_le (x : ℝ) :
    |chebyshevPsi0Error x -
        chebyshevPsi0Error (Nat.floor x : ℝ)| ≤
      chebyshevPsi0FloorRoundingBudget x := by
  rw [chebyshevPsi0Error, chebyshevPsi0Error, chebyshevPsi0,
    chebyshevPsi0, chebyshevPsi_eq_natFloor]
  calc
    |(chebyshevPsi (Nat.floor x : ℝ) - jumpVonMangoldt x / 2 - x) -
          (chebyshevPsi (Nat.floor x : ℝ) -
            jumpVonMangoldt (Nat.floor x : ℝ) / 2 -
              (Nat.floor x : ℝ))|
        =
        |(jumpVonMangoldt (Nat.floor x : ℝ) / 2 -
            jumpVonMangoldt x / 2) +
          ((Nat.floor x : ℝ) - x)| := by
            congr 1
            ring
    _ ≤
        |jumpVonMangoldt (Nat.floor x : ℝ) / 2 -
            jumpVonMangoldt x / 2| +
          |(Nat.floor x : ℝ) - x| :=
      abs_add_le _ _
    _ ≤
        (|jumpVonMangoldt (Nat.floor x : ℝ) / 2| +
            |jumpVonMangoldt x / 2|) +
          |(Nat.floor x : ℝ) - x| := by
      gcongr
      exact abs_sub _ _
    _ = chebyshevPsi0FloorRoundingBudget x := by
      rw [abs_div, abs_div]
      norm_num
      rw [abs_sub_comm]
      unfold chebyshevPsi0FloorRoundingBudget
      ring

/--
Reverse-triangle form: every real PNT-error witness survives at the natural
floor after subtracting the explicit rounding budget.
-/
theorem abs_chebyshevPsi0Error_sub_roundingBudget_le_abs_natFloor
    (x : ℝ) :
    |chebyshevPsi0Error x| - chebyshevPsi0FloorRoundingBudget x ≤
      |chebyshevPsi0Error (Nat.floor x : ℝ)| := by
  have hdiff := abs_chebyshevPsi0Error_sub_natFloor_le x
  have htriangle :
      |chebyshevPsi0Error x| ≤
        |chebyshevPsi0Error x -
            chebyshevPsi0Error (Nat.floor x : ℝ)| +
          |chebyshevPsi0Error (Nat.floor x : ℝ)| := by
    calc
      |chebyshevPsi0Error x| =
          |(chebyshevPsi0Error x -
              chebyshevPsi0Error (Nat.floor x : ℝ)) +
            chebyshevPsi0Error (Nat.floor x : ℝ)| := by
              congr 1
              ring
      _ ≤
          |chebyshevPsi0Error x -
              chebyshevPsi0Error (Nat.floor x : ℝ)| +
            |chebyshevPsi0Error (Nat.floor x : ℝ)| :=
        abs_add_le _ _
  linarith

/--
Continuous logarithmic witnesses at `x = exp y` transfer quantitatively to
the natural point `floor (exp y)`.
-/
theorem continuousExpPsi0Witness_to_natFloor
    {y amplitude : ℝ}
    (hwitness :
      amplitude ≤ |chebyshevPsi0Error (Real.exp y)|) :
    amplitude - chebyshevPsi0FloorRoundingBudget (Real.exp y) ≤
      |chebyshevPsi0Error (Nat.floor (Real.exp y) : ℝ)| := by
  have hfloor :=
    abs_chebyshevPsi0Error_sub_roundingBudget_le_abs_natFloor
      (Real.exp y)
  linarith

end PrimeNumberTheorem
