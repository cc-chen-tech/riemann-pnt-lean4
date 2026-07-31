import PrimeNumberTheorem.VKEdgePiOverTwoAbelPhase

open Complex Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The logarithmic interval selected by the Gaussian centered at `16m`,
with tails cut at distance `12m`. -/
def gaussianLogWindow (m : ℝ) : Set ℝ :=
  Set.Icc (4 * m) (28 * m)

/-- The logarithmic image of the power interval `[Y, Y^7]`. -/
def logarithmicPowerSevenWindow (Y : ℝ) : Set ℝ :=
  Set.Icc (Real.log Y) (7 * Real.log Y)

/-- The fixed power interval used by the localized oscillation argument. -/
def powerSevenWindow (Y : ℝ) : Set ℝ :=
  Set.Icc Y (Y ^ (7 : ℕ))

/-- Choosing `m = log Y / 4` identifies the Gaussian localization window
exactly with the logarithmic image of `[Y, Y^7]`. -/
theorem gaussianLogWindow_log_div_four (Y : ℝ) :
    gaussianLogWindow (Real.log Y / 4) =
      logarithmicPowerSevenWindow Y := by
  ext y
  simp only [gaussianLogWindow, logarithmicPowerSevenWindow, Set.mem_Icc]
  constructor <;> rintro ⟨hyLower, hyUpper⟩
  · constructor <;> nlinarith
  · constructor <;> nlinarith

private theorem exp_seven_mul_log {Y : ℝ} (hY : 0 < Y) :
    Real.exp (7 * Real.log Y) = Y ^ (7 : ℕ) := by
  rw [show 7 * Real.log Y = (7 : ℕ) * Real.log Y by norm_num]
  rw [Real.exp_nat_mul, Real.exp_log hY]

/-- A logarithmic-scale witness for the normalized PNT error gives a witness
for the ordinary Chebyshev error in `[Y,Y^7]`.  This uses an approximate
supremum witness only; no continuity of the step function `chebyshevPsi` is
required. -/
theorem exists_psiError_in_powerSevenWindow_of_normalizedPsiError
    {rho : ℂ} {C Y : ℝ}
    (hrho : rho ≠ 0) (hY : 1 ≤ Y)
    (hlocal :
      ∃ y ∈ logarithmicPowerSevenWindow Y,
        C < |normalizedPsiError rho y|) :
    ∃ x ∈ powerSevenWindow Y,
      C * (x ^ rho.re / ‖rho‖) <
        |chebyshevPsi x - x| := by
  rcases hlocal with ⟨y, hyWindow, hyError⟩
  have hYPos : 0 < Y := zero_lt_one.trans_le hY
  have hxLower : Y ≤ Real.exp y :=
    (Real.log_le_iff_le_exp hYPos).mp hyWindow.1
  have hxUpper : Real.exp y ≤ Y ^ (7 : ℕ) := by
    calc
      Real.exp y ≤ Real.exp (7 * Real.log Y) :=
        Real.exp_le_exp.mpr hyWindow.2
      _ = Y ^ (7 : ℕ) := exp_seven_mul_log hYPos
  refine ⟨Real.exp y, ⟨hxLower, hxUpper⟩, ?_⟩
  have hnormPos : (0 : ℝ) < ‖rho‖ := norm_pos_iff.mpr hrho
  rw [normalizedPsiError, abs_mul, abs_mul,
    abs_of_nonneg (norm_nonneg rho),
    abs_of_pos (Real.exp_pos _)] at hyError
  have hxpow :
      (Real.exp y) ^ rho.re =
        Real.exp (rho.re * y) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp]
    congr 1
    ring
  have hexpCancel :
      Real.exp (-rho.re * y) *
          Real.exp (rho.re * y) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  have hscaled :
      C * Real.exp (rho.re * y) <
        ‖rho‖ * |chebyshevPsi (Real.exp y) - Real.exp y| := by
    calc
      C * Real.exp (rho.re * y) <
          (‖rho‖ *
              |chebyshevPsi (Real.exp y) - Real.exp y| *
              Real.exp (-rho.re * y)) *
            Real.exp (rho.re * y) :=
        mul_lt_mul_of_pos_right hyError
          (Real.exp_pos (rho.re * y))
      _ = ‖rho‖ *
          |chebyshevPsi (Real.exp y) - Real.exp y| := by
        calc
          (‖rho‖ *
                |chebyshevPsi (Real.exp y) - Real.exp y| *
                Real.exp (-rho.re * y)) *
              Real.exp (rho.re * y) =
            (‖rho‖ *
                |chebyshevPsi (Real.exp y) - Real.exp y|) *
              (Real.exp (-rho.re * y) *
                Real.exp (rho.re * y)) := by ring
          _ = ‖rho‖ *
              |chebyshevPsi (Real.exp y) - Real.exp y| := by
            rw [hexpCancel]
            ring
  have hdiv :
      (C * (Real.exp y) ^ rho.re) / ‖rho‖ <
        |chebyshevPsi (Real.exp y) - Real.exp y| := by
    rw [hxpow]
    exact (div_lt_iff₀ hnormPos).2 (by
      simpa [mul_comm] using hscaled)
  change
    C * ((Real.exp y) ^ rho.re / ‖rho‖) <
      |chebyshevPsi (Real.exp y) - Real.exp y|
  calc
    C * ((Real.exp y) ^ rho.re / ‖rho‖) =
        (C * (Real.exp y) ^ rho.re) / ‖rho‖ := by ring
    _ < |chebyshevPsi (Real.exp y) - Real.exp y| := hdiv

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
