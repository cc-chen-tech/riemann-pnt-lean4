import PrimeNumberTheorem.VKEdgePiOverTwoLocalized

open Complex Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The logarithmic interval selected by a Gaussian with center `q * m` and
radius `d * m`. -/
def localizedGaussianLogWindow (q d m : ℝ) : Set ℝ :=
  Set.Icc ((q - d) * m) ((q + d) * m)

/-- The power interval with multiplicative width controlled by `ε`. -/
def powerOnePlusEpsilonWindow (ε Y : ℝ) : Set ℝ :=
  Set.Icc Y (Y ^ (1 + ε))

/-- The Gaussian center coefficient for the epsilon power window. -/
def epsilonCenterCoefficient (ε : ℝ) : ℝ :=
  64 * (2 + ε) ^ 2 / ε ^ 2

/-- The Gaussian radius coefficient for the epsilon power window. -/
def epsilonRadiusCoefficient (ε : ℝ) : ℝ :=
  64 * (2 + ε) / ε

/-- The Gaussian scale identifying the localized logarithmic window with the
logarithmic image of the epsilon power window. -/
def epsilonGaussianScale (ε Y : ℝ) : ℝ :=
  Real.log Y /
    (epsilonCenterCoefficient ε - epsilonRadiusCoefficient ε)

theorem epsilonRadiusCoefficient_pos {ε : ℝ} (hε : 0 < ε) :
    0 < epsilonRadiusCoefficient ε := by
  unfold epsilonRadiusCoefficient
  positivity

theorem epsilonRadiusCoefficient_lt_center {ε : ℝ} (hε : 0 < ε) :
    epsilonRadiusCoefficient ε < epsilonCenterCoefficient ε := by
  unfold epsilonCenterCoefficient epsilonRadiusCoefficient
  field_simp [hε.ne']
  nlinarith

theorem epsilonRadius_sq_ge_thirtyTwo_mul {ε : ℝ} (hε : 0 < ε) :
    32 * (epsilonCenterCoefficient ε + epsilonRadiusCoefficient ε) ≤
      epsilonRadiusCoefficient ε ^ 2 := by
  unfold epsilonCenterCoefficient epsilonRadiusCoefficient
  field_simp [hε.ne']
  nlinarith

private theorem epsilon_window_ratio {ε : ℝ} (hε : 0 < ε) :
    (epsilonCenterCoefficient ε + epsilonRadiusCoefficient ε) /
        (epsilonCenterCoefficient ε - epsilonRadiusCoefficient ε) =
      1 + ε := by
  unfold epsilonCenterCoefficient epsilonRadiusCoefficient
  field_simp [hε.ne']
  ring

/-- The selected Gaussian log window is exactly the logarithmic image of the
epsilon power window. -/
theorem localizedGaussianLogWindow_epsilonGaussianScale
    {ε : ℝ} (hε : 0 < ε) (Y : ℝ) :
    localizedGaussianLogWindow
        (epsilonCenterCoefficient ε)
        (epsilonRadiusCoefficient ε)
        (epsilonGaussianScale ε Y) =
      Set.Icc (Real.log Y) ((1 + ε) * Real.log Y) := by
  have hgap : epsilonCenterCoefficient ε - epsilonRadiusCoefficient ε ≠ 0 :=
    ne_of_gt (sub_pos.mpr (epsilonRadiusCoefficient_lt_center hε))
  have hratio := epsilon_window_ratio hε
  have hlower :
      (epsilonCenterCoefficient ε - epsilonRadiusCoefficient ε) *
          (Real.log Y /
            (epsilonCenterCoefficient ε - epsilonRadiusCoefficient ε)) =
        Real.log Y := by
    field_simp [hgap]
  have hupper :
      (epsilonCenterCoefficient ε + epsilonRadiusCoefficient ε) *
          (Real.log Y /
            (epsilonCenterCoefficient ε - epsilonRadiusCoefficient ε)) =
        (1 + ε) * Real.log Y := by
    calc
      (epsilonCenterCoefficient ε + epsilonRadiusCoefficient ε) *
          (Real.log Y /
            (epsilonCenterCoefficient ε - epsilonRadiusCoefficient ε)) =
          ((epsilonCenterCoefficient ε + epsilonRadiusCoefficient ε) /
            (epsilonCenterCoefficient ε - epsilonRadiusCoefficient ε)) *
            Real.log Y := by
        field_simp [hgap]
      _ = (1 + ε) * Real.log Y := by rw [hratio]
  ext y
  simp only [localizedGaussianLogWindow, epsilonGaussianScale, Set.mem_Icc]
  rw [hlower, hupper]

private theorem exp_one_add_epsilon_mul_log {ε Y : ℝ} (hY : 0 < Y) :
    Real.exp ((1 + ε) * Real.log Y) = Y ^ (1 + ε) := by
  rw [Real.rpow_def_of_pos hY]
  congr 1
  ring

/-- A normalized-error witness in the epsilon Gaussian log window gives a
standard Chebyshev-error witness in the corresponding epsilon power window. -/
theorem exists_psiError_in_powerOnePlusEpsilonWindow_of_normalizedPsiError
    {rho : ℂ} {C ε Y : ℝ}
    (hrho : rho ≠ 0) (hε : 0 < ε) (hY : 1 ≤ Y)
    (hlocal :
      ∃ y ∈ localizedGaussianLogWindow
        (epsilonCenterCoefficient ε)
        (epsilonRadiusCoefficient ε)
        (epsilonGaussianScale ε Y),
        C < |normalizedPsiError rho y|) :
    ∃ x ∈ powerOnePlusEpsilonWindow ε Y,
      C * (x ^ rho.re / ‖rho‖) <
        |chebyshevPsi x - x| := by
  rcases hlocal with ⟨y, hyWindow, hyError⟩
  have hYPos : 0 < Y := zero_lt_one.trans_le hY
  rw [localizedGaussianLogWindow_epsilonGaussianScale hε Y] at hyWindow
  have hxLower : Y ≤ Real.exp y :=
    (Real.log_le_iff_le_exp hYPos).mp hyWindow.1
  have hxUpper : Real.exp y ≤ Y ^ (1 + ε) := by
    calc
      Real.exp y ≤ Real.exp ((1 + ε) * Real.log Y) :=
        Real.exp_le_exp.mpr hyWindow.2
      _ = Y ^ (1 + ε) := exp_one_add_epsilon_mul_log hYPos
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
