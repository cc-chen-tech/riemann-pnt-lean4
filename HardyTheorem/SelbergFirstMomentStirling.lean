import HardyTheorem.SelbergFirstMomentHorizontal
import HardyTheorem.VerticalGammaAsymptotic

open Complex

namespace HardyTheorem

/-!
# Uniform archimedean lower bound for Selberg's first moment

The vertical Stirling theorem supplies the exact exponential scale.  On a
dyadic interval `T / 2 <= t <= T`, a tilt `0 <= delta <= 1 / T` loses only
the fixed factor `exp (-1/2)`, while the negative quarter power is bounded
below by its value at `T`.
-/

/-- The Gamma factor and Selberg tilt are uniformly bounded below by the
dyadic scale `T^(-1/4)`. -/
theorem exists_pos_rpow_neg_quarter_le_norm_GammaR_mul_selbergTilt :
    ∃ c : ℝ, 0 < c ∧
      ∀ T delta t : ℝ,
        2 ≤ T → 0 ≤ delta → delta ≤ 1 / T →
        T / 2 ≤ t → t ≤ T →
        c * T ^ (-(1 / 4 : ℝ)) ≤
          ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ *
            Real.exp ((Real.pi / 4 - delta / 2) * t) := by
  obtain ⟨A, hA, hstirling⟩ :=
    exists_pos_rpow_neg_quarter_mul_exp_le_norm_GammaR
  refine ⟨A * Real.exp (-(1 / 2 : ℝ)), by positivity, ?_⟩
  intro T delta t hT hdelta0 hdelta hlow hhigh
  have hT0 : 0 < T := by linarith
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hraw := hstirling t ht1
  have hpow : T ^ (-(1 / 4 : ℝ)) ≤ t ^ (-(1 / 4 : ℝ)) := by
    exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)
      (Set.mem_Ioi.mpr ht0) (Set.mem_Ioi.mpr hT0) hhigh
  have hdeltat : delta * t ≤ 1 := by
    calc
      delta * t ≤ (1 / T) * t :=
        mul_le_mul_of_nonneg_right hdelta ht0.le
      _ ≤ (1 / T) * T :=
        mul_le_mul_of_nonneg_left hhigh (one_div_nonneg.mpr hT0.le)
      _ = 1 := by field_simp [hT0.ne']
  have hexpTilt : Real.exp (-(1 / 2 : ℝ)) ≤
      Real.exp (-delta * t / 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hraw
    (Real.exp_pos ((Real.pi / 4 - delta / 2) * t)).le
  calc
    (A * Real.exp (-(1 / 2 : ℝ))) * T ^ (-(1 / 4 : ℝ)) ≤
        A * t ^ (-(1 / 4 : ℝ)) * Real.exp (-delta * t / 2) := by
      have hAnonneg : 0 ≤ A := hA.le
      have hTpow : 0 ≤ T ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg hT0.le _
      have htpow : 0 ≤ t ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg ht0.le _
      calc
        (A * Real.exp (-(1 / 2 : ℝ))) * T ^ (-(1 / 4 : ℝ)) =
            A * (T ^ (-(1 / 4 : ℝ)) * Real.exp (-(1 / 2 : ℝ))) := by ring
        _ ≤ A * (t ^ (-(1 / 4 : ℝ)) * Real.exp (-delta * t / 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hpow hexpTilt
              (Real.exp_pos (-(1 / 2 : ℝ))).le htpow) hAnonneg
        _ = A * t ^ (-(1 / 4 : ℝ)) * Real.exp (-delta * t / 2) := by ring
    _ = (A * t ^ (-(1 / 4 : ℝ)) * Real.exp (-Real.pi * t / 4)) *
        Real.exp ((Real.pi / 4 - delta / 2) * t) := by
      rw [show
        (A * t ^ (-(1 / 4 : ℝ)) * Real.exp (-Real.pi * t / 4)) *
            Real.exp ((Real.pi / 4 - delta / 2) * t) =
          A * t ^ (-(1 / 4 : ℝ)) *
            (Real.exp (-Real.pi * t / 4) *
              Real.exp ((Real.pi / 4 - delta / 2) * t)) by ring]
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ *
        Real.exp ((Real.pi / 4 - delta / 2) * t) := hscaled

end HardyTheorem
