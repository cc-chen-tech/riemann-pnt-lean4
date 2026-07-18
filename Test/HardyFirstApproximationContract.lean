import RiemannPNT

example : HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_target_proved

example : HardyTheorem.hardy_theorem_target :=
  HardyTheorem.hardy_theorem_target_proved

example : HardyTheorem.hardy_zeros_unbounded_target :=
  RiemannPNT.API.hardy_zeros_unbounded_target_proved

example : HardyTheorem.hardy_theorem_target :=
  RiemannPNT.API.hardy_theorem_target_proved

example (T : ℝ) :
    HardyTheorem.zeroCountOnCriticalLine T =
      {t : Set.Icc 0 T |
        riemannZeta (0.5 + Complex.I * t) = 0}.ncard :=
  RiemannPNT.API.zeroCountOnCriticalLine_eq_distinct_ncard T
