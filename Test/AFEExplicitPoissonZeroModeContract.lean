import HardyTheorem.AFEExplicitPoissonZeroMode

open HardyTheorem AFE Complex MeasureTheory

-- Exact principal-power core, with only the two unit transition errors.
example {s : ℂ} {x N : ℝ} (hs : 0 ≤ s.re) (hs1 : s ≠ 1)
    (hx : 1 < x) (hxN : x ≤ N) :
    ‖(∫ u in (x - 1)..(N + 1), explicitWeightedPoissonCutoff s x N u) -
      ((N : ℂ) ^ (1 - s) - (x : ℂ) ^ (1 - s)) / (1 - s)‖ ≤
        (x - 1) ^ (-s.re) + N ^ (-s.re) :=
  norm_explicitWeightedPoissonIntegral_sub_core_le hs hs1 hx hxN

-- The divergent upper main term is subtracted, not separately sent to a limit.
example {sigma x N t : ℝ} (hs : 0 ≤ sigma) (hx : 1 < x) (hxN : x ≤ N)
    (ht : 0 < t) :
    let s : ℂ := (sigma : ℂ) + I * t
    ‖explicitPoissonMode sigma x N t 0 - (N : ℂ) ^ (1 - s) / (1 - s)‖ ≤
      (x - 1) ^ (-sigma) + N ^ (-sigma) + x ^ (1 - sigma) / t :=
  norm_explicitPoissonZeroMode_sub_main_le hs hx hxN ht

#print axioms norm_explicitWeightedPoissonIntegral_sub_core_le
#print axioms norm_explicitPoissonZeroMode_sub_main_le
