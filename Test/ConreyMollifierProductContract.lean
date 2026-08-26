import HardyTheorem.ConreyMollifierProduct

open Complex

namespace HardyTheorem

example {Y : ℕ} {P : ℝ → ℝ} (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (sigma0 : ℝ) :
    conreyMollifierCoefficient Y sigma0 P 1 = 1 :=
  conreyMollifierCoefficient_one hY hP1 sigma0

example (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ) (s : ℂ) :
    conreyMollifier Y sigma0 P s =
      ∑ n ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius n : ℂ) *
          (P (Real.log ((Y : ℝ) / (n : ℝ)) / Real.log Y) : ℂ) *
          (n : ℂ) ^ ((sigma0 - 1 / 2 : ℝ) : ℂ) /
          (n : ℂ) ^ s :=
  conreyMollifier_eq_conrey_formula Y sigma0 P s

example (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ) :
    AnalyticOnNhd ℂ (conreyMollifier Y sigma0 P) Set.univ :=
  analyticOnNhd_conreyMollifier Y sigma0 P

example {Y : ℕ} {P : ℝ → ℝ} (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (sigma0 : ℝ) :
    Filter.Tendsto (fun sigma : ℝ =>
      conreyMollifier Y sigma0 P (sigma : ℂ)) Filter.atTop (nhds 1) :=
  tendsto_conreyMollifier_real_atTop hY hP1 sigma0

example {Y : ℕ} {P : ℝ → ℝ} (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (sigma0 : ℝ) (s : ℂ) :
    analyticOrderAt (conreyMollifier Y sigma0 P) s ≠ ⊤ :=
  analyticOrderAt_conreyMollifier_ne_top hY hP1 sigma0 s

example (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ)
    (P : ℝ → ℝ) (s : ℂ) :
    conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s =
      conreyDegreeOneV1 g g0 g1 L s *
        conreyMollifier Y sigma0 P s :=
  conreyMollifiedDegreeOneV1_eq g g0 g1 L Y sigma0 P s

example {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ} {s : ℂ}
    (hzero : conreyDegreeOneV1 g g0 g1 L s = 0) :
    conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s = 0 :=
  conreyMollifiedDegreeOneV1_eq_zero_of_v1_eq_zero hzero

example {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1)
    (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hVfinite : analyticOrderAt (conreyDegreeOneV1 g g0 g1 L) s ≠ ⊤) :
    analyticOrderNatAt (conreyDegreeOneV1 g g0 g1 L) s ≤
      analyticOrderNatAt
        (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) s :=
  analyticOrderNatAt_conreyDegreeOneV1_le_mollified
    hs0 hs1 hY hP1 hVfinite

#print axioms conreyMollifierCoefficient_one
#print axioms conreyMollifier_eq_conrey_formula
#print axioms tendsto_conreyMollifier_real_atTop
#print axioms analyticOrderAt_conreyMollifier_ne_top
#print axioms analyticOrderNatAt_conreyDegreeOneV1_le_mollified

end HardyTheorem
