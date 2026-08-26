import HardyTheorem.ConreyDegreeOneNontrivial
import HardyTheorem.ConreyMollifierProduct

open Complex

namespace HardyTheorem

example (g g0 g1 L : ℝ) :
    AnalyticOnNhd ℂ (conreyDegreeOneEta g g0 g1 L) Set.univ :=
  analyticOnNhd_conreyDegreeOneEta g g0 g1 L

example {g g0 g1 L : ℝ} (hg : g ≠ 0) :
    ∃ s : ℂ, conreyDegreeOneEta g g0 g1 L s ≠ 0 :=
  exists_conreyDegreeOneEta_ne_zero_of_g_ne_zero hg

example {g g0 g1 L : ℝ} (hg : g ≠ 0) (s : ℂ) :
    analyticOrderAt (conreyDegreeOneEta g g0 g1 L) s ≠ ⊤ :=
  analyticOrderAt_conreyDegreeOneEta_ne_top_of_g_ne_zero hg s

example {g g0 g1 L : ℝ} (hg : g ≠ 0) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt (conreyDegreeOneV1 g g0 g1 L) s ≠ ⊤ :=
  analyticOrderAt_conreyDegreeOneV1_ne_top_of_g_ne_zero hg hs0 hs1

example {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ} {s : ℂ}
    (hg : g ≠ 0) (hs0 : 0 < s.re) (hs1 : s ≠ 1)
    (hY : 2 ≤ Y) (hP1 : P 1 = 1) :
    analyticOrderNatAt (conreyDegreeOneV1 g g0 g1 L) s ≤
      analyticOrderNatAt
        (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) s :=
  analyticOrderNatAt_conreyDegreeOneV1_le_mollified_of_g_ne_zero
    hg hs0 hs1 hY hP1

#print axioms analyticOnNhd_conreyDegreeOneEta
#print axioms exists_conreyDegreeOneEta_ne_zero_of_g_ne_zero
#print axioms analyticOrderAt_conreyDegreeOneEta_ne_top_of_g_ne_zero
#print axioms analyticOrderAt_conreyDegreeOneV1_ne_top_of_g_ne_zero
#print axioms analyticOrderNatAt_conreyDegreeOneV1_le_mollified_of_g_ne_zero

end HardyTheorem
