import HardyTheorem.ConreyV1RightEdge

open Complex

namespace HardyTheorem

noncomputable section

example (g g0 g1 L t : ℝ) : ℂ :=
  conreyDegreeOneHeightMain g g0 g1 L t

example (g g0 g1 L t : ℝ) {s : ℂ} :
    conreyDegreeOneV1 g g0 g1 L s -
        conreyDegreeOneHeightMain g g0 g1 L t =
      conreyDegreeOneHeightMain g g0 g1 L t * (riemannZeta s - 1) +
        ((g1 / L : ℝ) : ℂ) * deriv riemannZeta s +
        ((g1 / L : ℝ) : ℂ) *
          (deriv conreyH s / conreyH s -
            ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)) * riemannZeta s :=
  conreyDegreeOneV1_sub_heightMain_eq g g0 g1 L t s

example {g g0 g1 L t : ℝ} {s : ℂ}
    (hL : Real.exp 2 ≤ L)
    (hre : s.re = 2 * Real.log L) (him : s.im = t)
    (ht : 2 ≤ t) (hst : s.re ≤ t) :
    ‖conreyDegreeOneV1 g g0 g1 L s -
        conreyDegreeOneHeightMain g g0 g1 L t‖ ≤
      (3 * ‖conreyDegreeOneHeightMain g g0 g1 L t‖ + 34 * |g1|) / L :=
  norm_conreyDegreeOneV1_sub_heightMain_movingRight_le hL hre him ht hst

#print axioms conreyDegreeOneHeightMain
#print axioms conreyDegreeOneV1_sub_heightMain_eq
#print axioms norm_conreyDegreeOneV1_sub_heightMain_movingRight_le

end
end HardyTheorem
