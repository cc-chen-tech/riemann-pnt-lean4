import PrimeNumberTheorem.MWKFCubicEulerSeparateHolomorphic
import ZeroFreeRegion.MeromorphicAux

open Complex

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Pole-unit factorization of the cubic Euler integrand

This file inserts the analytic pole unit at `1` into the actual zeta quotient
from the cubic Selberg--Perron series.  The three linear factors
`s + t`, `s + w`, and `t + w` are thereby separated from a unit core whose
central value is exactly one.  This identifies, without an asymptotic
argument, the algebraic source of the extra constant in the differentiated
diagonal term.

No contour displacement, boundary decay, residue summation, or off-diagonal
estimate is asserted here.
-/

/-- The analytic unit left after removing the three explicit linear factors
from the zeta quotient and adjoining the convergent Euler correction. -/
noncomputable def mwkfEulerPoleUnitCore (s t w : ℂ) : ℂ :=
  ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + s + t) /
      (ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + s + w) *
        ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + t + w)) *
    mwkfEulerCorrection s t w

/-- The pole-normal form of the zeta quotient times the Euler correction. -/
noncomputable def mwkfEulerPoleModel (s t w : ℂ) : ℂ :=
  ((s + w) * (t + w) / (s + t)) * mwkfEulerPoleUnitCore s t w

/-- The pole-unit core is normalized to one at the central point. -/
theorem mwkfEulerPoleUnitCore_zero : mwkfEulerPoleUnitCore 0 0 0 = 1 := by
  simp [mwkfEulerPoleUnitCore,
    ZeroFreeRegion.riemannZetaPoleUnitAtOne_one,
    mwkfEulerCorrection_zero]

/-- For fixed `s,t` in the Euler strip, the pole-unit core is analytic in the
third variable at zero as soon as the two denominator units do not vanish.
The hypotheses `0 < eta < 1/4` place both shifted zeta arguments in the
half-plane where the pole unit is analytic and put zero inside the correction
half-plane. -/
theorem analyticAt_mwkfEulerPoleUnitCore_in_third_zero
    {eta : ℝ} (hetaPos : 0 < eta) (hetaQuarter : eta < 1 / 4)
    {s t : ℂ} (hs : -eta < s.re) (ht : -eta < t.re)
    (hQs : ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + s) ≠ 0)
    (hQt : ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + t) ≠ 0) :
    AnalyticAt ℂ (fun w ↦ mwkfEulerPoleUnitCore s t w) 0 := by
  have hsPos : 0 < (1 + s).re := by
    change 0 < 1 + s.re
    linarith
  have htPos : 0 < (1 + t).re := by
    change 0 < 1 + t.re
    linarith
  have hQsw : AnalyticAt ℂ
      (fun w : ℂ ↦ ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + s + w)) 0 := by
    have haffine : AnalyticAt ℂ (fun w : ℂ ↦ 1 + s + w) 0 := by
      fun_prop
    have hQat : AnalyticAt ℂ ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + s) := by
      apply ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
        (θ := 0) le_rfl
      exact hsPos
    change AnalyticAt ℂ
      (ZeroFreeRegion.riemannZetaPoleUnitAtOne ∘ fun w : ℂ ↦ 1 + s + w) 0
    exact hQat.comp_of_eq haffine (by simp)
  have hQtw : AnalyticAt ℂ
      (fun w : ℂ ↦ ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + t + w)) 0 := by
    have haffine : AnalyticAt ℂ (fun w : ℂ ↦ 1 + t + w) 0 := by
      fun_prop
    have hQat : AnalyticAt ℂ ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + t) := by
      apply ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
        (θ := 0) le_rfl
      exact htPos
    change AnalyticAt ℂ
      (ZeroFreeRegion.riemannZetaPoleUnitAtOne ∘ fun w : ℂ ↦ 1 + t + w) 0
    exact hQat.comp_of_eq haffine (by simp)
  have hH : AnalyticAt ℂ (fun w ↦ mwkfEulerCorrection s t w) 0 :=
    analyticOnNhd_mwkfEulerCorrection_in_third hetaQuarter hs ht 0
      (by simp [mwkfEulerHalfPlane]; linarith)
  unfold mwkfEulerPoleUnitCore
  have hden :
      (fun w : ℂ ↦ ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + s + w)) 0 *
          (fun w : ℂ ↦ ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + t + w)) 0 ≠ 0 := by
    simpa using mul_ne_zero hQs hQt
  exact (analyticAt_const.div (hQsw.mul hQtw) hden).mul hH

/-- Away from the three explicit hyperplanes and the two denominator zeros,
the original zeta quotient times the global correction is exactly its
pole-unit normal form. -/
theorem mwkfZetaRatio_mul_correction_eq_poleModel
    {s t w : ℂ}
    (hst : s + t ≠ 0) (hsw : s + w ≠ 0) (htw : t + w ≠ 0)
    (honeSt : 1 + s + t ≠ 0)
    (honeSw : 1 + s + w ≠ 0)
    (honeTw : 1 + t + w ≠ 0)
    (hzSw : riemannZeta (1 + s + w) ≠ 0)
    (hzTw : riemannZeta (1 + t + w) ≠ 0) :
    riemannZeta (1 + s + t) /
          (riemannZeta (1 + s + w) * riemannZeta (1 + t + w)) *
        mwkfEulerCorrection s t w =
      mwkfEulerPoleModel s t w := by
  have hqSt := ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
    honeSt (by simpa [add_assoc] using hst)
  have hqSw := ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
    honeSw (by simpa [add_assoc] using hsw)
  have hqTw := ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
    honeTw (by simpa [add_assoc] using htw)
  have hqSt' :
      ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + s + t) =
        (s + t) * riemannZeta (1 + s + t) := by
    calc
      _ = (1 + s + t - 1) * riemannZeta (1 + s + t) := hqSt
      _ = _ := by ring
  have hqSw' :
      ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + s + w) =
        (s + w) * riemannZeta (1 + s + w) := by
    calc
      _ = (1 + s + w - 1) * riemannZeta (1 + s + w) := hqSw
      _ = _ := by ring
  have hqTw' :
      ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + t + w) =
        (t + w) * riemannZeta (1 + t + w) := by
    calc
      _ = (1 + t + w - 1) * riemannZeta (1 + t + w) := hqTw
      _ = _ := by ring
  unfold mwkfEulerPoleModel mwkfEulerPoleUnitCore
  rw [hqSt', hqSw', hqTw']
  field_simp [hst, hsw, htw, hzSw, hzTw]

/-- Differentiating the pole model in `w` at zero exposes a leading copy of
the unit core.  Since that core equals one at the center, this is the exact
algebraic source of the extra `1` in the cubic diagonal main term. -/
theorem deriv_mwkfEulerPoleModel_in_third_zero
    {s t : ℂ} (hst : s + t ≠ 0)
    (hcore : AnalyticAt ℂ (fun w ↦ mwkfEulerPoleUnitCore s t w) 0) :
    deriv (fun w ↦ mwkfEulerPoleModel s t w) 0 =
      mwkfEulerPoleUnitCore s t 0 +
        (s * t / (s + t)) *
          deriv (fun w ↦ mwkfEulerPoleUnitCore s t w) 0 := by
  have hpole : DifferentiableAt ℂ
      (fun w : ℂ ↦ (s + w) * (t + w) / (s + t)) 0 := by
    fun_prop
  unfold mwkfEulerPoleModel
  change deriv
      ((fun w : ℂ ↦ (s + w) * (t + w) / (s + t)) *
        (fun w : ℂ ↦ mwkfEulerPoleUnitCore s t w)) 0 = _
  have hpoleDeriv : HasDerivAt
      (fun w : ℂ ↦ (s + w) * (t + w) / (s + t)) 1 0 := by
    have hraw := (((hasDerivAt_const (0 : ℂ) s).add (hasDerivAt_id 0)).mul
      ((hasDerivAt_const (0 : ℂ) t).add (hasDerivAt_id 0))).div_const
        (s + t)
    apply hraw.congr_deriv
    field_simp [hst]
    simp [add_comm]
  rw [deriv_mul hpole hcore.differentiableAt, hpoleDeriv.deriv]
  simp

end PrimeNumberTheorem.MWKFCubic
