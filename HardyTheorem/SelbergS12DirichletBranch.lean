import HardyTheorem.SelbergS12AnalyticBranch
import HardyTheorem.SelbergS12CoeffBound
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv

open Complex Set
open ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
  LSeries.notation

namespace HardyTheorem

/-!
# Selberg S12: the Dirichlet-series-normalized square-root branch

The bounded coefficients `alpha_n` have an absolutely convergent L-series for `re s > 1`.
Their Dirichlet-convolution square is Moebius, so the square of this L-series is exactly
`1 / riemannZeta s`.  This identifies the canonical branch needed by Perron's formula, including
its sign, rather than merely producing an unspecified analytic square root.
-/

noncomputable def selbergSqrtZetaCoeffComplex : ArithmeticFunction ℂ :=
  ⟨fun n => (selbergSqrtZetaCoeff n : ℂ), by simp⟩

@[simp] theorem selbergSqrtZetaCoeffComplex_apply (n : ℕ) :
    selbergSqrtZetaCoeffComplex n = (selbergSqrtZetaCoeff n : ℂ) := rfl

theorem norm_selbergSqrtZetaCoeffComplex_le_one (n : ℕ) :
    ‖selbergSqrtZetaCoeffComplex n‖ ≤ 1 := by
  simpa [selbergSqrtZetaCoeffComplex] using
    abs_selbergSqrtZetaCoeff_le_one_light n

theorem selbergSqrtZetaCoeffComplex_mul_self :
    selbergSqrtZetaCoeffComplex * selbergSqrtZetaCoeffComplex =
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) := by
  apply ArithmeticFunction.ext
  intro n
  have hreal :
      (selbergSqrtZetaCoeff * selbergSqrtZetaCoeff) n =
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) n :=
    congrArg (fun F : ArithmeticFunction ℝ => F n)
      selbergSqrtZetaCoeff_mul_self
  have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal
  change (∑ x ∈ n.divisorsAntidiagonal,
      (selbergSqrtZetaCoeff x.1 : ℂ) *
        (selbergSqrtZetaCoeff x.2 : ℂ)) =
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ) n
  simpa using hcast

theorem LSeriesSummable_selbergSqrtZetaCoeffComplex {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable ↗selbergSqrtZetaCoeffComplex s := by
  exact LSeriesSummable_of_bounded_of_one_lt_re
    (m := 1) (fun n _ => norm_selbergSqrtZetaCoeffComplex_le_one n) hs

noncomputable def selbergS12DirichletSquareRoot (s : ℂ) : ℂ :=
  L ↗selbergSqrtZetaCoeffComplex s

theorem analyticOnNhd_selbergS12DirichletSquareRoot :
    AnalyticOnNhd ℂ selbergS12DirichletSquareRoot {s : ℂ | 1 < s.re} := by
  have habs :
      LSeries.abscissaOfAbsConv (↗selbergSqrtZetaCoeffComplex : ℕ → ℂ) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const
      ⟨1, fun n _ => norm_selbergSqrtZetaCoeffComplex_le_one n⟩
  intro s hs
  unfold selbergS12DirichletSquareRoot
  exact (LSeries_analyticOnNhd (↗selbergSqrtZetaCoeffComplex : ℕ → ℂ)) s
    (habs.trans_lt (by exact_mod_cast hs))

theorem selbergS12DirichletSquareRoot_sq_eq_inv_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    selbergS12DirichletSquareRoot s ^ 2 = (riemannZeta s)⁻¹ := by
  have hsum : LSeriesSummable ↗selbergSqrtZetaCoeffComplex s :=
    LSeriesSummable_selbergSqrtZetaCoeffComplex hs
  have hmul :
      L ↗(selbergSqrtZetaCoeffComplex * selbergSqrtZetaCoeffComplex) s =
        L ↗selbergSqrtZetaCoeffComplex s *
          L ↗selbergSqrtZetaCoeffComplex s :=
    ArithmeticFunction.LSeries_mul' hsum hsum
  have hzetaMu := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hzetaMu
  have hmu : L ↗(ArithmeticFunction.moebius : ArithmeticFunction ℂ) s =
      (riemannZeta s)⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ (riemannZeta_ne_zero_of_one_lt_re hs)).mp
      (by simpa [mul_comm] using hzetaMu)
  unfold selbergS12DirichletSquareRoot
  rw [pow_two, ← hmul, selbergSqrtZetaCoeffComplex_mul_self, hmu]

noncomputable def selbergS12ShiftedDirichletSquareRoot
    (theta : ℝ) (s : ℂ) : ℂ :=
  selbergS12DirichletSquareRoot (((1 - theta : ℝ) : ℂ) + s)

theorem analyticOnNhd_selbergS12ShiftedDirichletSquareRoot (theta : ℝ) :
    AnalyticOnNhd ℂ (selbergS12ShiftedDirichletSquareRoot theta)
      (selbergS12RightHalfPlane theta) := by
  intro s hs
  have hwre : 1 < ((((1 - theta : ℝ) : ℂ) + s).re) :=
    selbergS12_shifted_re_gt_one hs
  have hroot : AnalyticAt ℂ selbergS12DirichletSquareRoot
      (((1 - theta : ℝ) : ℂ) + s) :=
    analyticOnNhd_selbergS12DirichletSquareRoot _ hwre
  have haffine : AnalyticAt ℂ (fun z : ℂ => ((1 - theta : ℝ) : ℂ) + z) s :=
    analyticAt_const.add analyticAt_id
  unfold selbergS12ShiftedDirichletSquareRoot
  exact AnalyticAt.comp
    (g := selbergS12DirichletSquareRoot)
    (f := fun z : ℂ => ((1 - theta : ℝ) : ℂ) + z)
    (x := s) hroot haffine

theorem selbergS12ShiftedDirichletSquareRoot_sq_eq (theta : ℝ)
    {s : ℂ} (hs : s ∈ selbergS12RightHalfPlane theta) :
    selbergS12ShiftedDirichletSquareRoot theta s ^ 2 =
      selbergS12ZetaReciprocal theta s := by
  unfold selbergS12ShiftedDirichletSquareRoot selbergS12ZetaReciprocal
  exact selbergS12DirichletSquareRoot_sq_eq_inv_riemannZeta
    (selbergS12_shifted_re_gt_one hs)

end HardyTheorem
