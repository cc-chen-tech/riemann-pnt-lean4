import HardyTheorem.SelbergAnalyticSquareRoot
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Complex Set

namespace HardyTheorem

/-!
# Selberg S12: the analytic square-root branch to the right of the branch point

For the Perron variable `s`, the only branch point is the boundary point `s = theta`.
On the convex right half-plane `re s > theta`, the shifted zeta argument has real part
strictly greater than one.  Hence its reciprocal is analytic and nonzero there, and it admits an
analytic square root on the entire half-plane.
-/

def selbergS12RightHalfPlane (theta : ℝ) : Set ℂ :=
  {s : ℂ | theta < s.re}

theorem isOpen_selbergS12RightHalfPlane (theta : ℝ) :
    IsOpen (selbergS12RightHalfPlane theta) := by
  exact isOpen_lt continuous_const Complex.continuous_re

theorem convex_selbergS12RightHalfPlane (theta : ℝ) :
    Convex ℝ (selbergS12RightHalfPlane theta) := by
  exact convex_halfSpace_re_gt theta

theorem nonempty_selbergS12RightHalfPlane (theta : ℝ) :
    (selbergS12RightHalfPlane theta).Nonempty := by
  refine ⟨((theta + 1 : ℝ) : ℂ), ?_⟩
  simp [selbergS12RightHalfPlane]

theorem isSimplyConnected_selbergS12RightHalfPlane (theta : ℝ) :
    IsSimplyConnected (selbergS12RightHalfPlane theta) := by
  letI : ContractibleSpace (selbergS12RightHalfPlane theta) :=
    (convex_selbergS12RightHalfPlane theta).contractibleSpace
      (nonempty_selbergS12RightHalfPlane theta)
  exact (inferInstance : SimplyConnectedSpace (selbergS12RightHalfPlane theta))

noncomputable def selbergS12ZetaReciprocal (theta : ℝ) (s : ℂ) : ℂ :=
  (riemannZeta (((1 - theta : ℝ) : ℂ) + s))⁻¹

theorem selbergS12_shifted_re_gt_one {theta : ℝ} {s : ℂ}
    (hs : s ∈ selbergS12RightHalfPlane theta) :
    1 < ((((1 - theta : ℝ) : ℂ) + s).re) := by
  change theta < s.re at hs
  norm_num
  linarith

theorem analyticOnNhd_selbergS12ZetaReciprocal (theta : ℝ) :
    AnalyticOnNhd ℂ (selbergS12ZetaReciprocal theta)
      (selbergS12RightHalfPlane theta) := by
  intro s hs
  let w : ℂ := ((1 - theta : ℝ) : ℂ) + s
  have hwre : 1 < w.re := selbergS12_shifted_re_gt_one hs
  have hw1 : w ≠ 1 := by
    intro h
    rw [h] at hwre
    norm_num at hwre
  have hzeta : AnalyticAt ℂ riemannZeta w :=
    analyticOn_riemannZeta w (by simpa using hw1)
  have haffine : AnalyticAt ℂ (fun z : ℂ => ((1 - theta : ℝ) : ℂ) + z) s :=
    analyticAt_const.add analyticAt_id
  have hcomp : AnalyticAt ℂ
      (fun z : ℂ => riemannZeta (((1 - theta : ℝ) : ℂ) + z)) s :=
    AnalyticAt.comp
      (g := riemannZeta)
      (f := fun z : ℂ => ((1 - theta : ℝ) : ℂ) + z)
      (x := s) hzeta haffine
  unfold selbergS12ZetaReciprocal
  exact hcomp.inv (riemannZeta_ne_zero_of_one_lt_re hwre)

theorem selbergS12ZetaReciprocal_ne_zero (theta : ℝ)
    {s : ℂ} (hs : s ∈ selbergS12RightHalfPlane theta) :
    selbergS12ZetaReciprocal theta s ≠ 0 := by
  exact inv_ne_zero (riemannZeta_ne_zero_of_one_lt_re
    (selbergS12_shifted_re_gt_one hs))

theorem exists_selbergS12AnalyticSquareRoot (theta : ℝ) :
    ∃ R : ℂ → ℂ,
      AnalyticOnNhd ℂ R (selbergS12RightHalfPlane theta) ∧
      ∀ s : ℂ, R s ^ 2 = selbergS12ZetaReciprocal theta s := by
  exact exists_analyticOnNhd_sq_eq
    (isSimplyConnected_selbergS12RightHalfPlane theta)
    (isOpen_selbergS12RightHalfPlane theta)
    (analyticOnNhd_selbergS12ZetaReciprocal theta)
    (fun s hs => selbergS12ZetaReciprocal_ne_zero theta hs)

end HardyTheorem
