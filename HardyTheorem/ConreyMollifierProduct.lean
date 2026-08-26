import HardyTheorem.ConreyDegreeOneV1
import HardyTheorem.SelbergMollifierNonvanishing

/-!
# Conrey's actual mollifier and the equation-(35) product inclusion

This file implements equations (1), (33), and the local analytic content of
equation (35) in Conrey's 1989 paper.  The polynomial side conditions on `P`
are irrelevant for the finite Dirichlet polynomial's analyticity, so `P` is
kept as a real function here; the normalization `P 1 = 1` is imposed exactly
where nontriviality of the mollifier is needed.
-/

open Complex Filter Set
open scoped BigOperators

namespace HardyTheorem

/-- Conrey's coefficient
`mu(n) P(log (Y/n) / log Y) n^(sigma0-1/2)` from equations (1) and (33). -/
noncomputable def conreyMollifierCoefficient
    (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) *
    (P (Real.log ((Y : ℝ) / (n : ℝ)) / Real.log Y) : ℂ) *
    (n : ℂ) ^ ((sigma0 - 1 / 2 : ℝ) : ℂ)

/-- The finite mollifier `B(s,P)` in Conrey's equation (33). -/
noncomputable def conreyMollifier
    (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ) (s : ℂ) : ℂ :=
  selbergMollifier Y (conreyMollifierCoefficient Y sigma0 P) s

/-- The normalization `P(1)=1` makes the constant Dirichlet coefficient
exactly one when the cutoff is genuine. -/
theorem conreyMollifierCoefficient_one
    {Y : ℕ} {P : ℝ → ℝ} (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (sigma0 : ℝ) :
    conreyMollifierCoefficient Y sigma0 P 1 = 1 := by
  have hYreal : (1 : ℝ) < Y := by exact_mod_cast hY
  have hlogY : Real.log (Y : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hYreal)
  simp [conreyMollifierCoefficient, hlogY, hP1]

/-- Expansion of the definition in exactly the form printed in equation
(33): `B(s,P) = sum b(n,P) n^(sigma0-1/2) / n^s`. -/
theorem conreyMollifier_eq_conrey_formula
    (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ) (s : ℂ) :
    conreyMollifier Y sigma0 P s =
      ∑ n ∈ Finset.Icc 1 Y,
        (ArithmeticFunction.moebius n : ℂ) *
          (P (Real.log ((Y : ℝ) / (n : ℝ)) / Real.log Y) : ℂ) *
          (n : ℂ) ^ ((sigma0 - 1 / 2 : ℝ) : ℂ) /
          (n : ℂ) ^ s := by
  unfold conreyMollifier selbergMollifier conreyMollifierCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Conrey's finite mollifier is entire. -/
theorem analyticOnNhd_conreyMollifier
    (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ) :
    AnalyticOnNhd ℂ (conreyMollifier Y sigma0 P) Set.univ := by
  exact analyticOnNhd_selbergMollifier Y
    (conreyMollifierCoefficient Y sigma0 P)

/-- A normalized Conrey mollifier tends to one on the positive real axis. -/
theorem tendsto_conreyMollifier_real_atTop
    {Y : ℕ} {P : ℝ → ℝ} (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (sigma0 : ℝ) :
    Tendsto (fun sigma : ℝ =>
      conreyMollifier Y sigma0 P (sigma : ℂ)) atTop (nhds 1) := by
  exact tendsto_selbergMollifier_real_atTop Y
    (conreyMollifierCoefficient Y sigma0 P) (by omega)
      (conreyMollifierCoefficient_one hY hP1 sigma0)

/-- A normalized Conrey mollifier is not locally the zero function, so its
analytic order is finite at every point. -/
theorem analyticOrderAt_conreyMollifier_ne_top
    {Y : ℕ} {P : ℝ → ℝ} (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (sigma0 : ℝ) (s : ℂ) :
    analyticOrderAt (conreyMollifier Y sigma0 P) s ≠ ⊤ := by
  have hYone : 1 ≤ Y := hY.trans' (by omega)
  have hcoeff : conreyMollifierCoefficient Y sigma0 P 1 = 1 :=
    conreyMollifierCoefficient_one hY hP1 sigma0
  obtain ⟨z, hz⟩ := exists_selbergMollifier_ne_zero Y
    (conreyMollifierCoefficient Y sigma0 P) hYone hcoeff
  have hzorder :
      analyticOrderAt (conreyMollifier Y sigma0 P) z ≠ ⊤ := by
    rw [(analyticOnNhd_conreyMollifier Y sigma0 P z (by simp)).analyticOrderAt_eq_zero.mpr hz]
    exact ENat.natCast_ne_top 0
  exact (analyticOnNhd_conreyMollifier Y sigma0 P).analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (by simp) (by simp) hzorder

/-- The actual product `V1(s) B(s,P)` whose zeros occur in equations
(35)--(40). -/
noncomputable def conreyMollifiedDegreeOneV1
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (s : ℂ) : ℂ :=
  conreyDegreeOneV1 g g0 g1 L s * conreyMollifier Y sigma0 P s

theorem conreyMollifiedDegreeOneV1_eq
    (g g0 g1 L : ℝ) (Y : ℕ) (sigma0 : ℝ) (P : ℝ → ℝ)
    (s : ℂ) :
    conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s =
      conreyDegreeOneV1 g g0 g1 L s * conreyMollifier Y sigma0 P s := by
  rfl

/-- Every zero of `V1` remains a zero after multiplication by Conrey's
mollifier. -/
theorem conreyMollifiedDegreeOneV1_eq_zero_of_v1_eq_zero
    {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ} {s : ℂ}
    (hzero : conreyDegreeOneV1 g g0 g1 L s = 0) :
    conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P s = 0 := by
  simp [conreyMollifiedDegreeOneV1, hzero]

/-- Pointwise multiplicity form of Conrey's equation-(35) inclusion.  The
finite-order hypothesis on `V1` is stated explicitly; the normalized finite
mollifier has finite order unconditionally. -/
theorem analyticOrderNatAt_conreyDegreeOneV1_le_mollified
    {g g0 g1 L sigma0 : ℝ} {Y : ℕ} {P : ℝ → ℝ} {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1)
    (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hVfinite : analyticOrderAt (conreyDegreeOneV1 g g0 g1 L) s ≠ ⊤) :
    analyticOrderNatAt (conreyDegreeOneV1 g g0 g1 L) s ≤
      analyticOrderNatAt
        (conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P) s := by
  have hV := analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
    (g := g) (g0 := g0) (g1 := g1) (L := L) hs0 hs1
  have hB := analyticOnNhd_conreyMollifier Y sigma0 P s (by simp)
  have hBfinite := analyticOrderAt_conreyMollifier_ne_top hY hP1 sigma0 s
  unfold conreyMollifiedDegreeOneV1
  change analyticOrderNatAt (conreyDegreeOneV1 g g0 g1 L) s ≤
    analyticOrderNatAt
      (conreyDegreeOneV1 g g0 g1 L * conreyMollifier Y sigma0 P) s
  rw [analyticOrderNatAt_mul hV hB hVfinite hBfinite]
  exact Nat.le_add_right _ _

end HardyTheorem
