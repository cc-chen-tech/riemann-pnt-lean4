import HardyTheorem.SelbergS12DirichletBranch
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

open Complex
open ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius LSeries.notation BigOperators

namespace HardyTheorem

/-!
# Selberg S12: deleting the Euler factors dividing `r`

The principal character modulo `r` is the exact coprimality indicator.  Twisting Selberg's
square-root coefficients by this character deletes precisely the terms with `(n,r) > 1`.
Since character twists commute with Dirichlet convolution, the square of the resulting
Dirichlet series is the inverse principal-character L-series.  The standard change-of-level
formula then supplies the finite Euler factors dividing `r`.
-/

noncomputable def selbergPrincipalCharacter (r : ℕ) : DirichletCharacter ℂ r :=
  1

noncomputable def selbergS12CoprimeCoeff (r : ℕ) (n : ℕ) : ℂ :=
  selbergPrincipalCharacter r n * selbergSqrtZetaCoeffComplex n

theorem selbergS12CoprimeCoeff_of_coprime {r n : ℕ} (h : n.Coprime r) :
    selbergS12CoprimeCoeff r n = selbergSqrtZetaCoeffComplex n := by
  unfold selbergS12CoprimeCoeff selbergPrincipalCharacter
  rw [MulChar.one_apply]
  · simp
  · exact (ZMod.isUnit_iff_coprime n r).2 h

theorem selbergS12CoprimeCoeff_of_not_coprime {r n : ℕ} (h : ¬n.Coprime r) :
    selbergS12CoprimeCoeff r n = 0 := by
  unfold selbergS12CoprimeCoeff selbergPrincipalCharacter
  rw [MulChar.map_nonunit]
  · simp
  · exact fun hu => h ((ZMod.isUnit_iff_coprime n r).1 hu)

theorem LSeriesSummable_selbergS12CoprimeCoeff {r : ℕ} {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (selbergS12CoprimeCoeff r) s := by
  exact DirichletCharacter.LSeriesSummable_mul (selbergPrincipalCharacter r)
    (LSeriesSummable_selbergSqrtZetaCoeffComplex hs)

noncomputable def selbergS12CoprimeDirichletSeries (r : ℕ) (s : ℂ) : ℂ :=
  L (selbergS12CoprimeCoeff r) s

private theorem selbergSqrtZetaCoeffComplex_convolution_self :
    (↗selbergSqrtZetaCoeffComplex : ℕ → ℂ) ⍟
        (↗selbergSqrtZetaCoeffComplex : ℕ → ℂ) =
      (↗(ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ℕ → ℂ) := by
  rw [ArithmeticFunction.coe_mul]
  funext n
  exact congrArg (fun F : ArithmeticFunction ℂ => F n)
    selbergSqrtZetaCoeffComplex_mul_self

private theorem selbergS12CoprimeCoeff_convolution_self (r : ℕ) :
    selbergS12CoprimeCoeff r ⍟ selbergS12CoprimeCoeff r =
      (↗(selbergPrincipalCharacter r) : ℕ → ℂ) *
        (↗(ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ℕ → ℂ) := by
  calc
    selbergS12CoprimeCoeff r ⍟ selbergS12CoprimeCoeff r =
        (↗(selbergPrincipalCharacter r) : ℕ → ℂ) *
          ((↗selbergSqrtZetaCoeffComplex : ℕ → ℂ) ⍟
            (↗selbergSqrtZetaCoeffComplex : ℕ → ℂ)) := by
      exact DirichletCharacter.mul_convolution_distrib
        (selbergPrincipalCharacter r)
        (↗selbergSqrtZetaCoeffComplex : ℕ → ℂ)
        (↗selbergSqrtZetaCoeffComplex : ℕ → ℂ)
    _ = (↗(selbergPrincipalCharacter r) : ℕ → ℂ) *
        (↗(ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ℕ → ℂ) := by
      rw [selbergSqrtZetaCoeffComplex_convolution_self]

theorem selbergS12CoprimeDirichletSeries_sq_eq_inv_principalLSeries
    {r : ℕ} {s : ℂ} (hs : 1 < s.re) :
    selbergS12CoprimeDirichletSeries r s ^ 2 =
      (L (↗(selbergPrincipalCharacter r) : ℕ → ℂ) s)⁻¹ := by
  have hsum : LSeriesSummable (selbergS12CoprimeCoeff r) s :=
    LSeriesSummable_selbergS12CoprimeCoeff hs
  have hmul := LSeries_convolution' hsum hsum
  have hprincipal := DirichletCharacter.LSeries.mul_mu_eq_one
    (selbergPrincipalCharacter r) hs
  have hprincipal0 := DirichletCharacter.LSeries_ne_zero_of_one_lt_re
    (selbergPrincipalCharacter r) hs
  have hinv :
      L ((↗(selbergPrincipalCharacter r) : ℕ → ℂ) *
          (↗(ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ℕ → ℂ)) s =
        (L (↗(selbergPrincipalCharacter r) : ℕ → ℂ) s)⁻¹ :=
    (mul_eq_one_iff_eq_inv₀ hprincipal0).mp
      (by simpa [mul_comm] using hprincipal)
  unfold selbergS12CoprimeDirichletSeries
  rw [pow_two, ← hmul, selbergS12CoprimeCoeff_convolution_self, hinv]

theorem selbergPrincipalLSeries_eq_zeta_mul_eulerFactors
    {r : ℕ} [NeZero r] {s : ℂ} (hs : 1 < s.re) :
    L (↗(selbergPrincipalCharacter r) : ℕ → ℂ) s =
      riemannZeta s *
        ∏ p ∈ r.primeFactors, (1 - (p : ℂ) ^ (-s)) := by
  have hchange := DirichletCharacter.LSeries_changeLevel
    (M := 1) (N := r) (one_dvd r) (1 : DirichletCharacter ℂ 1) hs
  rw [DirichletCharacter.changeLevel_one] at hchange
  have hone (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    exact MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1))
  rw [DirichletCharacter.modOne_eq_one, LSeries_one_eq_riemannZeta hs] at hchange
  simp_rw [hone, one_mul] at hchange
  simpa [selbergPrincipalCharacter] using hchange

theorem selbergS12CoprimeDirichletSeries_sq_eq_explicit
    {r : ℕ} [NeZero r] {s : ℂ} (hs : 1 < s.re) :
    selbergS12CoprimeDirichletSeries r s ^ 2 =
      (riemannZeta s *
        ∏ p ∈ r.primeFactors, (1 - (p : ℂ) ^ (-s)))⁻¹ := by
  rw [selbergS12CoprimeDirichletSeries_sq_eq_inv_principalLSeries hs,
    selbergPrincipalLSeries_eq_zeta_mul_eulerFactors hs]

end HardyTheorem
