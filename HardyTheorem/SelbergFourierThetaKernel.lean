import HardyTheorem.SelbergFourierMellinAlgebra
import HardyTheorem.SelbergSqrtZetaMollifier

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# The explicit theta kernel in Selberg's S1 transform

The definitions below are the exact right-hand side of the Fourier--Mellin
identity.  This file does not assert the contour shift equating it to the
completed-zeta function; that analytic equality is the remaining S1 gate.
-/

/-- Selberg's finite tapered `zeta^(-1/2)` Dirichlet polynomial. -/
noncomputable def selbergSqrtZetaPsi (X : ℕ) (s : ℂ) : ℂ :=
  selbergMollifier X
    (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ)) s

/-- The nonconstant triple-theta sum in equations (7.3) and (8.7), after
the positive integer `n`-sum has been packaged as a convergent theta sum. -/
noncomputable def selbergNonconstantThetaKernel
    (delta : ℝ) (X : ℕ) (y : ℝ) : ℂ :=
  ∑ μ ∈ Finset.Icc 1 X, ∑ ν ∈ Finset.Icc 1 X,
    ((selbergSqrtZetaTaperedCoeff X μ : ℂ) *
      (selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ)) *
      selbergGaussianThetaSum delta y μ ν

/-- The finite mollifier sum at one fixed positive theta index. -/
noncomputable def selbergNonconstantThetaLevel
    (delta : ℝ) (X : ℕ) (y : ℝ) (n : ℕ) : ℂ :=
  ∑ μ ∈ Finset.Icc 1 X, ∑ ν ∈ Finset.Icc 1 X,
    ((selbergSqrtZetaTaperedCoeff X μ : ℂ) *
      (selbergSqrtZetaTaperedCoeff X ν : ℂ) / (ν : ℂ)) *
      selbergGaussianThetaTerm delta y μ ν (n + 1)

/-- Absolute convergence survives the two finite mollifier sums, justifying
the finite-sum/positive-theta-sum interchange in S1. -/
theorem summable_selbergNonconstantThetaLevel
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) (y : ℝ) :
    Summable (selbergNonconstantThetaLevel delta X y) := by
  unfold selbergNonconstantThetaLevel
  apply summable_sum
  intro μ hμ
  apply summable_sum
  intro ν hν
  exact (summable_selbergGaussianThetaTerm_add_one
    hdelta0 hdeltaPi
      (Finset.mem_Icc.mp hμ).1 (Finset.mem_Icc.mp hν).1 y).mul_left _

/-- Summing the fixed-index levels gives exactly the finite mollifier sum of
the convergent theta series. -/
theorem hasSum_selbergNonconstantThetaLevel
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) (y : ℝ) :
    HasSum (selbergNonconstantThetaLevel delta X y)
      (selbergNonconstantThetaKernel delta X y) := by
  have hs := summable_selbergNonconstantThetaLevel
    hdelta0 hdeltaPi X y
  rw [hs.hasSum_iff]
  unfold selbergNonconstantThetaLevel selbergNonconstantThetaKernel
  rw [Summable.tsum_finsetSum (fun μ hμ => by
    apply summable_sum
    intro ν hν
    exact (summable_selbergGaussianThetaTerm_add_one
      hdelta0 hdeltaPi
        (Finset.mem_Icc.mp hμ).1 (Finset.mem_Icc.mp hν).1 y).mul_left _)]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [Summable.tsum_finsetSum (fun ν hν =>
    (summable_selbergGaussianThetaTerm_add_one
      hdelta0 hdeltaPi
        (Finset.mem_Icc.mp hμ).1 (Finset.mem_Icc.mp hν).1 y).mul_left _)]
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Summable.tsum_mul_left _
    (summable_selbergGaussianThetaTerm_add_one
      hdelta0 hdeltaPi
        (Finset.mem_Icc.mp hμ).1 (Finset.mem_Icc.mp hν).1 y)]
  rfl

/-- The explicit inverse unitary Fourier kernel: the first term is exactly
the residue at `s = 1`, and the second is the nonconstant Gaussian series. -/
noncomputable def selbergExplicitInverseFourierKernel
    (delta : ℝ) (X : ℕ) (y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * selbergFourierZ delta y ^ (1 / 2 : ℂ) *
      selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0 -
    selbergFourierZ delta y ^ (-1 / 2 : ℂ) *
      selbergNonconstantThetaKernel delta X y

end HardyTheorem
