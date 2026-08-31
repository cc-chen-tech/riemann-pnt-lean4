import HardyTheorem.AFE
import HardyTheorem.SelbergMollifier
import HardyTheorem.TwoScaleSelbergMollifier

/-!
# A canonical critical-line AFE remainder

The corrected square-root AFE target in `HardyTheorem.AFE` is deliberately
only a proposition: it does not provide an analytic theorem.  Its remainder
is also existential at every height, which is inconvenient under an
integral.  This file makes no attempt to prove that target.  Instead it
defines the unique canonical remainder, proves the exact equivalent form of
the target, and records the product decomposition and elementary mollifier
bound needed by the Carlson critical-boundary argument.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- The two independently introduced names for the standard linear Selberg
mollifier are definitionally the same finite Dirichlet polynomial. -/
theorem linearLogSelbergMollifier_eq_selbergMoebiusMollifier
    (X : ℕ) (s : ℂ) :
    linearLogSelbergMollifier X s = selbergMoebiusMollifier X s := by
  rfl

/-- The elementary pointwise square-root bound for the standard linear
Selberg mollifier on the critical line. -/
theorem norm_selbergMoebiusMollifier_criticalLine_le_two_sqrt
    {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    ‖selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
      2 * Real.sqrt X := by
  unfold selbergMoebiusMollifier selbergMollifier
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        (selbergMoebiusCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ ≤
        ∑ n ∈ Finset.Icc 1 X,
          ‖(selbergMoebiusCoeff X n : ℂ) *
            (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (Real.sqrt n)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
      have hnpos : 0 < n := by omega
      have hcoeff : ‖(selbergMoebiusCoeff X n : ℂ)‖ ≤ 1 := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          abs_selbergMoebiusCoeff_le_one hX hn1 hnX
      have hpow :
          ‖(n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ = Real.sqrt n := by
        rw [Complex.norm_natCast_cpow_of_pos hnpos]
        simp [Real.sqrt_eq_rpow]
      rw [norm_mul, norm_div, norm_one, hpow, one_div]
      exact mul_le_of_le_one_left
        (inv_nonneg.mpr (Real.sqrt_nonneg n)) hcoeff
    _ ≤ 2 * Real.sqrt X := sum_inv_sqrt_Icc_one_le_two_sqrt X

namespace AFE

/-- The natural square-root cutoff in the corrected critical-line AFE. -/
noncomputable def criticalAfeCutoff (t : ℝ) : ℕ :=
  Nat.floor (Real.sqrt (t / (2 * Real.pi)))

/-- The first square-root Dirichlet polynomial in the critical-line AFE. -/
noncomputable def criticalAfeMainSum (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (criticalAfeCutoff t),
    1 / ((n + 1 : ℂ) ^ ((1 / 2 : ℂ) + I * t))

/-- The conjugate-exponent square-root polynomial in the critical-line AFE. -/
noncomputable def criticalAfeDualSum (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (criticalAfeCutoff t),
    1 / ((n + 1 : ℂ) ^ ((1 / 2 : ℂ) - I * t))

/-- The unique remainder obtained by subtracting the two corrected AFE main
terms from zeta.  Unlike the witness in `zeta_critical_afe_target`, this is a
genuine function of the height. -/
noncomputable def criticalAfeCanonicalRemainder (t : ℝ) : ℂ :=
  riemannZeta ((1 / 2 : ℂ) + I * t) -
    (criticalAfeMainSum t + criticalAfeDualPhase t * criticalAfeDualSum t)

/-- Tautological exact decomposition associated with the canonical
remainder. -/
theorem riemannZeta_critical_eq_afe_add_canonicalRemainder (t : ℝ) :
    riemannZeta ((1 / 2 : ℂ) + I * t) =
      criticalAfeMainSum t +
        criticalAfeDualPhase t * criticalAfeDualSum t +
          criticalAfeCanonicalRemainder t := by
  unfold criticalAfeCanonicalRemainder
  ring

/-- The existential AFE target is exactly a uniform bound for the canonical
remainder.  This is only a logical normalization; it does not prove the AFE. -/
theorem zeta_critical_afe_target_iff_canonical_remainder :
    zeta_critical_afe_target ↔
      ∃ R > (0 : ℝ), ∀ t : ℝ, t > 1 →
        ‖criticalAfeCanonicalRemainder t‖ ≤
          R * t ^ (-1 / 4 : ℝ) := by
  constructor
  · rintro ⟨R, hR, htarget⟩
    refine ⟨R, hR, ?_⟩
    intro t ht
    obtain ⟨R', hzeta, hR'⟩ := htarget t ht
    have hcanonical : criticalAfeCanonicalRemainder t = R' := by
      unfold criticalAfeCanonicalRemainder criticalAfeMainSum
        criticalAfeDualSum criticalAfeCutoff
      rw [hzeta]
      ring
    rwa [hcanonical]
  · rintro ⟨R, hR, hcanonical⟩
    refine ⟨R, hR, ?_⟩
    intro t ht
    refine ⟨criticalAfeCanonicalRemainder t, ?_, hcanonical t ht⟩
    simpa [criticalAfeMainSum, criticalAfeDualSum, criticalAfeCutoff] using
      riemannZeta_critical_eq_afe_add_canonicalRemainder t

/-- The corrected dual multiplier has unit norm. -/
@[simp] theorem norm_criticalAfeDualPhase (t : ℝ) :
    ‖criticalAfeDualPhase t‖ = 1 := by
  rw [criticalAfeDualPhase, Complex.norm_exp]
  have hre : (-2 * I * (unwrappedRiemannSiegelTheta t : ℂ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero]

/-- Exact product decomposition after multiplying the canonical AFE by the
standard linear Selberg mollifier. -/
theorem criticalAfe_product_decomposition (X : ℕ) (t : ℝ) :
    riemannZeta ((1 / 2 : ℂ) + I * t) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      criticalAfeMainSum t *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) +
        criticalAfeDualPhase t *
          (criticalAfeDualSum t *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) +
        criticalAfeCanonicalRemainder t *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) := by
  rw [riemannZeta_critical_eq_afe_add_canonicalRemainder]
  ring

/-- The canonical `O(t^{-1/4})` AFE remainder costs only the elementary
`2 sqrt X` pointwise norm when multiplied by the linear mollifier. -/
theorem norm_criticalAfeCanonicalRemainder_mul_selbergMoebiusMollifier_le
    {X : ℕ} (hX : 2 ≤ X) {R t : ℝ} (_hR : 0 ≤ R)
    (hrem : ‖criticalAfeCanonicalRemainder t‖ ≤
      R * t ^ (-1 / 4 : ℝ)) :
    ‖criticalAfeCanonicalRemainder t *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
      (R * t ^ (-1 / 4 : ℝ)) * (2 * Real.sqrt X) := by
  have hRhs : 0 ≤ R * t ^ (-1 / 4 : ℝ) :=
    (norm_nonneg (criticalAfeCanonicalRemainder t)).trans hrem
  rw [norm_mul]
  exact mul_le_mul hrem
    (norm_selbergMoebiusMollifier_criticalLine_le_two_sqrt hX t)
    (norm_nonneg _) hRhs

end AFE
end HardyTheorem
