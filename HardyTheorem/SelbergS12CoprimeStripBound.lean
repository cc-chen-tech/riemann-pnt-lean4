import HardyTheorem.SelbergS12CoprimeDirichlet
import HardyTheorem.SelbergS12StripZetaInverse
import HardyTheorem.SelbergS13AbsoluteBound

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Selberg S12: the coprime square-root series on the one-strip

The reciprocal zeta estimate on `1 + epsilon + it` is combined with the
finite Euler factors deleted by the coprimality condition.  The local reverse
triangle inequality is the only estimate needed for those factors.
-/

/-- On the closed one-strip, deleting one prime Euler factor costs at most
`(1 - 1 / p)⁻¹`. -/
theorem norm_inv_one_sub_prime_cpow_le {p : ℕ} (hp : p.Prime)
    {epsilon t : ℝ} (hepsilon : 0 ≤ epsilon) :
    ‖(1 - (p : ℂ) ^ (-selbergS12StripPoint epsilon t))⁻¹‖ ≤
      (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow :
      ‖(p : ℂ) ^ (-selbergS12StripPoint epsilon t)‖ ≤ (p : ℝ)⁻¹ := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, neg_re,
      ← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le hp1.le
    simp [selbergS12StripPoint]
    linarith
  have hbase : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
  have hden :
      1 - (p : ℝ)⁻¹ ≤ ‖1 - (p : ℂ) ^ (-selbergS12StripPoint epsilon t)‖ := by
    calc
      1 - (p : ℝ)⁻¹ ≤
          ‖(1 : ℂ)‖ - ‖(p : ℂ) ^ (-selbergS12StripPoint epsilon t)‖ := by
        simpa using sub_le_sub_left hpow 1
      _ ≤ ‖(1 : ℂ) - (p : ℂ) ^ (-selbergS12StripPoint epsilon t)‖ :=
        norm_sub_norm_le _ _
  have hdenpos :
      0 < ‖(1 : ℂ) - (p : ℂ) ^ (-selbergS12StripPoint epsilon t)‖ :=
    hbase.trans_le hden
  rw [norm_inv]
  exact (inv_le_inv₀ hdenpos hbase).2 hden

/-- The norm of all deleted Euler factors is controlled by Selberg's finite
`(1 + 1 / p)` product, with the absolute factor `2` from S13. -/
theorem norm_selbergS12CoprimeEulerFactors_inv_le (r : ℕ)
    {epsilon t : ℝ} (hepsilon : 0 ≤ epsilon) :
    ‖(∏ p ∈ r.primeFactors,
        (1 - (p : ℂ) ^ (-selbergS12StripPoint epsilon t)))⁻¹‖ ≤
      2 * ∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹) := by
  calc
    ‖(∏ p ∈ r.primeFactors,
        (1 - (p : ℂ) ^ (-selbergS12StripPoint epsilon t)))⁻¹‖ =
        ‖∏ p ∈ r.primeFactors,
          (1 - (p : ℂ) ^ (-selbergS12StripPoint epsilon t))⁻¹‖ := by
      rw [Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ r.primeFactors,
        ‖(1 - (p : ℂ) ^ (-selbergS12StripPoint epsilon t))⁻¹‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
      exact Finset.prod_le_prod
        (fun _ _ => norm_nonneg _)
        (fun p hp => norm_inv_one_sub_prime_cpow_le
          (Nat.prime_of_mem_primeFactors hp) hepsilon)
    _ ≤ 2 * ∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹) :=
      selbergS13MinusEulerProduct_le_two_mul_plus r

/-- Uniform square-root bound for the coprime Dirichlet series throughout the
absolute-convergence strip used by Perron's formula. -/
theorem exists_norm_selbergS12CoprimeDirichletSeries_strip_le :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (r : ℕ) [NeZero r] (epsilon t : ℝ),
        0 < epsilon → epsilon ≤ 1 →
        ‖selbergS12CoprimeDirichletSeries r
            (selbergS12StripPoint epsilon t)‖ ≤
          B * Real.sqrt (epsilon + |t|) *
            Real.sqrt (∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)) := by
  rcases exists_norm_inv_riemannZeta_strip_le_mul_offset with
    ⟨A, hA, hZeta⟩
  let B : ℝ := Real.sqrt (2 * A)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  refine ⟨B, hB, ?_⟩
  intro r _ epsilon t hepsilon hepsilon1
  let P : ℝ := ∏ p ∈ r.primeFactors, (1 + (p : ℝ)⁻¹)
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hs : 1 < (selbergS12StripPoint epsilon t).re := by
    simp [selbergS12StripPoint]
    linarith
  have hsqIdentity :=
    selbergS12CoprimeDirichletSeries_sq_eq_explicit (r := r) hs
  have hEuler := norm_selbergS12CoprimeEulerFactors_inv_le r
    (t := t) hepsilon.le
  have hsq :
      ‖selbergS12CoprimeDirichletSeries r
          (selbergS12StripPoint epsilon t)‖ ^ 2 ≤
        (2 * A) * (epsilon + |t|) * P := by
    calc
      ‖selbergS12CoprimeDirichletSeries r
          (selbergS12StripPoint epsilon t)‖ ^ 2 =
          ‖(selbergS12CoprimeDirichletSeries r
            (selbergS12StripPoint epsilon t)) ^ 2‖ := by rw [norm_pow]
      _ = ‖(riemannZeta (selbergS12StripPoint epsilon t) *
            ∏ p ∈ r.primeFactors,
              (1 - (p : ℂ) ^ (-selbergS12StripPoint epsilon t)))⁻¹‖ := by
        rw [hsqIdentity]
      _ = ‖(riemannZeta (selbergS12StripPoint epsilon t))⁻¹‖ *
            ‖(∏ p ∈ r.primeFactors,
              (1 - (p : ℂ) ^ (-selbergS12StripPoint epsilon t)))⁻¹‖ := by
        rw [mul_inv_rev, norm_mul, mul_comm]
      _ ≤ (A * (epsilon + |t|)) * (2 * P) :=
        mul_le_mul (hZeta epsilon t hepsilon hepsilon1) hEuler
          (norm_nonneg _) (by positivity)
      _ = (2 * A) * (epsilon + |t|) * P := by ring
  calc
    ‖selbergS12CoprimeDirichletSeries r
        (selbergS12StripPoint epsilon t)‖ =
        Real.sqrt (‖selbergS12CoprimeDirichletSeries r
          (selbergS12StripPoint epsilon t)‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt ((2 * A) * (epsilon + |t|) * P) :=
      Real.sqrt_le_sqrt hsq
    _ = B * Real.sqrt (epsilon + |t|) * Real.sqrt P := by
      rw [Real.sqrt_mul (mul_nonneg (by positivity) (by positivity)),
        Real.sqrt_mul (by positivity)]

end HardyTheorem
