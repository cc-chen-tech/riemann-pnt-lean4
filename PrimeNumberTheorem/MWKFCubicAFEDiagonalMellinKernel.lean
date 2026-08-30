import PrimeNumberTheorem.MWKFCubicAFEDiagonalSplit

open Complex

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Exact reciprocal-LCM normalization of the diagonal Mellin kernel

No zero-mode evaluation or asymptotic input is used. The positive diagonal
scale gives zeta(1+2z), with the exact reciprocal-LCM coefficient.
-/

theorem cubicAFEDiagonal_sqrt_normalization {d e : ℕ} (hd : 0 < d) (_he : 0 < e) :
    Real.sqrt (((d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℝ) *
      Real.sqrt ((d : ℝ) * e) = (Nat.lcm d e : ℝ) := by
  let q := Nat.gcd d e
  let r := d / q
  let s := e / q
  have hq : 0 < q := Nat.gcd_pos_of_pos_left e hd
  obtain ⟨hdq, heq, _⟩ := gcd_extraction hq.ne'
  have hlcm : Nat.lcm d e = q * (r * s) := by
    apply Nat.mul_left_cancel hq
    change Nat.gcd d e * Nat.lcm d e = q * (q * (r * s))
    rw [Nat.gcd_mul_lcm]
    calc
      d * e = (q * r) * (q * s) := congrArg₂ (· * ·) hdq heq
      _ = _ := by ring
  have hde : (d : ℝ) * e = (q : ℝ)^2 * ((r * s : ℕ) : ℝ) := by
    have hd' : (d : ℝ) = (q : ℝ) * r := by exact_mod_cast hdq
    have he' : (e : ℝ) = (q : ℝ) * s := by exact_mod_cast heq
    rw [hd', he', Nat.cast_mul]
    ring
  change Real.sqrt ((r * s : ℕ) : ℝ) * Real.sqrt ((d : ℝ) * e) = _
  rw [hde, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg q), hlcm]
  simp only [Nat.cast_mul]
  calc
    _ = (q : ℝ) * (Real.sqrt ((r : ℝ) * s))^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]

private theorem sqrt_square_mul_nat (l Q : ℕ) :
    Real.sqrt ((l^2 * Q : ℕ) : ℝ) = (l : ℝ) * Real.sqrt (Q : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg l)]

private theorem square_mul_nat_cpow (l Q : ℕ) (z : ℂ) :
    ((l^2 * Q : ℕ) : ℂ) ^ z = (l : ℂ) ^ (2 * z) * (Q : ℂ) ^ z := by
  have hk : l^2 * Q = (l * l) * Q := by ring
  rw [hk, Nat.cast_mul, natCast_mul_natCast_cpow, Nat.cast_mul, natCast_mul_natCast_cpow]
  rw [show (2 : ℂ) * z = (2 : ℕ) * z by norm_num, Complex.cpow_nat_mul]
  ring

noncomputable def cubicAFEDiagonalMellinMonomial (d e k : ℕ) (z : ℂ) : ℂ :=
  ((Real.sqrt (((k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℝ) : ℂ)⁻¹ *
    (Real.sqrt ((d : ℝ) * e) : ℂ)⁻¹) *
      (1 / (((k + 1)^2 * (d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℂ) ^ z)

theorem cubicAFEDiagonalMellinMonomial_eq {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (k : ℕ) (z : ℂ) :
    cubicAFEDiagonalMellinMonomial d e k z =
      (1 / (Nat.lcm d e : ℂ)) *
        (1 / (((d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℂ)^z) *
          (1 / (k + 1 : ℂ) ^ (1 + 2 * z)) := by
  let Q := (d / Nat.gcd d e) * (e / Nat.gcd d e)
  have hnorm : (Real.sqrt (Q : ℝ) : ℂ) * (Real.sqrt ((d : ℝ) * e) : ℂ) =
      (Nat.lcm d e : ℂ) := by
    exact_mod_cast cubicAFEDiagonal_sqrt_normalization hd he
  have hl : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  unfold cubicAFEDiagonalMellinMonomial
  rw [Nat.mul_assoc, sqrt_square_mul_nat, Complex.ofReal_mul, square_mul_nat_cpow]
  rw [Complex.cpow_add _ _ hl, Complex.cpow_one]
  simp only [one_div, mul_inv_rev]
  rw [← hnorm]
  dsimp [Q] at *
  push_cast
  simp only [mul_inv_rev]
  ring

theorem hasSum_cubicAFEDiagonalMellinMonomial {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun k : ℕ ↦ cubicAFEDiagonalMellinMonomial d e k z)
      ((1 / (Nat.lcm d e : ℂ)) *
        (1 / (((d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℂ)^z) * riemannZeta (1 + 2 * z)) := by
  have hs : 1 < (1 + 2 * z).re := by simp; linarith
  have hsum : HasSum (fun k : ℕ ↦ 1 / (k + 1 : ℂ) ^ (1 + 2 * z)) (riemannZeta (1 + 2 * z)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    apply Summable.hasSum
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.mpr hs)
  apply (hsum.mul_left ((1 / (Nat.lcm d e : ℂ)) *
    (1 / (((d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℂ)^z))).congr_fun
  intro k
  exact cubicAFEDiagonalMellinMonomial_eq hd he k z

end PrimeNumberTheorem.MWKFCubic
