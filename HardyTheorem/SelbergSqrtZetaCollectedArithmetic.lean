import HardyTheorem.ArithmeticLogLeibniz
import HardyTheorem.SelbergSqrtZetaMollifier

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Global arithmetic of the square-root zeta mollifier

This file lifts the local prime-power calculation to Dirichlet-convolution
identities.  Its purpose is to identify the complete low-range coefficients
of Selberg's mollified Dirichlet polynomial.
-/

/-- The square-root zeta coefficient multiplied pointwise by `log n`. -/
noncomputable def selbergSqrtZetaLogCoeff :
    ArithmeticFunction ℝ :=
  selbergSqrtZetaCoeff.pmul ArithmeticFunction.log

/-- The real Möbius function multiplied pointwise by `log n`. -/
noncomputable def selbergMoebiusLogCoeff :
    ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius :
    ArithmeticFunction ℝ).pmul ArithmeticFunction.log

/-- Differentiating `a * a = μ` gives `2 a * (a log) = μ log`. -/
theorem two_mul_selbergSqrtZeta_mul_logCoeff :
    (2 : ArithmeticFunction ℝ) *
        (selbergSqrtZetaCoeff *
          selbergSqrtZetaLogCoeff) =
      selbergMoebiusLogCoeff := by
  have h := arithmeticFunction_pmul_log_mul
    selbergSqrtZetaCoeff selbergSqrtZetaCoeff
  rw [selbergSqrtZetaCoeff_mul_self] at h
  change selbergMoebiusLogCoeff =
      selbergSqrtZetaLogCoeff *
          selbergSqrtZetaCoeff +
        selbergSqrtZetaCoeff *
          selbergSqrtZetaLogCoeff at h
  rw [mul_comm selbergSqrtZetaLogCoeff
    selbergSqrtZetaCoeff] at h
  rw [h]
  ring

/-- Möbius-log convolution with zeta is `-Λ`. -/
theorem selbergMoebiusLogCoeff_mul_zeta :
    selbergMoebiusLogCoeff *
        (ArithmeticFunction.zeta :
          ArithmeticFunction ℝ) =
      -ArithmeticFunction.vonMangoldt := by
  ext n
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  change
    (∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) *
        Real.log d) =
      -ArithmeticFunction.vonMangoldt n
  exact ArithmeticFunction.sum_moebius_mul_log_eq

/-- The untapered square-root coefficient square cancels zeta. -/
theorem selbergSqrtZetaCoeff_sq_mul_zeta :
    (selbergSqrtZetaCoeff *
        selbergSqrtZetaCoeff) *
      (ArithmeticFunction.zeta :
        ArithmeticFunction ℝ) = 1 := by
  rw [selbergSqrtZetaCoeff_mul_self]
  exact ArithmeticFunction.coe_moebius_mul_coe_zeta
    (R := ℝ)

/-- A denominator-free form of the second logarithmic coefficient identity. -/
theorem four_mul_selbergSqrtZetaLogCoeff_sq_mul_zeta :
    (4 : ArithmeticFunction ℝ) *
        ((selbergSqrtZetaLogCoeff *
            selbergSqrtZetaLogCoeff) *
          (ArithmeticFunction.zeta :
            ArithmeticFunction ℝ)) =
      ArithmeticFunction.vonMangoldt *
        ArithmeticFunction.vonMangoldt := by
  calc
    (4 : ArithmeticFunction ℝ) *
          ((selbergSqrtZetaLogCoeff *
              selbergSqrtZetaLogCoeff) *
            (ArithmeticFunction.zeta :
              ArithmeticFunction ℝ)) =
        ((selbergSqrtZetaCoeff *
            selbergSqrtZetaCoeff) *
          (ArithmeticFunction.zeta :
            ArithmeticFunction ℝ)) *
        ((4 : ArithmeticFunction ℝ) *
          ((selbergSqrtZetaLogCoeff *
              selbergSqrtZetaLogCoeff) *
            (ArithmeticFunction.zeta :
              ArithmeticFunction ℝ))) := by
      rw [selbergSqrtZetaCoeff_sq_mul_zeta,
        one_mul]
    _ = (((2 : ArithmeticFunction ℝ) *
            (selbergSqrtZetaCoeff *
              selbergSqrtZetaLogCoeff)) *
          (ArithmeticFunction.zeta :
            ArithmeticFunction ℝ)) *
        (((2 : ArithmeticFunction ℝ) *
            (selbergSqrtZetaCoeff *
              selbergSqrtZetaLogCoeff)) *
          (ArithmeticFunction.zeta :
            ArithmeticFunction ℝ)) := by ring
    _ = (selbergMoebiusLogCoeff *
          (ArithmeticFunction.zeta :
            ArithmeticFunction ℝ)) *
        (selbergMoebiusLogCoeff *
          (ArithmeticFunction.zeta :
            ArithmeticFunction ℝ)) := by
      rw [two_mul_selbergSqrtZeta_mul_logCoeff]
    _ = (-ArithmeticFunction.vonMangoldt) *
        (-ArithmeticFunction.vonMangoldt) := by
      rw [selbergMoebiusLogCoeff_mul_zeta]
    _ = ArithmeticFunction.vonMangoldt *
        ArithmeticFunction.vonMangoldt := by ring

/-- The unrestricted linearly tapered square-root zeta coefficient.  The
finite mollifier agrees with this arithmetic function throughout its complete
cutoff range. -/
noncomputable def selbergSqrtZetaFullTapered
    (X : ℕ) : ArithmeticFunction ℝ :=
  selbergSqrtZetaCoeff -
    (Real.log X)⁻¹ • selbergSqrtZetaLogCoeff

@[simp] theorem selbergSqrtZetaFullTapered_apply
    (X n : ℕ) :
    selbergSqrtZetaFullTapered X n =
      selbergSqrtZetaCoeff n *
        (1 - Real.log n / Real.log X) := by
  change selbergSqrtZetaCoeff n -
      (Real.log X)⁻¹ *
        (selbergSqrtZetaCoeff n * Real.log n) =
    selbergSqrtZetaCoeff n *
      (1 - Real.log n / Real.log X)
  rw [div_eq_mul_inv]
  ring

/-- The denominator-free tapered coefficient
`a(n) * (log X - log n)`. -/
noncomputable def selbergSqrtZetaScaledTapered
    (X : ℕ) : ArithmeticFunction ℝ :=
  Real.log X • selbergSqrtZetaCoeff -
    selbergSqrtZetaLogCoeff

@[simp] theorem selbergSqrtZetaScaledTapered_apply
    (X n : ℕ) :
    selbergSqrtZetaScaledTapered X n =
      selbergSqrtZetaCoeff n *
        (Real.log X - Real.log n) := by
  change Real.log X * selbergSqrtZetaCoeff n -
      selbergSqrtZetaCoeff n * Real.log n =
    selbergSqrtZetaCoeff n *
      (Real.log X - Real.log n)
  ring

/-- Denominator-free global coefficient identity for the scaled tapered
square-root mollifier. -/
theorem selbergSqrtZetaScaledTapered_collected
    (X : ℕ) :
    (4 : ArithmeticFunction ℝ) *
        (((selbergSqrtZetaScaledTapered X *
            selbergSqrtZetaScaledTapered X) *
          (ArithmeticFunction.zeta :
            ArithmeticFunction ℝ))) =
      (4 * Real.log X ^ 2) •
          (1 : ArithmeticFunction ℝ) +
        (4 * Real.log X) •
          ArithmeticFunction.vonMangoldt +
        ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt := by
  rw [selbergSqrtZetaScaledTapered]
  calc
    (4 : ArithmeticFunction ℝ) *
          (((Real.log X • selbergSqrtZetaCoeff -
              selbergSqrtZetaLogCoeff) *
            (Real.log X • selbergSqrtZetaCoeff -
              selbergSqrtZetaLogCoeff)) *
            (ArithmeticFunction.zeta :
              ArithmeticFunction ℝ)) =
        (4 * Real.log X ^ 2) •
            ((selbergSqrtZetaCoeff *
                selbergSqrtZetaCoeff) *
              (ArithmeticFunction.zeta :
                ArithmeticFunction ℝ)) -
          (4 * Real.log X) •
            (((2 : ArithmeticFunction ℝ) *
                (selbergSqrtZetaCoeff *
                  selbergSqrtZetaLogCoeff)) *
              (ArithmeticFunction.zeta :
                ArithmeticFunction ℝ)) +
          (4 : ArithmeticFunction ℝ) *
            ((selbergSqrtZetaLogCoeff *
                selbergSqrtZetaLogCoeff) *
              (ArithmeticFunction.zeta :
                ArithmeticFunction ℝ)) := by
      simp only [Algebra.smul_def, map_mul, map_pow, map_ofNat]
      ring
    _ = (4 * Real.log X ^ 2) •
          (1 : ArithmeticFunction ℝ) -
        (4 * Real.log X) •
          (-ArithmeticFunction.vonMangoldt) +
        ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt := by
      rw [selbergSqrtZetaCoeff_sq_mul_zeta,
        two_mul_selbergSqrtZeta_mul_logCoeff,
        selbergMoebiusLogCoeff_mul_zeta,
        four_mul_selbergSqrtZetaLogCoeff_sq_mul_zeta]
    _ = (4 * Real.log X ^ 2) •
          (1 : ArithmeticFunction ℝ) +
        (4 * Real.log X) •
          ArithmeticFunction.vonMangoldt +
        ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt := by
      simp

/-- For a nontrivial cutoff, the scaled taper is `log X` times the normalized
taper. -/
theorem selbergSqrtZetaScaledTapered_eq_log_smul
    {X : ℕ} (hX : 1 < X) :
    selbergSqrtZetaScaledTapered X =
      Real.log X • selbergSqrtZetaFullTapered X := by
  have hlog : Real.log (X : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hX))
  ext n
  rw [selbergSqrtZetaScaledTapered_apply,
    ArithmeticFunction.smul_map,
    selbergSqrtZetaFullTapered_apply]
  simp only [smul_eq_mul]
  field_simp [hlog]

/-- The normalized global coefficient identity before cancelling the common
factor `4 * log(X)^2`. -/
theorem selbergSqrtZetaFullTapered_collected_denominator_free
    {X : ℕ} (hX : 1 < X) :
    (4 * Real.log X ^ 2) •
        (((selbergSqrtZetaFullTapered X *
            selbergSqrtZetaFullTapered X) *
          (ArithmeticFunction.zeta :
            ArithmeticFunction ℝ))) =
      (4 * Real.log X ^ 2) •
          (1 : ArithmeticFunction ℝ) +
        (4 * Real.log X) •
          ArithmeticFunction.vonMangoldt +
        ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt := by
  have hscaled :=
    selbergSqrtZetaScaledTapered_collected X
  rw [selbergSqrtZetaScaledTapered_eq_log_smul hX] at hscaled
  calc
    (4 * Real.log X ^ 2) •
          (((selbergSqrtZetaFullTapered X *
              selbergSqrtZetaFullTapered X) *
            (ArithmeticFunction.zeta :
              ArithmeticFunction ℝ))) =
        (4 : ArithmeticFunction ℝ) *
          (((Real.log X •
                selbergSqrtZetaFullTapered X) *
              (Real.log X •
                selbergSqrtZetaFullTapered X)) *
            (ArithmeticFunction.zeta :
              ArithmeticFunction ℝ)) := by
      simp only [Algebra.smul_def, map_mul, map_pow, map_ofNat]
      ring
    _ = (4 * Real.log X ^ 2) •
          (1 : ArithmeticFunction ℝ) +
        (4 * Real.log X) •
          ArithmeticFunction.vonMangoldt +
        ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt := hscaled

/-- Complete global identity for the unrestricted tapered square-root zeta
coefficient. -/
theorem selbergSqrtZetaFullTapered_collected
    {X : ℕ} (hX : 1 < X) :
    ((selbergSqrtZetaFullTapered X *
        selbergSqrtZetaFullTapered X) *
      (ArithmeticFunction.zeta :
        ArithmeticFunction ℝ)) =
      (1 : ArithmeticFunction ℝ) +
        (Real.log X)⁻¹ •
          ArithmeticFunction.vonMangoldt +
        (4 * Real.log X ^ 2)⁻¹ •
          (ArithmeticFunction.vonMangoldt *
            ArithmeticFunction.vonMangoldt) := by
  have hlog : Real.log (X : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hX))
  have h :=
    selbergSqrtZetaFullTapered_collected_denominator_free hX
  ext n
  have hn := congrArg (fun f : ArithmeticFunction ℝ => f n) h
  simp only [ArithmeticFunction.smul_map,
    ArithmeticFunction.add_apply, smul_eq_mul] at hn ⊢
  field_simp [hlog]
  convert hn using 1 <;> ring

/-- Inside the cutoff, the finite and unrestricted tapered coefficients
agree. -/
theorem selbergShortTaperedSqrtZeta_eq_full_of_le
    {X n : ℕ} (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    selbergShortTaperedSqrtZeta X n =
      selbergSqrtZetaFullTapered X n := by
  rw [selbergShortTaperedSqrtZeta_apply,
    if_pos (Finset.mem_Icc.mpr ⟨hn1, hnX⟩),
    selbergSqrtZetaFullTapered_apply]
  rfl

/-- In the complete divisor range, truncation does not change the convolution
square. -/
theorem selbergShortTaperedSqrtZeta_sq_eq_full_sq_of_le
    {X n : ℕ} (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    (selbergShortTaperedSqrtZeta X *
        selbergShortTaperedSqrtZeta X) n =
      (selbergSqrtZetaFullTapered X *
        selbergSqrtZetaFullTapered X) n := by
  rw [ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro ij hij
  rcases Nat.mem_divisorsAntidiagonal.mp hij with
    ⟨hprod, hn0⟩
  have hprod0 : ij.1 * ij.2 ≠ 0 := by
    simpa [hprod] using hn0
  have hi0 : ij.1 ≠ 0 :=
    left_ne_zero_of_mul hprod0
  have hj0 : ij.2 ≠ 0 :=
    right_ne_zero_of_mul hprod0
  have hiDvd : ij.1 ∣ n := ⟨ij.2, hprod.symm⟩
  have hjDvd : ij.2 ∣ n :=
    ⟨ij.1, by simpa [Nat.mul_comm] using hprod.symm⟩
  rw [selbergShortTaperedSqrtZeta_eq_full_of_le
      (Nat.one_le_iff_ne_zero.mpr hi0)
      ((Nat.le_of_dvd hn1 hiDvd).trans hnX),
    selbergShortTaperedSqrtZeta_eq_full_of_le
      (Nat.one_le_iff_ne_zero.mpr hj0)
      ((Nat.le_of_dvd hn1 hjDvd).trans hnX)]

/-- Collecting the convolution square against zeta is also unaffected by the
cutoff throughout the complete divisor range. -/
theorem selbergShortTaperedSqrtZeta_collected_eq_full_of_le
    {X n : ℕ} (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    (((selbergShortTaperedSqrtZeta X *
          selbergShortTaperedSqrtZeta X) *
        (ArithmeticFunction.zeta :
          ArithmeticFunction ℝ)) n) =
      (((selbergSqrtZetaFullTapered X *
          selbergSqrtZetaFullTapered X) *
        (ArithmeticFunction.zeta :
          ArithmeticFunction ℝ)) n) := by
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hdDvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hdPos0 : 0 < d :=
    Nat.pos_of_dvd_of_pos hdDvd (by omega)
  have hdPos : 1 ≤ d := by omega
  exact selbergShortTaperedSqrtZeta_sq_eq_full_sq_of_le
    hdPos ((Nat.le_of_dvd hn1 hdDvd).trans hnX)

/-- Exact low-range coefficient formula for the finite Selberg square-root
zeta mollifier. -/
theorem selbergShortTaperedSqrtZeta_collected_apply_of_le
    {X n : ℕ} (hX : 1 < X) (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    (((selbergShortTaperedSqrtZeta X *
          selbergShortTaperedSqrtZeta X) *
        (ArithmeticFunction.zeta :
          ArithmeticFunction ℝ)) n) =
      (if n = 1 then 1 else 0) +
        ArithmeticFunction.vonMangoldt n / Real.log X +
        (ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt) n /
            (4 * Real.log X ^ 2) := by
  rw [selbergShortTaperedSqrtZeta_collected_eq_full_of_le
    hn1 hnX]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (selbergSqrtZetaFullTapered_collected hX)
  simpa only [ArithmeticFunction.one_apply,
    ArithmeticFunction.add_apply,
    ArithmeticFunction.smul_map, smul_eq_mul,
    inv_mul_eq_div] using h

end HardyTheorem
