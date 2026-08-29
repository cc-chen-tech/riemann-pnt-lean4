import PrimeNumberTheorem.MWKFCubicAFEArithmetic

open Complex

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Combined zeta--mollifier phase and its exact diagonal

The first AFE coordinate is the denominator index and the second is the
numerator index.  Thus the structural diagonal is instantiated with
`m = p.2 + 1` and `n = p.1 + 1`.
-/

noncomputable def cubicAFECombinedLogPhase
    (p : ℕ × ℕ) (d e : ℕ) : ℝ :=
  (Real.log (p.2 + 1) - Real.log (p.1 + 1)) +
    (Real.log e - Real.log d)

theorem cubicAFECombinedLogPhase_eq_log_products
    (p : ℕ × ℕ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    cubicAFECombinedLogPhase p d e =
      Real.log ((p.2 + 1) * e) - Real.log ((p.1 + 1) * d) := by
  rw [Real.log_mul (by positivity : (p.2 + 1 : ℝ) ≠ 0)
      (by exact_mod_cast he.ne'),
    Real.log_mul (by positivity : (p.1 + 1 : ℝ) ≠ 0)
      (by exact_mod_cast hd.ne')]
  unfold cubicAFECombinedLogPhase
  ring

theorem cubicAFECombinedLogPhase_eq_zero_of_diagonal
    (p : ℕ × ℕ) {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hdiag : (p.2 + 1) * e = (p.1 + 1) * d) :
    cubicAFECombinedLogPhase p d e = 0 := by
  rw [cubicAFECombinedLogPhase_eq_log_products p hd he]
  have hdiagR :
      ((p.2 : ℝ) + 1) * (e : ℝ) =
        ((p.1 : ℝ) + 1) * (d : ℝ) := by
    exact_mod_cast hdiag
  rw [hdiagR, sub_self]

/-- Product of one critical-line zeta coefficient and one ordered mollifier
pair, before the common product weight is attached. -/
noncomputable def cubicAFECombinedArithmeticFactor
    (t : ℝ) (p : ℕ × ℕ) (d e : ℕ) : ℂ :=
  cubicAFEDirichletTerm t 0 p *
    ((1 / (d : ℂ) ^ cubicCriticalPoint t) *
      (starRingEnd ℂ) (1 / (e : ℂ) ^ cubicCriticalPoint t))

theorem cubicAFECombinedArithmeticFactor_eq_exp
    (t : ℝ) (p : ℕ × ℕ) {d e : ℕ}
    (hd : d ≠ 0) (he : e ≠ 0) :
    cubicAFECombinedArithmeticFactor t p d e =
      ((((Real.sqrt (cubicAFEPositiveIndexProduct p) : ℝ) : ℂ)⁻¹) *
        (((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹)) *
        Complex.exp
          ((I * (cubicAFECombinedLogPhase p d e : ℂ)) * t) := by
  rw [cubicAFECombinedArithmeticFactor,
    cubicAFEDirichletTerm_zero_eq_exp]
  rw [show cubicCriticalPoint t = (1 / 2 : ℂ) + I * t by rfl,
    cubicCriticalPair_eq_exp hd he]
  let A : ℂ := (((Real.sqrt (cubicAFEPositiveIndexProduct p) : ℝ) : ℂ)⁻¹)
  let B : ℂ := (((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹)
  let E₁ : ℂ := Complex.exp
    ((I * ((Real.log (p.2 + 1) - Real.log (p.1 + 1) : ℝ) : ℂ)) * t)
  let E₂ : ℂ := Complex.exp
    ((I * ((Real.log e - Real.log d : ℝ) : ℂ)) * t)
  change A * E₁ * (B * E₂) =
    (A * B) * Complex.exp
      ((I * (cubicAFECombinedLogPhase p d e : ℂ)) * t)
  rw [show A * E₁ * (B * E₂) = (A * B) * (E₁ * E₂) by ring]
  dsimp only [E₁, E₂]
  rw [← Complex.exp_add]
  have hphase :
      (I * ((Real.log (p.2 + 1) - Real.log (p.1 + 1) : ℝ) : ℂ) * t) +
          (I * ((Real.log e - Real.log d : ℝ) : ℂ) * t) =
        (I * (cubicAFECombinedLogPhase p d e : ℂ)) * t := by
    unfold cubicAFECombinedLogPhase
    simp only [Complex.ofReal_add, Complex.ofReal_sub]
    ring
  rw [hphase]

/-- On the exact multiplicative diagonal, the full oscillatory phase is one
and only the positive square-root amplitudes remain. -/
theorem cubicAFECombinedArithmeticFactor_eq_on_diagonal
    (t : ℝ) (p : ℕ × ℕ) {d e : ℕ}
    (hd : 0 < d) (he : 0 < e)
    (hdiag : (p.2 + 1) * e = (p.1 + 1) * d) :
    cubicAFECombinedArithmeticFactor t p d e =
      (((Real.sqrt (cubicAFEPositiveIndexProduct p) : ℝ) : ℂ)⁻¹) *
        (((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹) := by
  rw [cubicAFECombinedArithmeticFactor_eq_exp t p hd.ne' he.ne',
    cubicAFECombinedLogPhase_eq_zero_of_diagonal p hd he hdiag]
  simp

end MWKFCubic
end PrimeNumberTheorem
