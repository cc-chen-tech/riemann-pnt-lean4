import HardyTheorem.FirstZetaApproximation
import HardyTheorem.ShortIntervalSignChangeMeasure

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Selberg mollifiers on the critical line

The nonnegative factor `normSq (selbergMollifier ...)` cannot create a sign
change.  Consequently every sign change of the mollified Hardy function is a
genuine odd-order zero of the Riemann zeta function on the critical line.
-/

/-- A finite Dirichlet-polynomial mollifier with arbitrary complex
coefficients. -/
noncomputable def selbergMollifier
    (X : ℕ) (coeff : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    coeff n * (1 / (n : ℂ) ^ s)

/-- The Selberg-mollified Hardy function.  The mollifier enters through its
nonnegative squared norm, so this remains real-valued and has no spurious
sign changes. -/
noncomputable def selbergMollifiedHardyZ
    (X : ℕ) (coeff : ℕ → ℂ) (t : ℝ) : ℝ :=
  hardyZ t * Complex.normSq
    (selbergMollifier X coeff ((1 / 2 : ℂ) + I * t))

theorem continuous_selbergMollifier_criticalLine
    (X : ℕ) (coeff : ℕ → ℂ) :
    Continuous (fun t : ℝ =>
      selbergMollifier X coeff ((1 / 2 : ℂ) + I * t)) := by
  unfold selbergMollifier
  apply continuous_finset_sum
  intro n hn
  have hn0 : n ≠ 0 := by
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  rw [show (fun t : ℝ =>
      coeff n * (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))) =
      fun t : ℝ => coeff n *
        (((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
          Complex.exp ((-I * (Real.log n : ℂ)) * t)) by
    funext t
    rw [inv_nat_cpow_criticalLine_eq_exp hn0 t]]
  fun_prop

theorem continuous_selbergMollifiedHardyZ
    (X : ℕ) (coeff : ℕ → ℂ) :
    Continuous (selbergMollifiedHardyZ X coeff) := by
  unfold selbergMollifiedHardyZ
  exact hardyZ_continuous.mul
    (Complex.continuous_normSq.comp
      (continuous_selbergMollifier_criticalLine X coeff))

lemma hardyZ_neg_of_selbergMollifiedHardyZ_neg
    {X : ℕ} {coeff : ℕ → ℂ} {t : ℝ}
    (hneg : selbergMollifiedHardyZ X coeff t < 0) :
    hardyZ t < 0 := by
  unfold selbergMollifiedHardyZ at hneg
  have hweight : 0 ≤ Complex.normSq
      (selbergMollifier X coeff ((1 / 2 : ℂ) + I * t)) :=
    Complex.normSq_nonneg _
  nlinarith

lemma hardyZ_pos_of_selbergMollifiedHardyZ_pos
    {X : ℕ} {coeff : ℕ → ℂ} {t : ℝ}
    (hpos : 0 < selbergMollifiedHardyZ X coeff t) :
    0 < hardyZ t := by
  unfold selbergMollifiedHardyZ at hpos
  have hweight : 0 ≤ Complex.normSq
      (selbergMollifier X coeff ((1 / 2 : ℂ) + I * t)) :=
    Complex.normSq_nonneg _
  nlinarith

/-- A local sign change of the mollified Hardy function is a local sign
change of the genuine Hardy function in the same orientation. -/
theorem hasNegToPosLocalSignChangeAt_hardyZ_of_mollified
    {X : ℕ} {coeff : ℕ → ℂ} {t : ℝ}
    (hchange : HasNegToPosLocalSignChangeAt
      (selbergMollifiedHardyZ X coeff) t) :
    HasNegToPosLocalSignChangeAt hardyZ t := by
  constructor
  · intro epsilon hepsilon
    obtain ⟨x, hx, hneg⟩ := hchange.1 epsilon hepsilon
    exact ⟨x, hx, hardyZ_neg_of_selbergMollifiedHardyZ_neg hneg⟩
  · intro epsilon hepsilon
    obtain ⟨x, hx, hpos⟩ := hchange.2 epsilon hepsilon
    exact ⟨x, hx, hardyZ_pos_of_selbergMollifiedHardyZ_pos hpos⟩

theorem hasPosToNegLocalSignChangeAt_hardyZ_of_mollified
    {X : ℕ} {coeff : ℕ → ℂ} {t : ℝ}
    (hchange : HasPosToNegLocalSignChangeAt
      (selbergMollifiedHardyZ X coeff) t) :
    HasPosToNegLocalSignChangeAt hardyZ t := by
  constructor
  · intro epsilon hepsilon
    obtain ⟨x, hx, hpos⟩ := hchange.1 epsilon hepsilon
    exact ⟨x, hx, hardyZ_pos_of_selbergMollifiedHardyZ_pos hpos⟩
  · intro epsilon hepsilon
    obtain ⟨x, hx, hneg⟩ := hchange.2 epsilon hepsilon
    exact ⟨x, hx, hardyZ_neg_of_selbergMollifiedHardyZ_neg hneg⟩

theorem hasLocalSignChangeAt_hardyZ_of_mollified
    {X : ℕ} {coeff : ℕ → ℂ} {t : ℝ}
    (hchange : HasLocalSignChangeAt
      (selbergMollifiedHardyZ X coeff) t) :
    HasLocalSignChangeAt hardyZ t := by
  rcases hchange with hchange | hchange
  · exact Or.inl
      (hasNegToPosLocalSignChangeAt_hardyZ_of_mollified hchange)
  · exact Or.inr
      (hasPosToNegLocalSignChangeAt_hardyZ_of_mollified hchange)

/-- Selberg's nonnegative mollifier weight preserves the odd analytic
multiplicity detected by a local sign change. -/
theorem odd_analyticOrderNatAt_riemannZeta_of_mollified_localSignChange
    {X : ℕ} {coeff : ℕ → ℂ} {t : ℝ}
    (hchange : HasLocalSignChangeAt
      (selbergMollifiedHardyZ X coeff) t) :
    Odd (analyticOrderNatAt riemannZeta
      ((1 / 2 : ℂ) + I * t)) := by
  rcases hasLocalSignChangeAt_hardyZ_of_mollified hchange with
    hchange | hchange
  · exact odd_analyticOrderNatAt_riemannZeta_of_hardyZ_local_sign_change
      hchange.1 hchange.2
  · exact odd_analyticOrderNatAt_riemannZeta_of_hardyZ_reverse_local_sign_change
      hchange.1 hchange.2

end HardyTheorem
