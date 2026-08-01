import HardyTheorem.SelbergMollifiedTripleCollected
import HardyTheorem.VerticalGammaAsymptotic

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Attaching the Hardy phase to the collected Selberg polynomial

Multiplication by `exp (I * thetaModel t)` translates every logarithmic
frequency of the sign-preserving Selberg triple polynomial by the same
nonlinear Hardy phase.  This file records the translation both before and
after collecting equal rational frequencies.
-/

/-- The Hardy phase attached to the reduced rational frequency `q`. -/
noncomputable def selbergMollifiedHardyPhaseFrequency
    (q : ℚ) (t : ℝ) : ℝ :=
  thetaModel t + selbergMollifiedTripleCollectedFrequency q * t

/-- The phase-attached triple polynomial before equal rational frequencies
are collected. -/
noncomputable def selbergMollifiedHardyPhasePolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ selbergMollifiedTripleSupport N X,
    selbergMollifiedTripleCoeff X p *
      Complex.exp
        (I *
          ((thetaModel t + selbergMollifiedTripleFrequency p * t : ℝ) : ℂ))

/-- The phase-attached triple polynomial after collecting by the reduced
rational key `q = l/(m*n)`. -/
noncomputable def selbergMollifiedHardyPhaseCollectedPolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  ∑ q ∈ selbergMollifiedTripleCollectedSupport N X,
    selbergMollifiedTripleCollectedCoeff N X q *
      Complex.exp (I * (selbergMollifiedHardyPhaseFrequency q t : ℂ))

private theorem exp_I_thetaModel_add_frequency
    (omega t : ℝ) :
    Complex.exp
        (I * ((thetaModel t + omega * t : ℝ) : ℂ)) =
      Complex.exp (I * (thetaModel t : ℂ)) *
        Complex.exp (I * ((omega * t : ℝ) : ℂ)) := by
  rw [show I * ((thetaModel t + omega * t : ℝ) : ℂ) =
      I * (thetaModel t : ℂ) + I * ((omega * t : ℝ) : ℂ) by
    push_cast
    ring]
  exact Complex.exp_add _ _

/-- Attaching the Hardy phase termwise before collection is exactly
multiplication of the original triple polynomial by the common phase. -/
theorem selbergMollifiedHardyPhasePolynomial_eq_exp_mul_triplePolynomial
    (N X : ℕ) (t : ℝ) :
    selbergMollifiedHardyPhasePolynomial N X t =
      Complex.exp (I * (thetaModel t : ℂ)) *
        selbergMollifiedTriplePolynomial N X t := by
  classical
  unfold selbergMollifiedHardyPhasePolynomial
  unfold selbergMollifiedTriplePolynomial
  unfold MathlibAux.exponentialPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [exp_I_thetaModel_add_frequency]
  have hcast :
      ((selbergMollifiedTripleFrequency p * t : ℝ) : ℂ) =
        (selbergMollifiedTripleFrequency p : ℂ) * (t : ℂ) := by
    exact Complex.ofReal_mul _ _
  rw [hcast]
  ring

/-- Attaching the Hardy phase after collection is exactly multiplication of
the collected triple polynomial by the same common phase. -/
theorem
    selbergMollifiedHardyPhaseCollectedPolynomial_eq_exp_mul_collectedPolynomial
    (N X : ℕ) (t : ℝ) :
    selbergMollifiedHardyPhaseCollectedPolynomial N X t =
      Complex.exp (I * (thetaModel t : ℂ)) *
        selbergMollifiedTripleCollectedPolynomial N X t := by
  classical
  unfold selbergMollifiedHardyPhaseCollectedPolynomial
  unfold selbergMollifiedHardyPhaseFrequency
  unfold selbergMollifiedTripleCollectedPolynomial
  unfold MathlibAux.exponentialPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [exp_I_thetaModel_add_frequency]
  have hcast :
      ((selbergMollifiedTripleCollectedFrequency q * t : ℝ) : ℂ) =
        (selbergMollifiedTripleCollectedFrequency q : ℂ) * (t : ℂ) := by
    exact Complex.ofReal_mul _ _
  rw [hcast]
  ring

/-- Collecting equal reduced rational frequencies commutes exactly with
attaching the Hardy phase. -/
theorem selbergMollifiedHardyPhasePolynomial_eq_collectedPolynomial
    (N X : ℕ) (t : ℝ) :
    selbergMollifiedHardyPhasePolynomial N X t =
      selbergMollifiedHardyPhaseCollectedPolynomial N X t := by
  rw [selbergMollifiedHardyPhasePolynomial_eq_exp_mul_triplePolynomial,
    selbergMollifiedHardyPhaseCollectedPolynomial_eq_exp_mul_collectedPolynomial,
    selbergMollifiedTriplePolynomial_eq_collectedPolynomial]

/-- The phase-attached polynomial is exactly the finite zeta polynomial times
the sign-preserving mollifier weight, rotated by the model Hardy phase. -/
theorem
    exp_I_thetaModel_mul_criticalLinePolynomial_mul_mollifier_mul_conj_eq_phasePolynomial
    (N X : ℕ) (t : ℝ) :
    Complex.exp (I * (thetaModel t : ℂ)) *
        (((∑ m ∈ Finset.Icc 1 N,
            1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
          (starRingEnd ℂ)
            (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
      selbergMollifiedHardyPhasePolynomial N X t := by
  rw [criticalLineDirichletPolynomial_mul_mollifier_mul_conj_eq_exponentialPolynomial]
  exact
    (selbergMollifiedHardyPhasePolynomial_eq_exp_mul_triplePolynomial
      N X t).symm

/-- The same rotated finite product is represented exactly by the polynomial
collected over reduced positive rational frequencies. -/
theorem
    exp_I_thetaModel_mul_criticalLinePolynomial_mul_mollifier_mul_conj_eq_collectedPhasePolynomial
    (N X : ℕ) (t : ℝ) :
    Complex.exp (I * (thetaModel t : ℂ)) *
        (((∑ m ∈ Finset.Icc 1 N,
            1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) *
          (starRingEnd ℂ)
            (selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
      selbergMollifiedHardyPhaseCollectedPolynomial N X t := by
  rw [
    exp_I_thetaModel_mul_criticalLinePolynomial_mul_mollifier_mul_conj_eq_phasePolynomial,
    selbergMollifiedHardyPhasePolynomial_eq_collectedPolynomial]

end HardyTheorem
