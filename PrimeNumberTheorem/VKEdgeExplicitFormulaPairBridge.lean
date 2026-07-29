import PrimeNumberTheorem.RiemannVonMangoldt.CriticalLinePartition
import PrimeNumberTheorem.VKEdgeCosineModelAnnihilator
import PrimeNumberTheorem.ZeroForcedOscillation

/-!
# The actual conjugate zero pair behind the cosine model

This module identifies the cosine model used by the annihilator experiments
with the two genuine multiplicity-weighted residues contributed by a
positive-ordinate nontrivial zeta zero and its conjugate. It also removes that
pair exactly from the repository's finite explicit-formula zero sum.

No estimate for the remaining zeros or for the contour error is asserted here.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- One genuine nontrivial-zero residue term in the zeta explicit formula. -/
def explicitFormulaZeroResidueTerm (x : ℝ) (z : ℂ) : ℂ :=
  -(analyticOrderNatAt riemannZeta z : ℂ) * (x : ℂ) ^ z / z

/-- The two residue terms at `rho` and its complex conjugate. -/
def explicitFormulaConjugatePairResidue (x : ℝ) (rho : ℂ) : ℂ :=
  explicitFormulaZeroResidueTerm x rho +
    explicitFormulaZeroResidueTerm x (conj rho)

/-- The conjugate-pair residue after the normalization used for the PNT
error in logarithmic coordinates. -/
def normalizedExplicitFormulaConjugatePair (rho : ℂ) (y : ℝ) : ℂ :=
  ((‖rho‖ * Real.exp (-rho.re * y) : ℝ) : ℂ) *
    explicitFormulaConjugatePairResidue (Real.exp y) rho

/-- The finite residue sum after deleting the target and conjugate points. -/
def finiteNontrivialZeroResidueRemainder
    (x T : ℝ) (rho : ℂ) : ℂ :=
  ∑ z ∈ ((nontrivialZerosFinset T).erase rho).erase (conj rho),
    explicitFormulaZeroResidueTerm x z

/-- The two closed-form terms occurring after the finite nontrivial-zero sum
in the multiplicity-aware explicit formula. -/
def explicitFormulaClosedTerms (y : ℝ) : ℂ :=
  deriv riemannZeta 0 / riemannZeta 0 +
    (1 / 2 : ℂ) *
      (Real.log (1 - Real.exp y ^ (-2 : ℝ)) : ℂ)

/-- The exact finite-height explicit-formula expression left after removing
the target conjugate zero pair from the normalized standard `psi` error.

The four summands are, respectively, the `psi - psi₀` jump correction, all
other finite-height zero residues, the closed-form terms, and the genuine
finite-height approximation error. No bound for this residual is asserted. -/
def normalizedExplicitFormulaResidual
    (rho : ℂ) (T y : ℝ) : ℂ :=
  ((‖rho‖ * Real.exp (-rho.re * y) : ℝ) : ℂ) *
    ((((chebyshevPsi (Real.exp y) - chebyshevPsi0 (Real.exp y) : ℝ) : ℂ)) +
      finiteNontrivialZeroResidueRemainder (Real.exp y) T rho -
      explicitFormulaClosedTerms y -
      (explicitFormulaApproxWithMultiplicity (Real.exp y) T -
        (chebyshevPsi0 (Real.exp y) : ℂ)))

private theorem exp_neg_re_mul_realExp_cpow
    (rho : ℂ) (y : ℝ) :
    ((Real.exp (-rho.re * y) : ℝ) : ℂ) *
        ((Real.exp y : ℝ) : ℂ) ^ rho =
      Complex.exp (I * (rho.im * y)) := by
  rw [ZeroForcedOscillation.realExp_cpow_eq_growth_mul_oscillation
    rho rho.re y rfl]
  rw [show
      ((Real.exp (-rho.re * y) : ℝ) : ℂ) =
        Complex.exp ((-rho.re * y : ℝ) : ℂ) by simp,
    show
      ((Real.exp (rho.re * y) : ℝ) : ℂ) =
        Complex.exp ((rho.re * y : ℝ) : ℂ) by simp,
    ← mul_assoc, ← Complex.exp_add]
  rw [show
      ((-rho.re * y : ℝ) : ℂ) + (rho.re * y : ℝ) = 0 by
    push_cast
    ring]
  simp

private theorem norm_div_eq_exp_neg_arg
    {rho : ℂ} (hrho0 : rho ≠ 0) :
    (‖rho‖ : ℂ) / rho =
      Complex.exp (-((rho.arg : ℂ) * I)) := by
  have hnorm0 : (‖rho‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hrho0
  have hpolar := Complex.norm_mul_exp_arg_mul_I rho
  apply (div_eq_iff hrho0).2
  calc
    (‖rho‖ : ℂ) =
        Complex.exp (-((rho.arg : ℂ) * I)) *
          ((‖rho‖ : ℂ) * Complex.exp ((rho.arg : ℂ) * I)) := by
      calc
        (‖rho‖ : ℂ) =
            (‖rho‖ : ℂ) *
              (Complex.exp (-((rho.arg : ℂ) * I)) *
                Complex.exp ((rho.arg : ℂ) * I)) := by
          rw [← Complex.exp_add]
          simp
        _ = _ := by ring
    _ = Complex.exp (-((rho.arg : ℂ) * I)) * rho := by
      rw [hpolar]

private theorem normalized_single_zero_residue
    {rho : ℂ} (hrho0 : rho ≠ 0) (m : ℕ) (y : ℝ) :
    ((‖rho‖ * Real.exp (-rho.re * y) : ℝ) : ℂ) *
        (-(m : ℂ) * ((Real.exp y : ℝ) : ℂ) ^ rho / rho) =
      -(m : ℂ) *
        Complex.exp (I * ((rho.im * y - rho.arg : ℝ) : ℂ)) := by
  rw [show
      ((‖rho‖ * Real.exp (-rho.re * y) : ℝ) : ℂ) *
          (-(m : ℂ) * ((Real.exp y : ℝ) : ℂ) ^ rho / rho) =
        -(m : ℂ) *
          (((Real.exp (-rho.re * y) : ℝ) : ℂ) *
            ((Real.exp y : ℝ) : ℂ) ^ rho) *
          ((‖rho‖ : ℂ) / rho) by
      push_cast
      ring]
  rw [exp_neg_re_mul_realExp_cpow, norm_div_eq_exp_neg_arg hrho0]
  calc
    -(m : ℂ) * Complex.exp (I * (rho.im * y)) *
          Complex.exp (-((rho.arg : ℂ) * I)) =
        -(m : ℂ) *
          (Complex.exp (I * (rho.im * y)) *
            Complex.exp (-((rho.arg : ℂ) * I))) := by ring
    _ = -(m : ℂ) *
        Complex.exp
          (I * (rho.im * y) - (rho.arg : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 2
    _ = -(m : ℂ) *
        Complex.exp (I * ((rho.im * y - rho.arg : ℝ) : ℂ)) := by
      congr 2
      push_cast
      ring

private theorem exp_I_add_exp_neg_I (t : ℝ) :
    Complex.exp (I * (t : ℂ)) + Complex.exp (-I * (t : ℂ)) =
      (2 * Real.cos t : ℝ) := by
  rw [show I * (t : ℂ) = (t : ℂ) * I by ring, Complex.exp_mul_I]
  rw [show -I * (t : ℂ) = ((-t : ℝ) : ℂ) * I by
    push_cast
    ring,
    Complex.exp_mul_I]
  apply Complex.ext <;> simp <;> ring

/-- The normalized residues of a positive-ordinate nontrivial zero and its
conjugate are exactly the real cosine model used by the annihilator module. -/
theorem normalizedExplicitFormulaConjugatePair_eq_cosineModel
    {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hrhoIm : 0 < rho.im) (y : ℝ) :
    normalizedExplicitFormulaConjugatePair rho y =
      (normalizedCosineModelPair rho y : ℂ) := by
  have hrho0 : rho ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith
  have hconj0 : conj rho ≠ 0 := by simpa using hrho0
  have hm :
      analyticOrderNatAt riemannZeta (conj rho) =
        analyticOrderNatAt riemannZeta rho :=
    RiemannVonMangoldt.analyticOrderNatAt_riemannZeta_conj_of_nontrivialZero
      hrho
  have harg : rho.arg ≠ Real.pi := by
    intro hargEq
    have himZero := (Complex.arg_eq_pi_iff.mp hargEq).2
    linarith
  let theta : ℝ := rho.im * y - rho.arg
  have hfirst := normalized_single_zero_residue hrho0
    (analyticOrderNatAt riemannZeta rho) y
  have hsecond := normalized_single_zero_residue hconj0
    (analyticOrderNatAt riemannZeta (conj rho)) y
  rw [normalizedExplicitFormulaConjugatePair,
    explicitFormulaConjugatePairResidue, mul_add]
  unfold explicitFormulaZeroResidueTerm
  rw [hfirst]
  have hscaleConj :
      ((‖rho‖ * Real.exp (-rho.re * y) : ℝ) : ℂ) *
          (-(analyticOrderNatAt riemannZeta (conj rho) : ℂ) *
              ((Real.exp y : ℝ) : ℂ) ^ (conj rho) / conj rho) =
        -(analyticOrderNatAt riemannZeta rho : ℂ) *
          Complex.exp (-I * ((theta : ℝ) : ℂ)) := by
    rw [show ‖rho‖ = ‖conj rho‖ by simp,
      show rho.re = (conj rho).re by simp,
      hsecond, hm]
    congr 2
    dsimp [theta]
    push_cast
    rw [Complex.arg_conj, if_neg harg]
    simp
    ring
  rw [hscaleConj]
  unfold normalizedCosineModelPair cosinePairModel
  dsimp [theta]
  have hcos :
      Complex.exp (I * ((rho.im * y - rho.arg : ℝ) : ℂ)) +
          Complex.exp (-I * ((rho.im * y - rho.arg : ℝ) : ℂ)) =
        (2 * Real.cos (rho.im * y - rho.arg) : ℝ) := by
    exact exp_I_add_exp_neg_I (rho.im * y - rho.arg)
  calc
    -(analyticOrderNatAt riemannZeta rho : ℂ) *
          Complex.exp (I * ((rho.im * y - rho.arg : ℝ) : ℂ)) +
        -(analyticOrderNatAt riemannZeta rho : ℂ) *
          Complex.exp (-I * ((rho.im * y - rho.arg : ℝ) : ℂ)) =
        -(analyticOrderNatAt riemannZeta rho : ℂ) *
          (Complex.exp (I * ((rho.im * y - rho.arg : ℝ) : ℂ)) +
            Complex.exp (-I * ((rho.im * y - rho.arg : ℝ) : ℂ))) := by
      ring
    _ = -(analyticOrderNatAt riemannZeta rho : ℂ) *
        (2 * Real.cos (rho.im * y - rho.arg) : ℝ) := by
      rw [hcos]
    _ = ((-2 * (analyticOrderNatAt riemannZeta rho : ℝ) *
        Real.cos (rho.im * y - rho.arg) : ℝ) : ℂ) := by
      push_cast
      ring

/-- The sum of genuine residue terms is the negative of the repository's
positive-sign multiplicity-aware zero sum. -/
theorem finiteNontrivialZeroResidueSum_eq_neg (x T : ℝ) :
    (∑ z ∈ nontrivialZerosFinset T,
        explicitFormulaZeroResidueTerm x z) =
      -finiteNontrivialZeroSumWithMultiplicity x T := by
  unfold finiteNontrivialZeroSumWithMultiplicity
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  unfold explicitFormulaZeroResidueTerm
  ring

/-- A positive-ordinate nontrivial zero and its conjugate can be removed
exactly from the finite residue sum once the height cutoff contains them. -/
theorem finiteNontrivialZeroResidueSum_eq_pair_add_remainder
    {rho : ℂ} {x T : ℝ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hrhoIm : 0 < rho.im) (hheight : |rho.im| ≤ T) :
    (∑ z ∈ nontrivialZerosFinset T,
        explicitFormulaZeroResidueTerm x z) =
      explicitFormulaConjugatePairResidue x rho +
        finiteNontrivialZeroResidueRemainder x T rho := by
  classical
  have hrhoMem : rho ∈ nontrivialZerosFinset T :=
    mem_nontrivialZerosFinset.mpr ⟨hrho, hheight⟩
  have hconjZero :
      RiemannHypothesis.IsNontrivialZero (conj rho) :=
    RiemannVonMangoldt.isNontrivialZero_conj hrho
  have hconjHeight : |(conj rho).im| ≤ T := by
    simpa using hheight
  have hconjMem : conj rho ∈ nontrivialZerosFinset T :=
    mem_nontrivialZerosFinset.mpr ⟨hconjZero, hconjHeight⟩
  have hne : conj rho ≠ rho := by
    intro heq
    have him := congrArg Complex.im heq
    simp at him
    linarith
  calc
    (∑ z ∈ nontrivialZerosFinset T,
        explicitFormulaZeroResidueTerm x z) =
        (∑ z ∈ (nontrivialZerosFinset T).erase rho,
          explicitFormulaZeroResidueTerm x z) +
            explicitFormulaZeroResidueTerm x rho :=
      (Finset.sum_erase_add (nontrivialZerosFinset T)
        (fun z => explicitFormulaZeroResidueTerm x z) hrhoMem).symm
    _ =
        ((∑ z ∈ ((nontrivialZerosFinset T).erase rho).erase (conj rho),
            explicitFormulaZeroResidueTerm x z) +
          explicitFormulaZeroResidueTerm x (conj rho)) +
            explicitFormulaZeroResidueTerm x rho := by
      rw [Finset.sum_erase_add
        ((nontrivialZerosFinset T).erase rho)
        (fun z => explicitFormulaZeroResidueTerm x z)
        (Finset.mem_erase.mpr ⟨hne, hconjMem⟩)]
    _ = explicitFormulaConjugatePairResidue x rho +
        finiteNontrivialZeroResidueRemainder x T rho := by
      unfold explicitFormulaConjugatePairResidue
      dsimp [finiteNontrivialZeroResidueRemainder]
      ring

/-- The residual used by the cosine-model detector is exactly the normalized
finite-height explicit-formula residual once the target zero and its conjugate
are present in the truncation.

This is an identification theorem only: it does not estimate the other zeros,
the finite-height approximation error, or the `psi - psi₀` jump correction. -/
theorem normalizedPsiModelResidual_eq_explicitFormulaResidual
    {rho : ℂ} {T : ℝ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hrhoIm : 0 < rho.im) (hheight : |rho.im| ≤ T) (y : ℝ) :
    (normalizedPsiModelResidual rho y : ℂ) =
      normalizedExplicitFormulaResidual rho T y := by
  have hpair :=
    normalizedExplicitFormulaConjugatePair_eq_cosineModel hrho hrhoIm y
  have hsum :=
    finiteNontrivialZeroResidueSum_eq_pair_add_remainder
      (rho := rho) (x := Real.exp y) hrho hrhoIm hheight
  have hdecomp :
      explicitFormulaConjugatePairResidue (Real.exp y) rho +
          finiteNontrivialZeroResidueRemainder (Real.exp y) T rho =
        -finiteNontrivialZeroSumWithMultiplicity (Real.exp y) T := by
    calc
      explicitFormulaConjugatePairResidue (Real.exp y) rho +
          finiteNontrivialZeroResidueRemainder (Real.exp y) T rho =
          ∑ z ∈ nontrivialZerosFinset T,
            explicitFormulaZeroResidueTerm (Real.exp y) z := hsum.symm
      _ = -finiteNontrivialZeroSumWithMultiplicity (Real.exp y) T :=
        finiteNontrivialZeroResidueSum_eq_neg (Real.exp y) T
  unfold normalizedPsiModelResidual normalizedPsiError
  push_cast
  rw [← hpair]
  unfold normalizedExplicitFormulaConjugatePair
  unfold normalizedExplicitFormulaResidual explicitFormulaClosedTerms
  rw [show
      explicitFormulaConjugatePairResidue (Real.exp y) rho =
        -finiteNontrivialZeroSumWithMultiplicity (Real.exp y) T -
          finiteNontrivialZeroResidueRemainder (Real.exp y) T rho by
    linear_combination hdecomp]
  unfold explicitFormulaApproxWithMultiplicity
  push_cast
  ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
