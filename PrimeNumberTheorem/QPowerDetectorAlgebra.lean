import Mathlib

open Polynomial
open scoped BigOperators

namespace PrimeNumberTheorem
namespace PrimeSideDetector

noncomputable section

def qPowerNode (q : Nat) (s : Complex) : Complex :=
  Complex.exp (-(s * Real.log q))

theorem qPowerNode_one {q : Nat} (hq : q ≠ 0) :
    qPowerNode q 1 = ((q : Real)⁻¹ : Complex) := by
  have hqpos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero hq
  rw [qPowerNode, one_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    Real.exp_neg, Real.exp_log hqpos, Complex.ofReal_inv]

def evalRealPolynomial (p : Polynomial Real) (z : Complex) : Complex :=
  (p.map Complex.ofRealHom).eval z

def realNodeFactor (r : Real) : Polynomial Real := X - C r

def conjugatePairFactor (z : Complex) : Polynomial Real :=
  X ^ 2 - C (2 * z.re) * X + C (Complex.normSq z)

theorem evalRealPolynomial_realNodeFactor_self (r : Real) :
    evalRealPolynomial (realNodeFactor r) r = 0 := by
  simp [evalRealPolynomial, realNodeFactor]

theorem evalRealPolynomial_conjugatePairFactor_left (z : Complex) :
    evalRealPolynomial (conjugatePairFactor z) z = 0 := by
  apply Complex.ext <;>
    simp [evalRealPolynomial, conjugatePairFactor, pow_two,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem evalRealPolynomial_conjugatePairFactor_right (z : Complex) :
    evalRealPolynomial (conjugatePairFactor z) (star z) = 0 := by
  apply Complex.ext <;>
    simp [evalRealPolynomial, conjugatePairFactor, pow_two,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
    ring

def realLinearInterpolator (z w : Complex) : Polynomial Real :=
  if z.im = 0 then
    C w.re
  else
    C (w.re - (w.im / z.im) * z.re) +
      C (w.im / z.im) * X

theorem evalRealPolynomial_realLinearInterpolator
    {z w : Complex} (hcompat : z.im = 0 → w.im = 0) :
    evalRealPolynomial (realLinearInterpolator z w) z = w := by
  by_cases hz : z.im = 0
  · apply Complex.ext <;>
      simp [realLinearInterpolator, hz, evalRealPolynomial, hcompat hz]
  · apply Complex.ext <;>
      simp [realLinearInterpolator, hz, evalRealPolynomial,
        Complex.mul_re, Complex.mul_im]

private theorem evalRealPolynomial_mul
    (p q : Polynomial Real) (z : Complex) :
    evalRealPolynomial (p * q) z =
      evalRealPolynomial p z * evalRealPolynomial q z := by
  simp [evalRealPolynomial]

private theorem evalRealPolynomial_finset_prod
    {ι : Type*} (s : Finset ι) (p : ι → Polynomial Real) (z : Complex) :
    evalRealPolynomial (∏ i ∈ s, p i) z =
      ∏ i ∈ s, evalRealPolynomial (p i) z := by
  simp only [evalRealPolynomial, ← Polynomial.eval₂_eq_eval_map,
    Polynomial.eval₂_finset_prod]

private theorem evalRealPolynomial_im_eq_zero_of_im_eq_zero
    (p : Polynomial Real) {z : Complex} (hz : z.im = 0) :
    (evalRealPolynomial p z).im = 0 := by
  have hzreal : z = (z.re : Complex) := by
    apply Complex.ext <;> simp [hz]
  rw [hzreal]
  rw [evalRealPolynomial, ← Polynomial.eval₂_eq_eval_map]
  change (p.eval₂ Complex.ofRealHom (Complex.ofRealHom z.re)).im = 0
  rw [Polynomial.eval₂_at_apply]
  exact Complex.ofReal_im _

def qPowerAnnihilator
    (q : Nat) (realNodes : Finset Real) (pairNodes : Finset Complex) : Polynomial Real :=
  realNodeFactor ((q : Real)⁻¹) *
    (∏ r ∈ realNodes, realNodeFactor r) *
    (∏ z ∈ pairNodes, conjugatePairFactor z)

def normalizedQPowerPolynomial
    (q : Nat) (realNodes : Finset Real) (pairNodes : Finset Complex)
    (z0 : Complex) : Polynomial Real :=
  let D := qPowerAnnihilator q realNodes pairNodes
  let w := (evalRealPolynomial D z0)⁻¹
  D * realLinearInterpolator z0 w

private theorem qPowerAnnihilator_eval_main
    (q : Nat) (realNodes : Finset Real) (pairNodes : Finset Complex) :
    evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes)
      ((q : Real)⁻¹) = 0 := by
  unfold qPowerAnnihilator
  rw [← Complex.ofReal_inv, evalRealPolynomial_mul, evalRealPolynomial_mul,
    evalRealPolynomial_realNodeFactor_self]
  simp

private theorem qPowerAnnihilator_eval_realNode
    {q : Nat} {realNodes : Finset Real} {pairNodes : Finset Complex}
    {r : Real} (hr : r ∈ realNodes) :
    evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes) r = 0 := by
  have hprod :
      evalRealPolynomial (∏ x ∈ realNodes, realNodeFactor x) r = 0 := by
    rw [evalRealPolynomial_finset_prod]
    apply Finset.prod_eq_zero (i := r) hr
    exact evalRealPolynomial_realNodeFactor_self r
  unfold qPowerAnnihilator
  rw [evalRealPolynomial_mul, evalRealPolynomial_mul, hprod]
  simp

private theorem qPowerAnnihilator_eval_pairNode
    {q : Nat} {realNodes : Finset Real} {pairNodes : Finset Complex}
    {z : Complex} (hz : z ∈ pairNodes) :
    evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes) z = 0 := by
  have hprod :
      evalRealPolynomial (∏ w ∈ pairNodes, conjugatePairFactor w) z = 0 := by
    rw [evalRealPolynomial_finset_prod]
    apply Finset.prod_eq_zero (i := z) hz
    exact evalRealPolynomial_conjugatePairFactor_left z
  unfold qPowerAnnihilator
  rw [evalRealPolynomial_mul, hprod]
  simp

theorem normalizedQPowerPolynomial_eval_target
    {q : Nat} {realNodes : Finset Real} {pairNodes : Finset Complex}
    {z0 : Complex}
    (hD : evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes) z0 ≠ 0) :
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0) z0 = 1 := by
  have hcompat :
      z0.im = 0 →
        ((evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes) z0)⁻¹).im = 0 := by
    intro hz
    rw [Complex.inv_im,
      evalRealPolynomial_im_eq_zero_of_im_eq_zero
        (qPowerAnnihilator q realNodes pairNodes) hz]
    simp
  unfold normalizedQPowerPolynomial
  rw [evalRealPolynomial_mul,
    evalRealPolynomial_realLinearInterpolator hcompat, mul_comm,
    inv_mul_cancel₀ hD]

theorem normalizedQPowerPolynomial_eval_main
    {q : Nat} {realNodes : Finset Real} {pairNodes : Finset Complex}
    {z0 : Complex} (_hq : q ≠ 0) :
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0)
      ((q : Real)⁻¹) = 0 := by
  unfold normalizedQPowerPolynomial
  rw [evalRealPolynomial_mul,
    qPowerAnnihilator_eval_main q realNodes pairNodes]
  simp

theorem normalizedQPowerPolynomial_eval_realNode
    {q : Nat} {realNodes : Finset Real} {pairNodes : Finset Complex}
    {z0 : Complex} {r : Real} (hr : r ∈ realNodes) :
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0) r = 0 := by
  unfold normalizedQPowerPolynomial
  rw [evalRealPolynomial_mul, qPowerAnnihilator_eval_realNode hr]
  simp

theorem normalizedQPowerPolynomial_eval_pairNode
    {q : Nat} {realNodes : Finset Real} {pairNodes : Finset Complex}
    {z0 z : Complex} (hz : z ∈ pairNodes) :
    evalRealPolynomial
      (normalizedQPowerPolynomial q realNodes pairNodes z0) z = 0 := by
  unfold normalizedQPowerPolynomial
  rw [evalRealPolynomial_mul, qPowerAnnihilator_eval_pairNode hz]
  simp

def qPowerDetector (q : Nat) (H : Polynomial Real) (s : Complex) : Complex :=
  evalRealPolynomial H (qPowerNode q s)

theorem qPowerDetector_eq_polynomial_eval
    (q : Nat) (H : Polynomial Real) (s : Complex) :
    qPowerDetector q H s = evalRealPolynomial H (qPowerNode q s) := rfl

theorem qPowerDetector_eq_coeff_sum
    (q : Nat) (H : Polynomial Real) (s : Complex) :
    qPowerDetector q H s =
      ∑ k ∈ H.support, (H.coeff k : Complex) * (qPowerNode q s) ^ k := by
  unfold qPowerDetector evalRealPolynomial
  rw [← Polynomial.eval₂_eq_eval_map]
  simp [Polynomial.eval₂_eq_sum, Polynomial.sum_def]

def normalizedQPowerDetector
    (q : Nat) (realNodes : Finset Real) (pairNodes : Finset Complex)
    (s0 s : Complex) : Complex :=
  qPowerDetector q
    (normalizedQPowerPolynomial q realNodes pairNodes (qPowerNode q s0)) s

theorem normalizedQPowerDetector_at_target
    {q : Nat} {realNodes : Finset Real} {pairNodes : Finset Complex}
    {s0 : Complex}
    (hD : evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes)
      (qPowerNode q s0) ≠ 0) :
    normalizedQPowerDetector q realNodes pairNodes s0 s0 = 1 := by
  unfold normalizedQPowerDetector qPowerDetector
  exact normalizedQPowerPolynomial_eval_target hD

theorem normalizedQPowerDetector_at_one
    {q : Nat} {realNodes : Finset Real} {pairNodes : Finset Complex}
    {s0 : Complex} (hq : q ≠ 0) :
    normalizedQPowerDetector q realNodes pairNodes s0 1 = 0 := by
  unfold normalizedQPowerDetector qPowerDetector
  rw [qPowerNode_one hq]
  exact normalizedQPowerPolynomial_eval_main hq

end

end PrimeSideDetector
end PrimeNumberTheorem
