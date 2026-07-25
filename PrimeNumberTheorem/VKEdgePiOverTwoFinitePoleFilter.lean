import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic

open Polynomial

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- A normalized linear factor that vanishes at the nonzero offset `z`. -/
def poleFactor (z : ℂ) : ℂ[X] :=
  1 - C z⁻¹ * X

/--
The finite-pole filter used when the distinguished pole is centered at zero.
The zero offset is omitted, so the target residue is retained with weight one.
-/
def targetPreservingPoleFilter (offsets : Finset ℂ) : ℂ[X] :=
  ∏ z ∈ offsets.erase 0, poleFactor z

/--
The finite-pole filter used when the center is not a retained pole. Every
nonzero listed offset is annihilated.
-/
def emptyCenterPoleFilter (offsets : Finset ℂ) : ℂ[X] :=
  ∏ z ∈ offsets, poleFactor z

/-- Coefficientwise complex conjugation of a polynomial. -/
def conjugatePolynomial (p : ℂ[X]) : ℂ[X] :=
  p.map (starRingEnd ℂ)

theorem poleFactor_eval_zero (z : ℂ) :
    (poleFactor z).eval 0 = 1 := by
  simp [poleFactor]

theorem poleFactor_eval_self {z : ℂ} (hz : z ≠ 0) :
    (poleFactor z).eval z = 0 := by
  simp [poleFactor, hz]

theorem targetPreservingPoleFilter_eval_zero (offsets : Finset ℂ) :
    (targetPreservingPoleFilter offsets).eval 0 = 1 := by
  rw [targetPreservingPoleFilter, eval_prod]
  simp [poleFactor_eval_zero]

theorem targetPreservingPoleFilter_eval_eq_zero
    {offsets : Finset ℂ} {z : ℂ}
    (hz : z ∈ offsets) (hz0 : z ≠ 0) :
    (targetPreservingPoleFilter offsets).eval z = 0 := by
  rw [targetPreservingPoleFilter, eval_prod]
  apply Finset.prod_eq_zero (i := z)
  · exact Finset.mem_erase.mpr ⟨hz0, hz⟩
  · exact poleFactor_eval_self hz0

theorem emptyCenterPoleFilter_eval_eq_zero
    {offsets : Finset ℂ} {z : ℂ}
    (hz : z ∈ offsets) (hz0 : z ≠ 0) :
    (emptyCenterPoleFilter offsets).eval z = 0 := by
  rw [emptyCenterPoleFilter, eval_prod]
  apply Finset.prod_eq_zero (i := z) hz
  exact poleFactor_eval_self hz0

theorem conjugatePolynomial_eval_star (p : ℂ[X]) (z : ℂ) :
    (conjugatePolynomial p).eval (star z) = star (p.eval z) := by
  exact Polynomial.eval_map_apply (p := p) (starRingEnd ℂ) z

private theorem conjugatePolynomial_poleFactor (z : ℂ) :
    conjugatePolynomial (poleFactor z) = poleFactor (star z) := by
  unfold conjugatePolynomial poleFactor
  rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X]
  simp only [map_inv₀, starRingEnd_apply]

theorem conjugatePolynomial_targetPreservingPoleFilter
    (offsets : Finset ℂ) :
    conjugatePolynomial (targetPreservingPoleFilter offsets) =
      targetPreservingPoleFilter (offsets.image fun z => star z) := by
  classical
  have hstar : Function.Injective (fun z : ℂ => star z) := star_injective
  unfold conjugatePolynomial targetPreservingPoleFilter
  rw [Polynomial.map_prod]
  simp_rw [show ∀ z : ℂ,
      (poleFactor z).map (starRingEnd ℂ) = poleFactor (star z) by
        intro z
        exact conjugatePolynomial_poleFactor z]
  rw [← Finset.prod_image hstar.injOn]
  rw [Finset.image_erase hstar offsets 0]
  simp

theorem conjugatePolynomial_emptyCenterPoleFilter
    (offsets : Finset ℂ) :
    conjugatePolynomial (emptyCenterPoleFilter offsets) =
      emptyCenterPoleFilter (offsets.image fun z => star z) := by
  classical
  have hstar : Function.Injective (fun z : ℂ => star z) := star_injective
  unfold conjugatePolynomial emptyCenterPoleFilter
  rw [Polynomial.map_prod]
  simp_rw [show ∀ z : ℂ,
      (poleFactor z).map (starRingEnd ℂ) = poleFactor (star z) by
        intro z
        exact conjugatePolynomial_poleFactor z]
  exact (Finset.prod_image hstar.injOn).symm

/-!
The factors above model simple logarithmic-derivative poles. Analytic
multiplicity belongs in the corresponding residue coefficient; it does not
require repeating a root in these annihilating polynomials.
-/

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
