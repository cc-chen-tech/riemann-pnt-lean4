import PrimeNumberTheorem.VKEdgePiOverTwoContourBounds
import PrimeNumberTheorem.VKEdgePiOverTwoRightMellin

open Complex Polynomial Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The concrete regularized logarithmic-derivative integrand used on every
edge of the localized zeta rectangle. -/
def localizedRegularizedLogDerivIntegrand
    (A : ℂ[X]) (w : ℂ) (m : ℝ) (z : ℂ) : ℂ :=
  localizedGaussianWeight A w m z *
    (-logDeriv riemannZeta z - z / (z - 1))

/--
At a good height, the finite right edge is exactly the weighted zero sum
plus the three remaining rectangle edges. Zeros are counted by their
analytic multiplicity.

This is the concrete finite-height bridge between the zeta residue theorem
and the infinite right-edge Mellin formula.
-/
theorem exists_rightEdgeIntegral_eq_zero_sum_add_other_edges_of_goodHeight
    (A : ℂ[X]) {u v m T : ℝ}
    (hu : 0 < u) (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∃ zeros : Finset ℂ,
      (∀ rho ∈ zeros,
        riemannZeta rho = 0 ∧
          (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
          -T < rho.im ∧ rho.im < T) ∧
      (∀ rho ∈
          ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
        riemannZeta rho = 0 → rho ∈ zeros) ∧
      (∫ t : ℝ in (-T)..T,
          localizedRegularizedLogDerivIntegrand A
            ((u : ℂ) + I * v) m
            (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        -(2 * Real.pi : ℂ) *
            ∑ rho ∈ zeros,
              (analyticOrderNatAt riemannZeta rho : ℂ) *
                localizedGaussianWeight A
                  ((u : ℂ) + I * v) m rho +
          I *
            ((∫ σ : ℝ in (-1)..(u + 2),
                localizedRegularizedLogDerivIntegrand A
                  ((u : ℂ) + I * v) m
                  ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) -
              ∫ σ : ℝ in (-1)..(u + 2),
                localizedRegularizedLogDerivIntegrand A
                  ((u : ℂ) + I * v) m
                  ((σ : ℂ) + (T : ℂ) * I)) +
          (∫ t : ℝ in (-T)..T,
            localizedRegularizedLogDerivIntegrand A
              ((u : ℂ) + I * v) m
              ((-1 : ℂ) + (t : ℂ) * I)) := by
  let w : ℂ := (u : ℂ) + I * v
  let W : ℂ → ℂ := localizedGaussianWeight A w m
  rcases
      exists_regularizedLogDeriv_boundaryRectIntegral_eq_zero_sum_of_goodHeight
        W (differentiable_localizedGaussianWeight A w m)
        hu hT hgood with
    ⟨zeros, hzeros, hcomplete, hcontour⟩
  refine ⟨zeros, hzeros, hcomplete, ?_⟩
  dsimp [MathlibAux.boundaryRectIntegral] at hcontour
  let bottom : ℂ :=
    ∫ σ : ℝ in (-1)..(u + 2),
      localizedRegularizedLogDerivIntegrand A
        ((u : ℂ) + I * v) m
        ((σ : ℂ) + -((T : ℂ) * I))
  let top : ℂ :=
    ∫ σ : ℝ in (-1)..(u + 2),
      localizedRegularizedLogDerivIntegrand A
        ((u : ℂ) + I * v) m
        ((σ : ℂ) + (T : ℂ) * I)
  let right : ℂ :=
    ∫ t : ℝ in (-T)..T,
      localizedRegularizedLogDerivIntegrand A
        ((u : ℂ) + I * v) m
        ((u : ℂ) + 2 + (t : ℂ) * I)
  let left : ℂ :=
    ∫ t : ℝ in (-T)..T,
      localizedRegularizedLogDerivIntegrand A
        ((u : ℂ) + I * v) m
        (-1 + (t : ℂ) * I)
  let zeroSum : ℂ :=
    ∑ rho ∈ zeros,
      (analyticOrderNatAt riemannZeta rho : ℂ) *
        localizedGaussianWeight A ((u : ℂ) + I * v) m rho
  dsimp [W, w] at hcontour
  norm_num at hcontour ⊢
  change
    bottom - top + I * right - I * left =
      -(2 * Real.pi * I * zeroSum) at hcontour
  change
    right =
      -(2 * Real.pi * zeroSum) +
        I * (bottom - top) + left
  have hrightI :
      I * right =
        -(2 * Real.pi * I) * zeroSum -
          (bottom - top) + I * left := by
    linear_combination hcontour
  calc
    right = (-I) * (I * right) := by
      rw [← mul_assoc, neg_mul, I_mul_I]
      ring
    _ =
        (-I) *
          (-(2 * Real.pi * I) * zeroSum -
            (bottom - top) + I * left) := by
      rw [hrightI]
    _ = _ := by
      ring_nf
      norm_num [I_mul_I, sub_eq_add_neg]

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
