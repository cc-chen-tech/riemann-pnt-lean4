import PrimeNumberTheorem.VKEdgePiOverTwoCenteredMellin

open Complex Filter MeasureTheory Polynomial Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The regularized logarithmic-derivative integrand with center coefficient
`q`. -/
def localizedRegularizedLogDerivIntegrandAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ) (z : ℂ) : ℂ :=
  localizedGaussianWeightAtCenter q A w m z *
    (-logDeriv riemannZeta z - z / (z - 1))

/-- The centered polynomial-Gaussian weight is entire. -/
theorem differentiable_localizedGaussianWeightAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    Differentiable ℂ (localizedGaussianWeightAtCenter q A w m) := by
  unfold localizedGaussianWeightAtCenter
  fun_prop

/-- The infinite geometric right edge equals the centered Gaussian average. -/
theorem
    integral_localizedRegularizedLogDerivIntegrandAtCenter_verticalLine_eq
    (q : ℝ) (A : ℂ[X]) {u v m : ℝ} (hu : 0 < u) (hm : 0 < m) :
    (∫ t : ℝ,
        localizedRegularizedLogDerivIntegrandAtCenter q A
          ((u : ℂ) + I * v) m
          (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      localizedPsiGaussianAverageAtCenter q A
        ((u : ℂ) + I * v) m := by
  let w : ℂ := (u : ℂ) + I * v
  let f : ℝ → ℂ := fun t =>
    localizedRegularizedLogDerivIntegrandAtCenter q A w m
      (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hw : 0 < w.re := by
    simpa [w] using hu
  have hmellin :=
    integral_localizedGaussianWeightAtCenter_mul_regularizedLogDeriv_rightEdge_eq
      q A hm hw
  calc
    (∫ t : ℝ,
        localizedRegularizedLogDerivIntegrandAtCenter q A
          ((u : ℂ) + I * v) m
          (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ, f t := by
      rfl
    _ = ∫ t : ℝ, f (t + v) :=
      (integral_add_right_eq_self f v).symm
    _ =
        ∫ t : ℝ,
          localizedGaussianWeightAtCenter q A w m
              (w + ((2 : ℂ) + I * (t : ℂ))) *
            (-logDeriv riemannZeta
                (w + ((2 : ℂ) + I * (t : ℂ))) -
              (w + ((2 : ℂ) + I * (t : ℂ))) /
                (w + ((2 : ℂ) + I * (t : ℂ)) - 1)) := by
      apply integral_congr_ae
      filter_upwards with t
      have hz :
          (((u + 2 : ℝ) : ℂ) + (((t + v : ℝ) : ℂ) * I)) =
            w + ((2 : ℂ) + I * (t : ℂ)) := by
        simp only [w, ofReal_add]
        push_cast
        ring
      simpa only [
        f,
        localizedRegularizedLogDerivIntegrandAtCenter,
        hz]
    _ = _ := by
      simpa [w] using hmellin

/-- The analytic-multiplicity weighted zero contribution at center
coefficient `q`. -/
def localizedZeroResidueSumAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ)
    (zeros : Finset ℂ) : ℂ :=
  ∑ rho ∈ zeros,
    (analyticOrderNatAt riemannZeta rho : ℂ) *
      localizedGaussianWeightAtCenter q A w m rho

/-- The bottom, top, and left rectangle edges at center coefficient `q`. -/
def localizedOtherEdgeContributionAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m u T : ℝ) : ℂ :=
  I *
      ((∫ σ : ℝ in (-1)..(u + 2),
          localizedRegularizedLogDerivIntegrandAtCenter q A w m
            ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) -
        ∫ σ : ℝ in (-1)..(u + 2),
          localizedRegularizedLogDerivIntegrandAtCenter q A w m
            ((σ : ℂ) + (T : ℂ) * I)) +
    ∫ t : ℝ in (-T)..T,
      localizedRegularizedLogDerivIntegrandAtCenter q A w m
        ((-1 : ℂ) + (t : ℂ) * I)

/-- The discarded tails of the infinite right edge at center coefficient
`q`. -/
def localizedRightEdgeTailAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m u T : ℝ) : ℂ :=
  (∫ t : ℝ,
      localizedRegularizedLogDerivIntegrandAtCenter q A w m
        (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) -
    ∫ t : ℝ in (-T)..T,
      localizedRegularizedLogDerivIntegrandAtCenter q A w m
        (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)

/-- The exact finite-height remainder at center coefficient `q`. -/
def localizedContourRemainderAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m u T : ℝ) : ℂ :=
  localizedOtherEdgeContributionAtCenter q A w m u T +
    localizedRightEdgeTailAtCenter q A w m u T

/--
At a good height, the finite right edge is the centered zero sum plus the
other three rectangle edges.

The zero residue and the exact cancellations at `s = 0` and `s = 1` come
from the general analytic-weight regularized zeta contour theorem.
-/
theorem
    exists_rightEdgeIntegralAtCenter_eq_zero_sum_add_other_edges_of_goodHeight
    (q : ℝ) (A : ℂ[X]) {u v m T : ℝ}
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
          localizedRegularizedLogDerivIntegrandAtCenter q A
            ((u : ℂ) + I * v) m
            (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        -(2 * Real.pi : ℂ) *
            ∑ rho ∈ zeros,
              (analyticOrderNatAt riemannZeta rho : ℂ) *
                localizedGaussianWeightAtCenter q A
                  ((u : ℂ) + I * v) m rho +
          I *
            ((∫ σ : ℝ in (-1)..(u + 2),
                localizedRegularizedLogDerivIntegrandAtCenter q A
                  ((u : ℂ) + I * v) m
                  ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) -
              ∫ σ : ℝ in (-1)..(u + 2),
                localizedRegularizedLogDerivIntegrandAtCenter q A
                  ((u : ℂ) + I * v) m
                  ((σ : ℂ) + (T : ℂ) * I)) +
          (∫ t : ℝ in (-T)..T,
            localizedRegularizedLogDerivIntegrandAtCenter q A
              ((u : ℂ) + I * v) m
              ((-1 : ℂ) + (t : ℂ) * I)) := by
  let w : ℂ := (u : ℂ) + I * v
  let W : ℂ → ℂ := localizedGaussianWeightAtCenter q A w m
  rcases
      exists_regularizedLogDeriv_boundaryRectIntegral_eq_zero_sum_of_goodHeight
        W (differentiable_localizedGaussianWeightAtCenter q A w m)
        hu hT hgood with
    ⟨zeros, hzeros, hcomplete, hcontour⟩
  refine ⟨zeros, hzeros, hcomplete, ?_⟩
  dsimp [MathlibAux.boundaryRectIntegral] at hcontour
  let bottom : ℂ :=
    ∫ σ : ℝ in (-1)..(u + 2),
      localizedRegularizedLogDerivIntegrandAtCenter q A
        ((u : ℂ) + I * v) m
        ((σ : ℂ) + -((T : ℂ) * I))
  let top : ℂ :=
    ∫ σ : ℝ in (-1)..(u + 2),
      localizedRegularizedLogDerivIntegrandAtCenter q A
        ((u : ℂ) + I * v) m
        ((σ : ℂ) + (T : ℂ) * I)
  let right : ℂ :=
    ∫ t : ℝ in (-T)..T,
      localizedRegularizedLogDerivIntegrandAtCenter q A
        ((u : ℂ) + I * v) m
        ((u : ℂ) + 2 + (t : ℂ) * I)
  let left : ℂ :=
    ∫ t : ℝ in (-T)..T,
      localizedRegularizedLogDerivIntegrandAtCenter q A
        ((u : ℂ) + I * v) m
        (-1 + (t : ℂ) * I)
  let zeroSum : ℂ :=
    ∑ rho ∈ zeros,
      (analyticOrderNatAt riemannZeta rho : ℂ) *
        localizedGaussianWeightAtCenter q A
          ((u : ℂ) + I * v) m rho
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

/--
The centered Chebyshev-error average equals the analytic-multiplicity zero
sum plus the named finite-height remainder.
-/
theorem
    exists_localizedPsiGaussianAverageAtCenter_eq_zeroSum_add_contourRemainder_of_goodHeight
    (q : ℝ) (A : ℂ[X]) {u v m T : ℝ}
    (hu : 0 < u) (hm : 0 < m) (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∃ zeros : Finset ℂ,
      (∀ rho ∈ zeros,
        riemannZeta rho = 0 ∧
          (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
          -T < rho.im ∧ rho.im < T) ∧
      (∀ rho ∈
          ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
        riemannZeta rho = 0 → rho ∈ zeros) ∧
      localizedPsiGaussianAverageAtCenter q A
          ((u : ℂ) + I * v) m =
        -(2 * Real.pi : ℂ) *
            localizedZeroResidueSumAtCenter q A
              ((u : ℂ) + I * v) m zeros +
          localizedContourRemainderAtCenter q A
            ((u : ℂ) + I * v) m u T := by
  rcases
      exists_rightEdgeIntegralAtCenter_eq_zero_sum_add_other_edges_of_goodHeight
        q A (u := u) (v := v) (m := m) (T := T) hu hT hgood with
    ⟨zeros, hzeros, hcomplete, hfinite⟩
  refine ⟨zeros, hzeros, hcomplete, ?_⟩
  have hinfinite :
      (∫ t : ℝ,
          localizedRegularizedLogDerivIntegrandAtCenter q A
            ((u : ℂ) + I * v) m
            (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        localizedPsiGaussianAverageAtCenter q A
          ((u : ℂ) + I * v) m :=
    integral_localizedRegularizedLogDerivIntegrandAtCenter_verticalLine_eq
      q A hu hm
  rw [← hinfinite]
  simp only [
    localizedZeroResidueSumAtCenter,
    localizedContourRemainderAtCenter,
    localizedOtherEdgeContributionAtCenter,
    localizedRightEdgeTailAtCenter]
  rw [hfinite]
  ring

/-- The centered integrand recovers the original integrand at `q = 16`. -/
@[simp] theorem localizedRegularizedLogDerivIntegrandAtCenter_sixteen
    (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    localizedRegularizedLogDerivIntegrandAtCenter 16 A w m =
      localizedRegularizedLogDerivIntegrand A w m := by
  rfl

/-- The centered zero sum recovers the original zero sum at `q = 16`. -/
@[simp] theorem localizedZeroResidueSumAtCenter_sixteen
    (A : ℂ[X]) (w : ℂ) (m : ℝ) (zeros : Finset ℂ) :
    localizedZeroResidueSumAtCenter 16 A w m zeros =
      localizedZeroResidueSum A w m zeros := by
  rfl

/-- The centered non-right edge contribution recovers the original one at
`q = 16`. -/
@[simp] theorem localizedOtherEdgeContributionAtCenter_sixteen
    (A : ℂ[X]) (w : ℂ) (m u T : ℝ) :
    localizedOtherEdgeContributionAtCenter 16 A w m u T =
      localizedOtherEdgeContribution A w m u T := by
  rfl

/-- The centered right-edge tail recovers the original one at `q = 16`. -/
@[simp] theorem localizedRightEdgeTailAtCenter_sixteen
    (A : ℂ[X]) (w : ℂ) (m u T : ℝ) :
    localizedRightEdgeTailAtCenter 16 A w m u T =
      localizedRightEdgeTail A w m u T := by
  rfl

/-- The centered contour remainder recovers the original one at `q = 16`. -/
@[simp] theorem localizedContourRemainderAtCenter_sixteen
    (A : ℂ[X]) (w : ℂ) (m u T : ℝ) :
    localizedContourRemainderAtCenter 16 A w m u T =
      localizedContourRemainder A w m u T := by
  rfl

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
