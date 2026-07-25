import PrimeNumberTheorem.VKEdgePiOverTwoContourBounds
import PrimeNumberTheorem.VKEdgePiOverTwoRightMellin

open Complex Filter MeasureTheory Polynomial Set Topology
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
The infinite right-edge Mellin identity is unchanged when the geometric
vertical line is parametrized independently of the imaginary part of the
Gaussian center.

This translation is needed to match the right edge of the symmetric residue
rectangle with the `w + 2 + it` parametrization used by the Mellin transform.
-/
theorem integral_localizedRegularizedLogDerivIntegrand_verticalLine_eq
    (A : ℂ[X]) {u v m : ℝ} (hu : 0 < u) (hm : 0 < m) :
    (∫ t : ℝ,
        localizedRegularizedLogDerivIntegrand A
          ((u : ℂ) + I * v) m
          (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      ∫ x in Set.Ioi (1 : ℝ),
        psiErrorAboveOneComplex x *
          ((2 * Real.pi : ℂ) *
            ((x : ℂ) ^ (-(((u : ℂ) + I * v) + 1)) *
              (((u : ℂ) + I * v) *
                  polynomialGaussianKernel A m
                    (16 * m - Real.log x) +
                polynomialGaussianKernelDeriv A m
                  (16 * m - Real.log x)))) := by
  let w : ℂ := (u : ℂ) + I * v
  let f : ℝ → ℂ := fun t =>
    localizedRegularizedLogDerivIntegrand A w m
      (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hw : 0 < w.re := by
    simpa [w] using hu
  have hmellin :=
    integral_localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge_eq
      A hm hw
  calc
    (∫ t : ℝ,
        localizedRegularizedLogDerivIntegrand A
          ((u : ℂ) + I * v) m
          (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ, f t := by
      rfl
    _ = ∫ t : ℝ, f (t + v) :=
      (integral_add_right_eq_self f v).symm
    _ =
        ∫ t : ℝ,
          localizedGaussianWeight A w m
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
      simpa only [f, localizedRegularizedLogDerivIntegrand, hz]
    _ = _ := by
      simpa [w] using hmellin

/--
The concrete right-edge integrand remains absolutely integrable after
separating the geometric vertical line from the imaginary part of its
Gaussian center.
-/
theorem integrable_localizedRegularizedLogDerivIntegrand_verticalLine
    (A : ℂ[X]) {u v m : ℝ} (hu : 0 < u) (hm : 0 < m) :
    Integrable
      (fun t : ℝ =>
        localizedRegularizedLogDerivIntegrand A
          ((u : ℂ) + I * v) m
          (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  let w : ℂ := (u : ℂ) + I * v
  let g : ℝ → ℂ := fun t =>
    localizedGaussianWeight A w m
        (w + ((2 : ℂ) + I * (t : ℂ))) *
      (-logDeriv riemannZeta
          (w + ((2 : ℂ) + I * (t : ℂ))) -
        (w + ((2 : ℂ) + I * (t : ℂ))) /
          (w + ((2 : ℂ) + I * (t : ℂ)) - 1))
  have hw : 0 < w.re := by
    simpa [w] using hu
  have hg : Integrable g := by
    simpa [g] using
      integrable_localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge
        A hm hw
  have hshift : Integrable (g ∘ fun t : ℝ => t + (-v)) :=
    (measurePreserving_add_right volume (-v)).integrable_comp_of_integrable hg
  apply hshift.congr
  filter_upwards with t
  have hz :
      w + ((2 : ℂ) + I * (((t + (-v) : ℝ) : ℂ))) =
        (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    simp only [w, ofReal_add, ofReal_neg]
    push_cast
    ring
  simpa only [
    Function.comp_apply,
    g,
    w,
    localizedRegularizedLogDerivIntegrand,
    hz]

/-- The concrete Gaussian average of the cutoff Chebyshev error. -/
def localizedPsiGaussianAverage
    (A : ℂ[X]) (w : ℂ) (m : ℝ) : ℂ :=
  ∫ x in Set.Ioi (1 : ℝ),
    psiErrorAboveOneComplex x *
      ((2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (16 * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (16 * m - Real.log x))))

/-- The analytic-multiplicity weighted zero contribution in one rectangle. -/
def localizedZeroResidueSum
    (A : ℂ[X]) (w : ℂ) (m : ℝ) (zeros : Finset ℂ) : ℂ :=
  ∑ rho ∈ zeros,
    (analyticOrderNatAt riemannZeta rho : ℂ) *
      localizedGaussianWeight A w m rho

/-- The oriented contribution of the bottom, top, and left rectangle edges. -/
def localizedOtherEdgeContribution
    (A : ℂ[X]) (w : ℂ) (m u T : ℝ) : ℂ :=
  I *
      ((∫ σ : ℝ in (-1)..(u + 2),
          localizedRegularizedLogDerivIntegrand A w m
            ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)) -
        ∫ σ : ℝ in (-1)..(u + 2),
          localizedRegularizedLogDerivIntegrand A w m
            ((σ : ℂ) + (T : ℂ) * I)) +
    ∫ t : ℝ in (-T)..T,
      localizedRegularizedLogDerivIntegrand A w m
        ((-1 : ℂ) + (t : ℂ) * I)

/--
The difference between the infinite geometric right edge and its symmetric
finite-height truncation.
-/
def localizedRightEdgeTail
    (A : ℂ[X]) (w : ℂ) (m u T : ℝ) : ℂ :=
  (∫ t : ℝ,
      localizedRegularizedLogDerivIntegrand A w m
        (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) -
    ∫ t : ℝ in (-T)..T,
      localizedRegularizedLogDerivIntegrand A w m
        (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)

/-- The complete finite-height contour remainder after the zero sum. -/
def localizedContourRemainder
    (A : ℂ[X]) (w : ℂ) (m u T : ℝ) : ℂ :=
  localizedOtherEdgeContribution A w m u T +
    localizedRightEdgeTail A w m u T

/--
For fixed Gaussian scale and center, the symmetric right-edge truncation
tail vanishes as the contour height tends to infinity.
-/
theorem tendsto_localizedRightEdgeTail_atTop
    (A : ℂ[X]) {u v m : ℝ} (hu : 0 < u) (hm : 0 < m) :
    Tendsto
      (fun T : ℝ =>
        localizedRightEdgeTail A ((u : ℂ) + I * v) m u T)
      atTop (𝓝 0) := by
  let f : ℝ → ℂ := fun t =>
    localizedRegularizedLogDerivIntegrand A
      ((u : ℂ) + I * v) m
      (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)
  have hf : Integrable f := by
    simpa [f] using
      integrable_localizedRegularizedLogDerivIntegrand_verticalLine A hu hm
  have hfinite :
      Tendsto
        (fun T : ℝ => ∫ t : ℝ in (-T)..T, f t)
        atTop
        (𝓝 (∫ t : ℝ, f t)) :=
    intervalIntegral_tendsto_integral
      hf tendsto_neg_atTop_atBot tendsto_id
  have hconst :
      Tendsto
        (fun _ : ℝ => ∫ t : ℝ, f t)
        atTop
        (𝓝 (∫ t : ℝ, f t)) :=
    tendsto_const_nhds
  have hsub := hconst.sub hfinite
  simpa [localizedRightEdgeTail, f] using hsub

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

/--
The concrete Gaussian average of the Chebyshev error is exactly the
analytic-multiplicity weighted zero sum plus a named finite-height contour
remainder.

No asymptotic estimate is hidden here: the remainder is definitionally the
three non-right rectangle edges plus the discarded right-edge tails.
-/
theorem exists_localizedPsiGaussianAverage_eq_zeroSum_add_contourRemainder_of_goodHeight
    (A : ℂ[X]) {u v m T : ℝ}
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
      localizedPsiGaussianAverage A ((u : ℂ) + I * v) m =
        -(2 * Real.pi : ℂ) *
            localizedZeroResidueSum A ((u : ℂ) + I * v) m zeros +
          localizedContourRemainder A ((u : ℂ) + I * v) m u T := by
  rcases
      exists_rightEdgeIntegral_eq_zero_sum_add_other_edges_of_goodHeight
        A (u := u) (v := v) (m := m) (T := T) hu hT hgood with
    ⟨zeros, hzeros, hcomplete, hfinite⟩
  refine ⟨zeros, hzeros, hcomplete, ?_⟩
  have hinfinite :
      (∫ t : ℝ,
          localizedRegularizedLogDerivIntegrand A
            ((u : ℂ) + I * v) m
            (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        localizedPsiGaussianAverage A ((u : ℂ) + I * v) m := by
    simpa [localizedPsiGaussianAverage] using
      integral_localizedRegularizedLogDerivIntegrand_verticalLine_eq
        A hu hm
  rw [← hinfinite]
  simp only [
    localizedZeroResidueSum,
    localizedContourRemainder,
    localizedOtherEdgeContribution,
    localizedRightEdgeTail]
  rw [hfinite]
  ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
