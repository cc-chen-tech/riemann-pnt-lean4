import PrimeNumberTheorem.CentralHorizontalEdge
import PrimeNumberTheorem.FirstOrderExplicitFormula
import PrimeNumberTheorem.LeftHorizontalEdge
import PrimeNumberTheorem.NontrivialZeroMultiplicity

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

/-- On a good horizontal height, the first-order explicit-formula integrand is
interval integrable on every finite real interval. -/
theorem intervalIntegrable_explicitFormulaIntegrand_goodHeight_horizontal
    {x T t a b : ℝ} (hx : 0 < x) (hT : 0 < T) (ht : |t| = T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    IntervalIntegrable
      (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro σ _hσ
  have htne : t ≠ 0 := by
    intro h
    subst t
    simp at ht
    linarith
  have hzeta := riemannZeta_ne_zero_on_goodHeight_horizontal
    (T := T) (t := t) (σ := σ) hT ht hgood
  have hs0 : (σ : ℂ) + I * t ≠ 0 := by
    intro hs
    apply htne
    have him := congrArg Complex.im hs
    simpa using him
  have hs1 : (σ : ℂ) + I * t ≠ 1 := by
    intro hs
    apply htne
    have him := congrArg Complex.im hs
    simpa using him
  have han : ContinuousAt (explicitFormulaIntegrand x) ((σ : ℂ) + I * t) :=
    (analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
      hx hs0 hs1 hzeta).continuousAt
  have hmap : ContinuousAt (fun r : ℝ => ((r : ℂ) + I * t)) σ := by
    fun_prop
  change ContinuousWithinAt
    (explicitFormulaIntegrand x ∘ fun r : ℝ => ((r : ℂ) + I * t)) _ σ
  exact (ContinuousAt.comp
    (f := fun r : ℝ => ((r : ℂ) + I * t))
    (x := σ) (g := explicitFormulaIntegrand x) han hmap).continuousWithinAt

/-- A single cofinal family closes the moving-rectangle assembly gap.  Along
strictly increasing good heights, the complete first-order contour remainder
vanishes and the multiplicity-weighted nontrivial-zero sums converge to the
classical `psi0` explicit-formula value. -/
theorem exists_cofinal_nontrivialZeroSum_tendsto
    {x : ℝ} (hx : 1 < x) :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧
      (∀ n : ℕ,
        T n ∈ Set.Icc (2 * (n : ℝ) + 4) (2 * (n : ℝ) + 5) ∧
          0 < T n ∧ ExplicitFormulaAux.goodHeight (T n)) ∧
      (∀ n,
        (∫ w : ℝ in (-(T n / (2 * Real.pi)))..(T n / (2 * Real.pi)),
            explicitFormulaIntegrand x ((2 : ℂ) + 2 * Real.pi * w * I)) =
          (∑ p ∈ finiteTrivialZeroSum (2 * ((2 * n : ℕ) : ℝ)),
              -((x : ℂ) ^ p) / p) +
            ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
              ∑ ρ ∈ nontrivialZerosFinset (T n),
                -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
              firstOrderContourRemainder x
                (-(2 * ((2 * n : ℕ) : ℝ) + 1)) 2
                (T n / (2 * Real.pi))) ∧
      Tendsto
        (fun n : ℕ => firstOrderContourRemainder x
          (-(2 * ((2 * n : ℕ) : ℝ) + 1)) 2
          (T n / (2 * Real.pi)))
        atTop (nhds 0) ∧
      Tendsto
        (fun n : ℕ =>
          ∑ ρ ∈ nontrivialZerosFinset (T n),
            -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ)
        atTop
        (nhds ((chebyshevPsi0 x : ℂ) -
          (((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)) -
          ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0))) := by
  classical
  rcases exists_tendsto_horizontal_central_explicitFormulaIntegrand_both_zero
      (show 1 ≤ x from hx.le) with
    ⟨T0, hT0spec, hT0top, hcentralTop0, hcentralBottom0⟩
  let e : ℕ → ℕ := fun n => 2 * n
  have hetop : Tendsto e atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    dsimp [e]
    omega
  let T : ℕ → ℝ := fun n => T0 (e n)
  have hTspec (n : ℕ) :
      T n ∈ Set.Icc (((e n : ℕ) : ℝ) + 4) (((e n : ℕ) : ℝ) + 5) ∧
        ExplicitFormulaAux.goodHeight (T n) := by
    exact ⟨(hT0spec (e n)).1, (hT0spec (e n)).2.1⟩
  have hTmono : StrictMono T := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hu := (hTspec n).1.2
    have hl := (hTspec (n + 1)).1.1
    dsimp [e] at hu hl
    norm_num [Nat.cast_add, Nat.cast_mul] at hu hl ⊢
    linarith
  have hTtop : Tendsto T atTop atTop := hT0top.comp hetop
  have hTpos (n : ℕ) : 0 < T n := by
    linarith [(hTspec n).1.1]
  have hcentralTop : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in (-1)..2,
        explicitFormulaIntegrand x ((σ : ℂ) + I * T n))
      atTop (nhds 0) := by
    simpa [T] using hcentralTop0.comp hetop
  have hcentralBottom : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in (-1)..2,
        explicitFormulaIntegrand x ((σ : ℂ) - I * T n))
      atTop (nhds 0) := by
    simpa [T] using hcentralBottom0.comp hetop
  let A : ℕ → ℝ := fun n => -(2 * ((e n : ℕ) : ℝ) + 1)
  let a : ℝ → ℝ := fun t => A (Function.invFun T t)
  have ha_eval (n : ℕ) : a (T n) = A n := by
    dsimp [a]
    rw [Function.leftInverse_invFun hTmono.injective]
  have ha : ∀ᶠ t : ℝ in atTop, a t ≤ -1 := by
    filter_upwards [] with t
    dsimp [a, A, e]
    have hn : 0 ≤ ((2 * Function.invFun T t : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hfarTop0 := tendsto_integral_farLeft_explicit_atTop
    (x := x) (ε := 1) hx one_pos a ha
  have hfarBottom0 := tendsto_integral_farLeft_explicit_neg_height_atTop
    (x := x) (ε := 1) hx one_pos a ha
  have hfarTop : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in A n..(-1),
        explicitFormulaIntegrand x ((σ : ℂ) + I * T n))
      atTop (nhds 0) := by
    apply (hfarTop0.comp hTtop).congr'
    filter_upwards [] with n
    simp only [Function.comp_apply]
    rw [ha_eval]
    apply intervalIntegral.integral_congr
    intro σ _hσ
    rw [mul_comm (T n : ℂ) I]
  have hfarBottom : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in A n..(-1),
        explicitFormulaIntegrand x ((σ : ℂ) - I * T n))
      atTop (nhds 0) := by
    apply (hfarBottom0.comp hTtop).congr'
    filter_upwards [] with n
    simp only [Function.comp_apply]
    rw [ha_eval]
    apply intervalIntegral.integral_congr
    intro σ _hσ
    rw [mul_comm (T n : ℂ) I]
  have hhorizontalTop : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in A n..2,
        explicitFormulaIntegrand x ((σ : ℂ) + I * T n))
      atTop (nhds 0) := by
    simpa only [add_zero] using (hfarTop.add hcentralTop).congr' (by
      filter_upwards [] with n
      have hfarInt :=
        intervalIntegrable_explicitFormulaIntegrand_goodHeight_horizontal
          (x := x) (T := T n) (t := T n) (a := A n) (b := -1)
          (zero_lt_one.trans hx) (hTpos n) (abs_of_pos (hTpos n)) (hTspec n).2
      have hcentralInt :=
        intervalIntegrable_explicitFormulaIntegrand_goodHeight_horizontal
          (x := x) (T := T n) (t := T n) (a := -1) (b := 2)
          (zero_lt_one.trans hx) (hTpos n) (abs_of_pos (hTpos n)) (hTspec n).2
      exact intervalIntegral.integral_add_adjacent_intervals hfarInt hcentralInt)
  have hhorizontalBottom : Tendsto
      (fun n : ℕ => ∫ σ : ℝ in A n..2,
        explicitFormulaIntegrand x ((σ : ℂ) - I * T n))
      atTop (nhds 0) := by
    simpa only [add_zero] using (hfarBottom.add hcentralBottom).congr' (by
      filter_upwards [] with n
      have ht_abs : |-T n| = T n := by rw [abs_neg, abs_of_pos (hTpos n)]
      have hfarInt :=
        intervalIntegrable_explicitFormulaIntegrand_goodHeight_horizontal
          (x := x) (T := T n) (t := -T n) (a := A n) (b := -1)
          (zero_lt_one.trans hx) (hTpos n) ht_abs (hTspec n).2
      have hcentralInt :=
        intervalIntegrable_explicitFormulaIntegrand_goodHeight_horizontal
          (x := x) (T := T n) (t := -T n) (a := -1) (b := 2)
          (zero_lt_one.trans hx) (hTpos n) ht_abs (hTspec n).2
      simpa [sub_eq_add_neg] using
        intervalIntegral.integral_add_adjacent_intervals hfarInt hcentralInt)
  have hT0nonneg (m : ℕ) : 0 ≤ T0 m := by
    linarith [(hT0spec m).1.1]
  have hT0upper (m : ℕ) : T0 m ≤ (m : ℝ) + 4 + 1 := by
    linarith [(hT0spec m).1.2]
  have hleft0 := tendsto_integral_explicitFormulaIntegrand_odd_vertical_atTop
    (x := x) (K := 4) (T := T0) hx hT0nonneg hT0upper
  have hleft : Tendsto
      (fun n : ℕ => ∫ t : ℝ in (-(T n))..(T n),
        explicitFormulaIntegrand x ((A n : ℂ) + (t : ℂ) * I))
      atTop (nhds 0) := by
    apply (hleft0.comp hetop).congr'
    filter_upwards [] with n
    simp only [Function.comp_apply]
    dsimp [T, A, e]
  have hnum := (hhorizontalBottom.sub hhorizontalTop).sub (hleft.const_mul I)
  have hden : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hremainder : Tendsto
      (fun n : ℕ => firstOrderContourRemainder x (A n) 2
        (T n / (2 * Real.pi)))
      atTop (nhds 0) := by
    have hdiv := hnum.div_const (2 * Real.pi * I)
    simpa only [sub_zero, mul_zero, zero_div] using hdiv.congr' (by
      filter_upwards [] with n
      have hscale : 2 * Real.pi * (T n / (2 * Real.pi)) = T n := by
        field_simp
      simp only [firstOrderContourRemainder, hscale]
      have hbottomEq :
          (∫ σ : ℝ in A n..2,
              explicitFormulaIntegrand x ((σ : ℂ) - I * T n)) =
            ∫ σ : ℝ in A n..2,
              explicitFormulaIntegrand x
                ((σ : ℂ) + (((-T n : ℝ) : ℂ) * I)) := by
        apply intervalIntegral.integral_congr
        intro σ _hσ
        apply congrArg (explicitFormulaIntegrand x)
        push_cast
        ring
      have htopEq :
          (∫ σ : ℝ in A n..2,
              explicitFormulaIntegrand x ((σ : ℂ) + I * T n)) =
            ∫ σ : ℝ in A n..2,
              explicitFormulaIntegrand x
                ((σ : ℂ) + (((T n : ℝ) : ℂ) * I)) := by
        apply intervalIntegral.integral_congr
        intro σ _hσ
        apply congrArg (explicitFormulaIntegrand x)
        ring
      rw [hbottomEq, htopEq])
  have hWpos (n : ℕ) : 0 < T n / (2 * Real.pi) :=
    div_pos (hTpos n) (by positivity)
  have hformula (n : ℕ) :=
    movingLeft_scaledRightIntegral_eq_truncatedExplicitFormula
      (x := x) (c := 2) (W := T n / (2 * Real.pi)) (2 * n)
      (zero_lt_one.trans hx) (by norm_num) (hWpos n) (by
        have hscale : 2 * Real.pi * (T n / (2 * Real.pi)) = T n := by
          field_simp
        simpa [hscale] using (hTspec n).2)
  have hformula' (n : ℕ) :
      (∫ w : ℝ in (-(T n / (2 * Real.pi)))..(T n / (2 * Real.pi)),
          explicitFormulaIntegrand x ((2 : ℂ) + 2 * Real.pi * w * I)) =
        (∑ p ∈ finiteTrivialZeroSum (2 * ((2 * n : ℕ) : ℝ)),
            -((x : ℂ) ^ p) / p) +
          ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
            ∑ ρ ∈ nontrivialZerosFinset (T n),
              -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
            firstOrderContourRemainder x (A n) 2
              (T n / (2 * Real.pi)) := by
    have hscale : 2 * Real.pi * (T n / (2 * Real.pi)) = T n := by
      field_simp
    simpa [A, e, hscale] using hformula n
  have hWtop : Tendsto (fun n => T n / (2 * Real.pi)) atTop atTop :=
    hTtop.atTop_div_const (by positivity)
  have hright :=
    (tendsto_scaledRightIntegral_explicitFormulaIntegrand_atTop
      (x := x) (c := 2) (zero_lt_one.trans hx) (by norm_num)).comp hWtop
  have htrivial0 := ExplicitFormulaAux.tendsto_finiteTrivialZeroSum_residues hx
  have htrivial := htrivial0.comp hetop
  let mainTerm : ℂ := (x : ℂ) - deriv riemannZeta 0 / riemannZeta 0
  have hzeroSum := ((hright.sub htrivial).sub
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => mainTerm) atTop (nhds mainTerm))).add
      hremainder
  refine ⟨T, hTmono, hTtop, (fun n => ?_), ?_, ?_, ?_⟩
  · have hIcc : T n ∈ Set.Icc (2 * (n : ℝ) + 4) (2 * (n : ℝ) + 5) := by
      simpa [e, Nat.cast_mul] using (hTspec n).1
    exact ⟨hIcc, hTpos n, (hTspec n).2⟩
  · intro n
    simpa [A, e] using hformula' n
  · simpa [A, e] using hremainder
  · simpa only [sub_eq_add_neg, add_zero] using hzeroSum.congr' (by
      filter_upwards [] with n
      have heq := hformula' n
      dsimp [mainTerm]
      linear_combination heq)

/-- The complete cofinal contour theorem, expressed directly through the
multiplicity-aware approximation used by the final explicit-formula target.

This is deliberately a sequential cofinal result.  It does not claim the
full real-height `atTop` limit; that still requires control of the weighted
zero contributions between consecutive selected heights. -/
theorem exists_cofinal_explicitFormulaApproxWithMultiplicity_tendsto
    {x : ℝ} (hx : 1 < x) :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧
      (∀ n : ℕ,
        T n ∈ Set.Icc (2 * (n : ℝ) + 4) (2 * (n : ℝ) + 5) ∧
          ExplicitFormulaAux.goodHeight (T n)) ∧
      Tendsto
        (fun n : ℕ => explicitFormulaApproxWithMultiplicity x (T n))
        atTop (nhds (chebyshevPsi0 x : ℂ)) := by
  rcases exists_cofinal_nontrivialZeroSum_tendsto hx with
    ⟨T, hTmono, hTtop, hTspec, _hformula, _hremainder, hzeroSum⟩
  refine ⟨T, hTmono, hTtop, (fun n => ⟨(hTspec n).1, (hTspec n).2.2⟩), ?_⟩
  let mainTerm : ℂ := (x : ℂ) - deriv riemannZeta 0 / riemannZeta 0
  let trivialTerm : ℂ :=
    (((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))
  have hsum := ((tendsto_const_nhds : Tendsto
      (fun _n : ℕ => mainTerm) atTop (nhds mainTerm)).add hzeroSum).add
    (tendsto_const_nhds : Tendsto
      (fun _n : ℕ => trivialTerm) atTop (nhds trivialTerm))
  have hlim :
      mainTerm +
          ((chebyshevPsi0 x : ℂ) -
            (((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)) -
            ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0)) +
        trivialTerm = (chebyshevPsi0 x : ℂ) := by
    dsimp [mainTerm, trivialTerm]
    ring
  rw [hlim] at hsum
  apply hsum.congr'
  filter_upwards [] with n
  dsimp [mainTerm, trivialTerm, explicitFormulaApproxWithMultiplicity,
    finiteNontrivialZeroSumWithMultiplicity]
  push_cast
  have hneg :
      (∑ ρ ∈ nontrivialZerosFinset (T n),
          -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) =
        -(∑ ρ ∈ nontrivialZerosFinset (T n),
          (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ρ _hρ
    ring
  rw [hneg]
  ring

end ExplicitFormulaResidues
end PrimeNumberTheorem
