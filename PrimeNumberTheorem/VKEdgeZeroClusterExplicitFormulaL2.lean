import PrimeNumberTheorem.VKEdgeZeroClusterLocalL2
import PrimeNumberTheorem.ZeroForcedOscillationExplicitFormula

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Finite zero clusters in the actual explicit formula

This module inserts an arbitrary finite subcluster of the actual
multiplicity-weighted height truncation into the standard Chebyshev-`psi`
explicit formula.  The complement, truncation error, closed terms, and
midpoint jump correction remain in one concrete remainder.
-/

/-- Contribution from all height-`T` nontrivial zeros outside `S`. -/
noncomputable def finiteZeroClusterComplementContribution
    (S : Finset ℂ) (x T : ℝ) : ℂ :=
  ∑ rho ∈ nontrivialZerosFinset T \ S,
    (analyticOrderNatAt riemannZeta rho : ℂ) * (x : ℂ) ^ rho / rho

/-- The actual finite-height remainder after selecting `S`, written for the
standard right-continuous Chebyshev function rather than the midpoint
convention. -/
noncomputable def finiteZeroClusterPsiExplicitFormulaRemainder
    (S : Finset ℂ) (y T : ℝ) : ℂ :=
  finiteZeroClusterComplementContribution S (Real.exp y) T +
    (explicitFormulaApproxWithMultiplicity (Real.exp y) T -
      (chebyshevPsi0 (Real.exp y) : ℂ)) +
    ZeroForcedOscillation.zeroPackageClosedTerms y -
    ((jumpVonMangoldt (Real.exp y) / 2 : ℝ) : ℂ)

/-- Standard Chebyshev error normalized at the real exponent `beta`. -/
noncomputable def normalizedChebyshevPsiErrorAtExponent
    (beta y : ℝ) : ℂ :=
  (Real.exp (-beta * y) : ℂ) *
    (((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ))

/-- The actual selected-cluster remainder with the same normalization. -/
noncomputable def normalizedFiniteZeroClusterPsiRemainder
    (S : Finset ℂ) (T beta y : ℝ) : ℂ :=
  (Real.exp (-beta * y) : ℂ) *
    finiteZeroClusterPsiExplicitFormulaRemainder S y T

/-- Local second moment of the standard normalized Chebyshev error. -/
noncomputable def normalizedChebyshevPsiErrorSecondMoment
    (beta a L : ℝ) : ℝ :=
  ∫ y in a..(a + L),
    ‖normalizedChebyshevPsiErrorAtExponent beta y‖ ^ 2

/-- Local second moment of the actual finite-cluster explicit-formula
remainder. -/
noncomputable def normalizedFiniteZeroClusterPsiRemainderSecondMoment
    (S : Finset ℂ) (T beta a L : ℝ) : ℝ :=
  ∫ y in a..(a + L),
    ‖normalizedFiniteZeroClusterPsiRemainder S T beta y‖ ^ 2

/-- The complete height truncation is the selected subcluster plus its actual
finset complement. -/
theorem finiteNontrivialZeroSumWithMultiplicity_eq_cluster_add_complement
    {S : Finset ℂ} {x T : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T) :
    finiteNontrivialZeroSumWithMultiplicity x T =
      (∑ rho ∈ S,
        (analyticOrderNatAt riemannZeta rho : ℂ) * (x : ℂ) ^ rho / rho) +
      finiteZeroClusterComplementContribution S x T := by
  classical
  let f : ℂ → ℂ := fun rho =>
    (analyticOrderNatAt riemannZeta rho : ℂ) * (x : ℂ) ^ rho / rho
  have hsplit :
      (∑ rho ∈ nontrivialZerosFinset T \ S, f rho) +
          ∑ rho ∈ S, f rho =
        ∑ rho ∈ nontrivialZerosFinset T, f rho :=
    Finset.sum_sdiff hS
  unfold finiteNontrivialZeroSumWithMultiplicity
  dsimp [finiteZeroClusterComplementContribution, f] at hsplit ⊢
  rw [← hsplit]
  ring

/-- Exact standard-`psi` decomposition before normalization. -/
theorem chebyshevPsi_sub_exp_eq_neg_cluster_sub_remainder
    {S : Finset ℂ} {T y : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T) :
    (((chebyshevPsi (Real.exp y) - Real.exp y : ℝ) : ℂ)) =
      -(∑ rho ∈ S,
          (analyticOrderNatAt riemannZeta rho : ℂ) *
            (Real.exp y : ℂ) ^ rho / rho) -
        finiteZeroClusterPsiExplicitFormulaRemainder S y T := by
  have hsplit :=
    finiteNontrivialZeroSumWithMultiplicity_eq_cluster_add_complement
      (S := S) (x := Real.exp y) (T := T) hS
  have happ :
      explicitFormulaApproxWithMultiplicity (Real.exp y) T =
        (Real.exp y : ℂ) -
          finiteNontrivialZeroSumWithMultiplicity (Real.exp y) T -
          ZeroForcedOscillation.zeroPackageClosedTerms y := by
    dsimp [explicitFormulaApproxWithMultiplicity,
      ZeroForcedOscillation.zeroPackageClosedTerms]
    ring
  have hmidpoint :
      chebyshevPsi0 (Real.exp y) =
        chebyshevPsi (Real.exp y) -
          jumpVonMangoldt (Real.exp y) / 2 := rfl
  rw [finiteZeroClusterPsiExplicitFormulaRemainder, happ, hsplit,
    hmidpoint]
  push_cast
  ring

/-- Exact normalized decomposition into the selected actual zero cluster and
the actual standard-`psi` remainder. -/
theorem normalizedChebyshevPsiErrorAtExponent_eq_neg_cluster_sub_remainder
    {S : Finset ℂ} {T beta y : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T) :
    normalizedChebyshevPsiErrorAtExponent beta y =
      -normalizedFiniteZeroClusterContribution S
          (analyticOrderNatAt riemannZeta) beta y -
        normalizedFiniteZeroClusterPsiRemainder S T beta y := by
  rw [normalizedChebyshevPsiErrorAtExponent,
    normalizedFiniteZeroClusterContribution,
    normalizedFiniteZeroClusterPsiRemainder,
    chebyshevPsi_sub_exp_eq_neg_cluster_sub_remainder hS]
  ring

private theorem measurable_normalizedChebyshevPsiErrorAtExponent
    (beta : ℝ) :
    Measurable (normalizedChebyshevPsiErrorAtExponent beta) := by
  have hpsi : Measurable chebyshevPsi := by
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  unfold normalizedChebyshevPsiErrorAtExponent
  fun_prop

private theorem normalizedChebyshevPsiErrorAtExponent_norm_le
    (beta y : ℝ) :
    ‖normalizedChebyshevPsiErrorAtExponent beta y‖ ≤
      (Real.log 4 + 5) * Real.exp ((1 - beta) * y) := by
  have hpsi :
      chebyshevPsi (Real.exp y) ≤
        (Real.log 4 + 4) * Real.exp y := by
    rw [chebyshevPsi_eq_mathlib]
    exact Chebyshev.psi_le_const_mul_self (Real.exp_pos y).le
  have hpsiNonneg : 0 ≤ chebyshevPsi (Real.exp y) := by
    unfold chebyshevPsi
    exact Finset.sum_nonneg fun n _ => by
      rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hraw :
      |chebyshevPsi (Real.exp y) - Real.exp y| ≤
        (Real.log 4 + 5) * Real.exp y := by
    rw [abs_sub_le_iff]
    constructor
    · nlinarith [Real.exp_pos y]
    · nlinarith [Real.exp_pos y,
        Real.log_pos (by norm_num : 1 < (4 : ℝ))]
  unfold normalizedChebyshevPsiErrorAtExponent
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_real, Real.norm_eq_abs]
  calc
    Real.exp (-beta * y) *
          |chebyshevPsi (Real.exp y) - Real.exp y| ≤
        Real.exp (-beta * y) *
          ((Real.log 4 + 5) * Real.exp y) :=
      mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le
    _ = (Real.log 4 + 5) * Real.exp ((1 - beta) * y) := by
      rw [show
          Real.exp (-beta * y) *
                ((Real.log 4 + 5) * Real.exp y) =
              (Real.log 4 + 5) *
                (Real.exp (-beta * y) * Real.exp y) by ring,
        ← Real.exp_add]
      congr 1
      ring

private theorem
    intervalIntegrable_normSq_normalizedChebyshevPsiErrorAtExponent
    (beta a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable
      (fun y => ‖normalizedChebyshevPsiErrorAtExponent beta y‖ ^ 2)
      volume a b := by
  let R : ℝ := |a| + |b|
  let B : ℝ :=
    ((Real.log 4 + 5) *
      Real.exp (|1 - beta| * R)) ^ 2
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
  · exact
      ((measurable_normalizedChebyshevPsiErrorAtExponent beta).norm.pow_const 2
        |>.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hmin :
        -R ≤ a := by
      dsimp [R]
      linarith [neg_abs_le a, abs_nonneg b]
    have hmax :
        b ≤ R := by
      dsimp [R]
      linarith [le_abs_self b, abs_nonneg a]
    have hyabs : |y| ≤ R := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    have hexponent :
        (1 - beta) * y ≤ |1 - beta| * R := by
      calc
        (1 - beta) * y ≤ |(1 - beta) * y| := le_abs_self _
        _ = |1 - beta| * |y| := abs_mul _ _
        _ ≤ |1 - beta| * R :=
          mul_le_mul_of_nonneg_left hyabs (abs_nonneg _)
    have hexp :
        Real.exp ((1 - beta) * y) ≤
          Real.exp (|1 - beta| * R) :=
      Real.exp_le_exp.mpr hexponent
    have hcoef : 0 ≤ Real.log 4 + 5 := by positivity
    have hnorm :=
      (normalizedChebyshevPsiErrorAtExponent_norm_le beta y).trans
        (mul_le_mul_of_nonneg_left hexp hcoef)
    have hsq :
        ‖normalizedChebyshevPsiErrorAtExponent beta y‖ ^ 2 ≤ B := by
      dsimp [B]
      nlinarith [norm_nonneg
        (normalizedChebyshevPsiErrorAtExponent beta y)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq

private theorem
    continuous_normalizedFiniteZeroClusterContribution
    (S : Finset ℂ) (multiplicity : ℂ → ℕ) (beta : ℝ) :
    Continuous
      (normalizedFiniteZeroClusterContribution S multiplicity beta) := by
  rw [show
      normalizedFiniteZeroClusterContribution S multiplicity beta =
        fun y =>
          MathlibAux.driftingExponentialPolynomial S
            (finiteZeroClusterCoefficientAt multiplicity beta 0)
            Complex.im (fun rho => rho.re - beta) 0 y by
    funext y
    exact
      normalizedFiniteZeroClusterContribution_eq_drifting
        S multiplicity beta 0 y]
  unfold MathlibAux.driftingExponentialPolynomial
  fun_prop

private theorem
    intervalIntegrable_normSq_normalizedFiniteZeroClusterContribution
    (S : Finset ℂ) (multiplicity : ℂ → ℕ)
    (beta a b : ℝ) :
    IntervalIntegrable
      (fun y =>
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta y‖ ^ 2)
      volume a b := by
  exact
    ((continuous_normalizedFiniteZeroClusterContribution
        S multiplicity beta).norm.pow 2).intervalIntegrable a b

private theorem
    intervalIntegrable_normSq_normalizedFiniteZeroClusterPsiRemainder
    {S : Finset ℂ} {T beta a b : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hab : a ≤ b) :
    IntervalIntegrable
      (fun y =>
        ‖normalizedFiniteZeroClusterPsiRemainder S T beta y‖ ^ 2)
      volume a b := by
  let E : ℝ → ℂ := normalizedChebyshevPsiErrorAtExponent beta
  let P : ℝ → ℂ :=
    normalizedFiniteZeroClusterContribution S
      (analyticOrderNatAt riemannZeta) beta
  have hE :
      IntervalIntegrable (fun y => ‖E y‖ ^ 2) volume a b := by
    simpa [E] using
      intervalIntegrable_normSq_normalizedChebyshevPsiErrorAtExponent
        beta a b hab
  have hP :
      IntervalIntegrable (fun y => ‖P y‖ ^ 2) volume a b := by
    simpa [P] using
      intervalIntegrable_normSq_normalizedFiniteZeroClusterContribution
        S (analyticOrderNatAt riemannZeta) beta a b
  have hmajor :
      IntervalIntegrable
        (fun y => 2 * ‖E y‖ ^ 2 + 2 * ‖P y‖ ^ 2)
        volume a b :=
    (hE.const_mul 2).add (hP.const_mul 2)
  have hmeas :
      AEStronglyMeasurable
        (fun y =>
          ‖normalizedFiniteZeroClusterPsiRemainder S T beta y‖ ^ 2)
        (volume.restrict (Ι a b)) := by
    have hEmeas :
        Measurable E := by
      simpa [E] using
        measurable_normalizedChebyshevPsiErrorAtExponent beta
    have hPmeas :
        Measurable P :=
      (continuous_normalizedFiniteZeroClusterContribution
        S (analyticOrderNatAt riemannZeta) beta).measurable
    have heq :
        (fun y =>
          ‖normalizedFiniteZeroClusterPsiRemainder S T beta y‖ ^ 2) =
        fun y => ‖-E y - P y‖ ^ 2 := by
      funext y
      have hdecomp :=
        normalizedChebyshevPsiErrorAtExponent_eq_neg_cluster_sub_remainder
          (S := S) (T := T) (beta := beta) (y := y) hS
      congr 1
      dsimp [E, P] at hdecomp ⊢
      rw [hdecomp]
      ring
    rw [heq]
    exact
      ((hEmeas.neg.sub hPmeas).norm.pow_const 2
        |>.aestronglyMeasurable).restrict
  apply hmajor.mono_fun' hmeas
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
  have hdecomp :=
    normalizedChebyshevPsiErrorAtExponent_eq_neg_cluster_sub_remainder
      (S := S) (T := T) (beta := beta) (y := y) hS
  have hrem :
      normalizedFiniteZeroClusterPsiRemainder S T beta y =
        -E y - P y := by
    dsimp [E, P] at hdecomp ⊢
    rw [hdecomp]
    ring
  rw [hrem, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have htriangle : ‖-E y - P y‖ ≤ ‖E y‖ + ‖P y‖ := by
    calc
      ‖-E y - P y‖ ≤ ‖-E y‖ + ‖P y‖ := norm_sub_le _ _
      _ = ‖E y‖ + ‖P y‖ := by rw [norm_neg]
  have hsquare :
      ‖-E y - P y‖ ^ 2 ≤ (‖E y‖ + ‖P y‖) ^ 2 := by
    nlinarith [norm_nonneg (-E y - P y), norm_nonneg (E y),
      norm_nonneg (P y)]
  have hcross : 2 * ‖E y‖ * ‖P y‖ ≤ ‖E y‖ ^ 2 + ‖P y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖E y‖ - ‖P y‖)]
  nlinarith

/-- Reverse-triangle `L²` transfer from an actual selected zero cluster to
the standard Chebyshev error.  Every unselected zero and every finite-height
explicit-formula error remains charged to the concrete remainder moment. -/
theorem normalizedChebyshevPsiErrorSecondMoment_ge_cluster_sub_remainder
    {S : Finset ℂ} {T beta a L : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hL : 0 ≤ L) :
    (1 / 2 : ℝ) *
          (∫ y in a..(a + L),
            ‖normalizedFiniteZeroClusterContribution S
              (analyticOrderNatAt riemannZeta) beta y‖ ^ 2) -
        normalizedFiniteZeroClusterPsiRemainderSecondMoment
          S T beta a L ≤
      normalizedChebyshevPsiErrorSecondMoment beta a L := by
  let E : ℝ → ℂ := normalizedChebyshevPsiErrorAtExponent beta
  let P : ℝ → ℂ :=
    normalizedFiniteZeroClusterContribution S
      (analyticOrderNatAt riemannZeta) beta
  let R : ℝ → ℂ :=
    normalizedFiniteZeroClusterPsiRemainder S T beta
  have hab : a ≤ a + L := by linarith
  have hE :
      IntervalIntegrable (fun y => ‖E y‖ ^ 2) volume a (a + L) := by
    simpa [E] using
      intervalIntegrable_normSq_normalizedChebyshevPsiErrorAtExponent
        beta a (a + L) hab
  have hP :
      IntervalIntegrable (fun y => ‖P y‖ ^ 2) volume a (a + L) := by
    simpa [P] using
      intervalIntegrable_normSq_normalizedFiniteZeroClusterContribution
        S (analyticOrderNatAt riemannZeta) beta a (a + L)
  have hR :
      IntervalIntegrable (fun y => ‖R y‖ ^ 2) volume a (a + L) := by
    simpa [R] using
      intervalIntegrable_normSq_normalizedFiniteZeroClusterPsiRemainder
        (S := S) (T := T) (beta := beta) (a := a) (b := a + L)
          hS hab
  have hleft :
      IntervalIntegrable
        (fun y => (1 / 2 : ℝ) * ‖P y‖ ^ 2 - ‖R y‖ ^ 2)
        volume a (a + L) :=
    (hP.const_mul (1 / 2 : ℝ)).sub hR
  have hpoint :
      ∀ y ∈ Set.Icc a (a + L),
        (1 / 2 : ℝ) * ‖P y‖ ^ 2 - ‖R y‖ ^ 2 ≤ ‖E y‖ ^ 2 := by
    intro y hy
    have hdecomp :=
      normalizedChebyshevPsiErrorAtExponent_eq_neg_cluster_sub_remainder
        (S := S) (T := T) (beta := beta) (y := y) hS
    have htriangle : ‖P y‖ ≤ ‖E y‖ + ‖R y‖ := by
      calc
        ‖P y‖ = ‖(-E y) - R y‖ := by
          congr 1
          dsimp [E, P, R] at hdecomp ⊢
          rw [hdecomp]
          ring
        _ ≤ ‖-E y‖ + ‖R y‖ := norm_sub_le _ _
        _ = ‖E y‖ + ‖R y‖ := by rw [norm_neg]
    have hsquare :
        ‖P y‖ ^ 2 ≤ (‖E y‖ + ‖R y‖) ^ 2 := by
      nlinarith [norm_nonneg (P y), norm_nonneg (E y),
        norm_nonneg (R y)]
    have hcross : 2 * ‖E y‖ * ‖R y‖ ≤ ‖E y‖ ^ 2 + ‖R y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖E y‖ - ‖R y‖)]
    nlinarith
  have hmono :=
    intervalIntegral.integral_mono_on hab hleft hE hpoint
  rw [intervalIntegral.integral_sub (hP.const_mul (1 / 2 : ℝ)) hR,
    intervalIntegral.integral_const_mul] at hmono
  simpa [E, P, R, normalizedChebyshevPsiErrorSecondMoment,
    normalizedFiniteZeroClusterPsiRemainderSecondMoment] using hmono

/-- Actual finite-cluster local separation forces an ordinary Chebyshev
second-moment lower bound, with the complete complementary explicit-formula
remainder still visible as a subtraction term. -/
theorem
    normalizedChebyshevPsiErrorSecondMoment_ge_localSeparation_sub_remainder
    {S : Finset ℂ} {T beta a L delta : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta)
    (hsupport :
      (MathlibAux.mergedFrequencySupport S Complex.im).Nontrivial) :
    (1 / 4 : ℝ) *
          (L * finiteZeroClusterMergedEnergy S
              (analyticOrderNatAt riemannZeta) beta a -
            4 * Real.pi *
              finiteZeroClusterLocalSeparationEnergy S
                (analyticOrderNatAt riemannZeta) beta a) -
        (1 / 2 : ℝ) * L *
          (1 - Real.exp (-delta * L)) ^ 2 *
            finiteZeroClusterCoefficientMass S
              (analyticOrderNatAt riemannZeta) beta a ^ 2 -
        normalizedFiniteZeroClusterPsiRemainderSecondMoment
          S T beta a L ≤
      normalizedChebyshevPsiErrorSecondMoment beta a L := by
  have hcluster :=
    integral_normSq_normalizedFiniteZeroClusterContribution_ge_localSeparation
      (S := S)
      (multiplicity := analyticOrderNatAt riemannZeta)
      (beta := beta) (a := a) (L := L) (delta := delta)
      hL hdelta hband hsupport
  have htransfer :=
    normalizedChebyshevPsiErrorSecondMoment_ge_cluster_sub_remainder
      (S := S) (T := T) (beta := beta) (a := a) (L := L)
      hS hL
  linarith

/-- Positivity endpoint for the actual standard-`psi` moment.  The hypothesis
states exactly that the finite-cluster local-separation budget exceeds the
complete complementary explicit-formula remainder moment. -/
theorem
    normalizedChebyshevPsiErrorSecondMoment_pos_of_localSeparation_remainder
    {S : Finset ℂ} {T beta a L delta : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta)
    (hsupport :
      (MathlibAux.mergedFrequencySupport S Complex.im).Nontrivial)
    (hremainder :
      normalizedFiniteZeroClusterPsiRemainderSecondMoment S T beta a L <
        (1 / 4 : ℝ) *
            (L * finiteZeroClusterMergedEnergy S
                (analyticOrderNatAt riemannZeta) beta a -
              4 * Real.pi *
                finiteZeroClusterLocalSeparationEnergy S
                  (analyticOrderNatAt riemannZeta) beta a) -
          (1 / 2 : ℝ) * L *
            (1 - Real.exp (-delta * L)) ^ 2 *
              finiteZeroClusterCoefficientMass S
                (analyticOrderNatAt riemannZeta) beta a ^ 2) :
    0 < normalizedChebyshevPsiErrorSecondMoment beta a L := by
  have hbound :=
    normalizedChebyshevPsiErrorSecondMoment_ge_localSeparation_sub_remainder
      (S := S) (T := T) (beta := beta) (a := a) (L := L)
      (delta := delta) hS hL hdelta hband hsupport
  linarith

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
