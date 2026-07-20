import HardyTheorem.CriticalLineMultiplicity
import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZetaSymmetry
import PrimeNumberTheorem.RiemannVonMangoldt.ZeroCount
import PrimeNumberTheorem.ZeroDensityCount

open Complex Filter
open scoped BigOperators
open scoped ComplexConjugate

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

/-- Reflection across the critical line, preserving imaginary part. -/
def criticalLineReflection (rho : ℂ) : ℂ :=
  1 - conj rho

@[simp]
lemma criticalLineReflection_re (rho : ℂ) :
    (criticalLineReflection rho).re = 1 - rho.re := by
  simp [criticalLineReflection]

@[simp]
lemma criticalLineReflection_im (rho : ℂ) :
    (criticalLineReflection rho).im = rho.im := by
  simp [criticalLineReflection]

@[simp]
lemma criticalLineReflection_involutive (rho : ℂ) :
    criticalLineReflection (criticalLineReflection rho) = rho := by
  apply Complex.ext <;> simp

theorem isNontrivialZero_conj {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    RiemannHypothesis.IsNontrivialZero (conj rho) := by
  have hcompleted : RiemannHypothesis.completedZeta rho = 0 :=
    (completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
      hrho.2.1 hrho.2.2).2 hrho.1
  have hcompletedConj :
      RiemannHypothesis.completedZeta (conj rho) = 0 := by
    rw [completedZeta_conj, hcompleted, map_zero]
  refine ⟨?_, by simpa using hrho.2.1, by simpa using hrho.2.2⟩
  exact
    (completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
      (by simpa using hrho.2.1) (by simpa using hrho.2.2)).1 hcompletedConj

theorem isNontrivialZero_criticalLineReflection {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    RiemannHypothesis.IsNontrivialZero (criticalLineReflection rho) := by
  simpa [criticalLineReflection] using nontrivial_zero_symmetric' (isNontrivialZero_conj hrho)

private lemma iteratedDeriv_conj_conj (n : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv n (conj ∘ f ∘ conj) =
      conj ∘ iteratedDeriv n f ∘ conj := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega, iteratedDeriv_succ, ih,
        deriv_conj_conj, ← iteratedDeriv_succ]

private theorem analyticOrderAt_conj_eq
    (f : ℂ → ℂ) (s : ℂ)
    (hf : ∀ z : ℂ, AnalyticAt ℂ f z)
    (hsym : ∀ z : ℂ, f (conj z) = conj (f z)) :
    analyticOrderAt f (conj s) = analyticOrderAt f s := by
  have hreflected : conj ∘ f ∘ conj = f := by
    funext z
    have hz := congrArg conj (hsym z)
    simpa [Function.comp_def] using hz
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf (conj s)),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf s)]
  constructor
  · intro h i hi
    calc
      iteratedDeriv i f s =
          iteratedDeriv i (conj ∘ f ∘ conj) s := by
        rw [hreflected]
      _ = conj (iteratedDeriv i f (conj s)) := by
        rw [iteratedDeriv_conj_conj]
        rfl
      _ = 0 := by simp [h i hi]
  · intro h i hi
    calc
      iteratedDeriv i f (conj s) =
          iteratedDeriv i (conj ∘ f ∘ conj) (conj s) := by
        rw [hreflected]
      _ = conj (iteratedDeriv i f s) := by
        rw [iteratedDeriv_conj_conj]
        simp
      _ = 0 := by simp [h i hi]

theorem analyticOrderNatAt_riemannZeta_conj_of_nontrivialZero
    {rho : ℂ} (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta (conj rho) =
      analyticOrderNatAt riemannZeta rho := by
  have hcompletedOrder :
      analyticOrderAt RiemannHypothesis.completedZeta (conj rho) =
        analyticOrderAt RiemannHypothesis.completedZeta rho :=
    analyticOrderAt_conj_eq RiemannHypothesis.completedZeta rho
      (fun z => differentiable_completedZeta.analyticAt z) completedZeta_conj
  unfold analyticOrderNatAt
  rw [← analyticOrderAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip
      (by simpa using hrho.2.1) (by simpa using hrho.2.2),
    ← analyticOrderAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip
      hrho.2.1 hrho.2.2,
    hcompletedOrder]

theorem analyticOrderNatAt_riemannZeta_criticalLineReflection_of_nontrivialZero
    {rho : ℂ} (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta (criticalLineReflection rho) =
      analyticOrderNatAt riemannZeta rho := by
  calc
    analyticOrderNatAt riemannZeta (criticalLineReflection rho) =
        analyticOrderNatAt riemannZeta (conj rho) := by
      simpa [criticalLineReflection] using
        analyticOrderNatAt_riemannZeta_one_sub_of_nontrivialZero
          (isNontrivialZero_conj hrho)
    _ = analyticOrderNatAt riemannZeta rho :=
      analyticOrderNatAt_riemannZeta_conj_of_nontrivialZero hrho

/-- Positive-ordinate nontrivial zeros on the critical line. -/
noncomputable def positiveCriticalLineZerosFinset (T : ℝ) : Finset ℂ :=
  (positiveNontrivialZerosFinset T).filter fun rho => rho.re = 1 / 2

lemma mem_positiveCriticalLineZerosFinset {rho : ℂ} {T : ℝ} :
    rho ∈ positiveCriticalLineZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧ rho.im ≤ T ∧ rho.re = 1 / 2 := by
  simp [positiveCriticalLineZerosFinset, mem_positiveNontrivialZerosFinset,
    and_assoc]

/-- Strict-positive critical-line zero count, with analytic multiplicity. -/
noncomputable def positiveCriticalLineZeroMultiplicityCount (T : ℝ) : ℕ :=
  ∑ rho ∈ positiveCriticalLineZerosFinset T,
    analyticOrderNatAt riemannZeta rho

private noncomputable def positiveLeftHalfZerosFinset (T : ℝ) : Finset ℂ :=
  (positiveNontrivialZerosFinset T).filter fun rho => rho.re < 1 / 2

private lemma mem_positiveLeftHalfZerosFinset {rho : ℂ} {T : ℝ} :
    rho ∈ positiveLeftHalfZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧ rho.im ≤ T ∧ rho.re < 1 / 2 := by
  simp [positiveLeftHalfZerosFinset, mem_positiveNontrivialZerosFinset,
    and_assoc]

private noncomputable def positiveRightHalfZerosFinset (T : ℝ) : Finset ℂ :=
  (positiveNontrivialZerosFinset T).filter fun rho => 1 / 2 < rho.re

private lemma mem_positiveRightHalfZerosFinset {rho : ℂ} {T : ℝ} :
    rho ∈ positiveRightHalfZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧
        0 < rho.im ∧ rho.im ≤ T ∧ 1 / 2 < rho.re := by
  simp [positiveRightHalfZerosFinset, mem_positiveNontrivialZerosFinset,
    and_assoc]

private lemma positiveRightHalfZerosFinset_eq_zeroDensityZerosFinset (T : ℝ) :
    positiveRightHalfZerosFinset T =
      ZeroDensity.zeroDensityZerosFinset (1 / 2) T := by
  ext rho
  rw [mem_positiveRightHalfZerosFinset,
    ZeroDensity.mem_zeroDensityZerosFinset]

private theorem sum_positiveLeftHalf_eq_sum_positiveRightHalf (T : ℝ) :
    ∑ rho ∈ positiveLeftHalfZerosFinset T,
        analyticOrderNatAt riemannZeta rho =
      ∑ rho ∈ positiveRightHalfZerosFinset T,
        analyticOrderNatAt riemannZeta rho := by
  classical
  apply Finset.sum_bij (fun rho _ => criticalLineReflection rho)
  · intro rho hrho
    rw [mem_positiveRightHalfZerosFinset]
    rw [mem_positiveLeftHalfZerosFinset] at hrho
    exact ⟨isNontrivialZero_criticalLineReflection hrho.1,
      by simpa using hrho.2.1, by simpa using hrho.2.2.1, by
        rw [criticalLineReflection_re]
        linarith [hrho.2.2.2]⟩
  · intro rho _ sigma _ heq
    have := congrArg criticalLineReflection heq
    simpa using this
  · intro sigma hsigma
    refine ⟨criticalLineReflection sigma, ?_, ?_⟩
    · rw [mem_positiveLeftHalfZerosFinset]
      rw [mem_positiveRightHalfZerosFinset] at hsigma
      exact ⟨isNontrivialZero_criticalLineReflection hsigma.1,
        by simpa using hsigma.2.1, by simpa using hsigma.2.2.1, by
          rw [criticalLineReflection_re]
          linarith [hsigma.2.2.2]⟩
    · exact criticalLineReflection_involutive sigma
  · intro rho hrho
    exact
      (analyticOrderNatAt_riemannZeta_criticalLineReflection_of_nontrivialZero
        (mem_positiveLeftHalfZerosFinset.mp hrho).1).symm

private lemma positiveNontrivialZerosFinset_partition (T : ℝ) :
    (positiveCriticalLineZerosFinset T ∪ positiveLeftHalfZerosFinset T) ∪
        positiveRightHalfZerosFinset T =
      positiveNontrivialZerosFinset T := by
  classical
  ext rho
  constructor
  · simp only [Finset.mem_union]
    rintro ((hcritical | hleft) | hright)
    · exact (Finset.mem_filter.mp hcritical).1
    · exact (Finset.mem_filter.mp hleft).1
    · exact (Finset.mem_filter.mp hright).1
  · intro hrho
    rcases lt_trichotomy rho.re (1 / 2 : ℝ) with hleft | hcritical | hright
    · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inr
        (Finset.mem_filter.mpr ⟨hrho, hleft⟩)
    · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_union.mpr <| Or.inl
        (Finset.mem_filter.mpr ⟨hrho, hcritical⟩)
    · exact Finset.mem_union.mpr <| Or.inr
        (Finset.mem_filter.mpr ⟨hrho, hright⟩)

private lemma disjoint_positiveCriticalLine_positiveLeftHalf (T : ℝ) :
    Disjoint (positiveCriticalLineZerosFinset T)
      (positiveLeftHalfZerosFinset T) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro rho hcritical hleft
  have hcritical' := (mem_positiveCriticalLineZerosFinset.mp hcritical).2.2.2
  have hleft' := (mem_positiveLeftHalfZerosFinset.mp hleft).2.2.2
  linarith

private lemma disjoint_positiveCriticalLine_union_left_positiveRightHalf (T : ℝ) :
    Disjoint (positiveCriticalLineZerosFinset T ∪ positiveLeftHalfZerosFinset T)
      (positiveRightHalfZerosFinset T) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro rho hcriticalOrLeft hright
  rw [Finset.mem_union] at hcriticalOrLeft
  have hright' := (mem_positiveRightHalfZerosFinset.mp hright).2.2.2
  rcases hcriticalOrLeft with hcritical | hleft
  · have := (mem_positiveCriticalLineZerosFinset.mp hcritical).2.2.2
    linarith
  · have := (mem_positiveLeftHalfZerosFinset.mp hleft).2.2.2
    linarith

/-- Exact decomposition of positive-ordinate nontrivial zeros into critical-line
zeros and reflected pairs off the critical line. -/
theorem riemannZeroCount_eq_positiveCriticalLine_add_two_mul_zeroDensityCount
    (T : ℝ) :
    riemannZeroCount T =
      positiveCriticalLineZeroMultiplicityCount T +
        2 * ZeroDensity.zeroDensityCount (1 / 2) T := by
  classical
  have hleftRight := sum_positiveLeftHalf_eq_sum_positiveRightHalf T
  have hrightCount :
      ∑ rho ∈ positiveRightHalfZerosFinset T,
          analyticOrderNatAt riemannZeta rho =
        ZeroDensity.zeroDensityCount (1 / 2) T := by
    rw [positiveRightHalfZerosFinset_eq_zeroDensityZerosFinset]
    rfl
  unfold riemannZeroCount positiveCriticalLineZeroMultiplicityCount
  rw [← positiveNontrivialZerosFinset_partition T,
    Finset.sum_union
      (disjoint_positiveCriticalLine_union_left_positiveRightHalf T),
    Finset.sum_union (disjoint_positiveCriticalLine_positiveLeftHalf T),
    hleftRight, hrightCount]
  omega

private lemma criticalLineZerosFinset_eq_positive_of_half_ne_zero
    (T : ℝ) (hhalf : riemannZeta (1 / 2) ≠ 0) :
    HardyTheorem.criticalLineZerosFinset T =
      positiveCriticalLineZerosFinset T := by
  classical
  ext rho
  constructor
  · intro hrho
    rw [HardyTheorem.mem_criticalLineZerosFinset] at hrho
    rw [mem_positiveCriticalLineZerosFinset]
    refine ⟨hrho.1, ?_, hrho.2.2.2, hrho.2.1⟩
    rcases hrho.2.2.1.eq_or_lt with him | him
    · exfalso
      apply hhalf
      have hrhoEq : rho = (1 / 2 : ℂ) := by
        apply Complex.ext
        · simpa using hrho.2.1
        · simpa using him.symm
      simpa [hrhoEq] using hrho.1.1
    · exact him
  · intro hrho
    rw [mem_positiveCriticalLineZerosFinset] at hrho
    rw [HardyTheorem.mem_criticalLineZerosFinset]
    exact ⟨hrho.1, hrho.2.2.2, hrho.2.1.le, hrho.2.2.1⟩

theorem criticalLineZeroMultiplicityCount_eq_positive_of_half_ne_zero
    (T : ℝ) (hhalf : riemannZeta (1 / 2) ≠ 0) :
    HardyTheorem.criticalLineZeroMultiplicityCount T =
      positiveCriticalLineZeroMultiplicityCount T := by
  unfold HardyTheorem.criticalLineZeroMultiplicityCount
    positiveCriticalLineZeroMultiplicityCount
  rw [criticalLineZerosFinset_eq_positive_of_half_ne_zero T hhalf]

theorem criticalLineZeroMultiplicityCount_eq_half_add_positive
    {T : ℝ} (hT : 0 ≤ T) :
    HardyTheorem.criticalLineZeroMultiplicityCount T =
      analyticOrderNatAt riemannZeta (1 / 2) +
        positiveCriticalLineZeroMultiplicityCount T := by
  classical
  by_cases hhalf : riemannZeta (1 / 2) = 0
  · have hhalfZero : RiemannHypothesis.IsNontrivialZero (1 / 2 : ℂ) := by
      refine ⟨hhalf, by norm_num, by norm_num⟩
    have hhalfMem : (1 / 2 : ℂ) ∈ HardyTheorem.criticalLineZerosFinset T := by
      rw [HardyTheorem.mem_criticalLineZerosFinset]
      exact ⟨hhalfZero, by norm_num, by norm_num, by simpa using hT⟩
    have hdecomp :
        HardyTheorem.criticalLineZerosFinset T =
          {(1 / 2 : ℂ)} ∪ positiveCriticalLineZerosFinset T := by
      ext rho
      constructor
      · intro hrho
        rw [HardyTheorem.mem_criticalLineZerosFinset] at hrho
        by_cases him : 0 < rho.im
        · exact Finset.mem_union.mpr <| Or.inr <|
            mem_positiveCriticalLineZerosFinset.mpr
              ⟨hrho.1, him, hrho.2.2.2, hrho.2.1⟩
        · apply Finset.mem_union.mpr
          left
          rw [Finset.mem_singleton]
          apply Complex.ext
          · simpa using hrho.2.1
          · have : rho.im = 0 := by linarith [hrho.2.2.1]
            simpa using this
      · rw [Finset.mem_union]
        rintro (hrho | hrho)
        · rw [Finset.mem_singleton] at hrho
          subst rho
          exact hhalfMem
        · rw [mem_positiveCriticalLineZerosFinset] at hrho
          rw [HardyTheorem.mem_criticalLineZerosFinset]
          exact ⟨hrho.1, hrho.2.2.2, hrho.2.1.le, hrho.2.2.1⟩
    have hdisjoint :
        Disjoint ({(1 / 2 : ℂ)} : Finset ℂ)
          (positiveCriticalLineZerosFinset T) := by
      refine Finset.disjoint_left.mpr ?_
      intro rho hrho hpositive
      rw [Finset.mem_singleton] at hrho
      subst rho
      have := (mem_positiveCriticalLineZerosFinset.mp hpositive).2.1
      norm_num at this
    unfold HardyTheorem.criticalLineZeroMultiplicityCount
      positiveCriticalLineZeroMultiplicityCount
    rw [hdecomp, Finset.sum_union hdisjoint]
    simp
  · have hcount :=
      criticalLineZeroMultiplicityCount_eq_positive_of_half_ne_zero T hhalf
    have hanalytic : AnalyticAt ℂ riemannZeta (1 / 2 : ℂ) :=
      ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one (1 / 2 : ℂ) (by norm_num)
    have horder : analyticOrderAt riemannZeta (1 / 2) = 0 :=
      hanalytic.analyticOrderAt_eq_zero.mpr hhalf
    have hnat : analyticOrderNatAt riemannZeta (1 / 2 : ℂ) = 0 := by
      unfold analyticOrderNatAt
      rw [horder]
      rfl
    rw [hnat, zero_add]
    exact hcount

/-- Corrected bridge to the existing nonnegative-height Hardy count.  The
extra term is the possible multiplicity at the real point `1/2`. -/
theorem riemannZeroCount_add_halfMultiplicity_eq_criticalLine_add_two_mul_zeroDensityCount
    {T : ℝ} (hT : 0 ≤ T) :
    riemannZeroCount T + analyticOrderNatAt riemannZeta (1 / 2) =
      HardyTheorem.criticalLineZeroMultiplicityCount T +
        2 * ZeroDensity.zeroDensityCount (1 / 2) T := by
  rw [riemannZeroCount_eq_positiveCriticalLine_add_two_mul_zeroDensityCount,
    criticalLineZeroMultiplicityCount_eq_half_add_positive hT]
  omega

/-- The requested identity with the existing nonnegative-height critical-line
count, conditional on excluding a zero at `1/2`. -/
theorem riemannZeroCount_eq_criticalLine_add_two_mul_zeroDensityCount
    (T : ℝ) (hhalf : riemannZeta (1 / 2) ≠ 0) :
    riemannZeroCount T =
      HardyTheorem.criticalLineZeroMultiplicityCount T +
        2 * ZeroDensity.zeroDensityCount (1 / 2) T := by
  rw [riemannZeroCount_eq_positiveCriticalLine_add_two_mul_zeroDensityCount,
    criticalLineZeroMultiplicityCount_eq_positive_of_half_ne_zero T hhalf]

end RiemannVonMangoldt
end PrimeNumberTheorem
