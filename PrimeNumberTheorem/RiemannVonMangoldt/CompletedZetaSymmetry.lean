import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZeta
import Mathlib.Analysis.Calculus.Deriv.Star

open Complex Filter Set
open scoped ComplexConjugate

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

private theorem riemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hsconj : 1 < (conj s).re := by simpa using hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hsconj,
    zeta_eq_tsum_one_div_nat_add_one_cpow hs, Complex.conj_tsum]
  congr 1
  funext n
  rw [map_div₀, map_one]
  congr 1
  have hbase : (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) := by norm_num
  have harg : ((n : ℂ) + 1).arg ≠ Real.pi := by
    rw [hbase, Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  have hconjBase : conj ((n : ℂ) + 1) = (n : ℂ) + 1 := by
    rw [map_add, map_natCast, map_one]
  have hpow := Complex.cpow_conj ((n : ℂ) + 1) s harg
  rw [hconjBase] at hpow
  exact hpow

private theorem GammaR_conj (s : ℂ) :
    Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul]
  have hpi : ((Real.pi : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  have hpow := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) hpi
  have hGamma : Complex.Gamma (conj s / 2) =
      conj (Complex.Gamma (s / 2)) := by
    simpa only [map_div₀, map_ofNat] using Complex.Gamma_conj (s / 2)
  rw [hGamma]
  congr 1
  simpa only [map_neg, map_div₀, map_ofNat, Complex.conj_ofReal] using hpow

private theorem completedRiemannZeta_conj_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hsconj0 : conj s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg conj h
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hGammaConj : Gammaℝ (conj s) ≠ 0 := by
    rw [GammaR_conj]
    intro h
    apply hGamma
    simpa using congrArg conj h
  have hzeta := riemannZeta_conj_of_one_lt_re hs
  have hbase := riemannZeta_def_of_ne_zero hs0
  have hbaseConj := riemannZeta_def_of_ne_zero hsconj0
  have hcompleted :
      completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    calc
      completedRiemannZeta s =
          (completedRiemannZeta s / Gammaℝ s) * Gammaℝ s :=
        (div_mul_cancel₀ _ hGamma).symm
      _ = riemannZeta s * Gammaℝ s := by rw [← hbase]
      _ = Gammaℝ s * riemannZeta s := mul_comm _ _
  have hcompletedConj :
      completedRiemannZeta (conj s) =
        Gammaℝ (conj s) * riemannZeta (conj s) := by
    calc
      completedRiemannZeta (conj s) =
          (completedRiemannZeta (conj s) / Gammaℝ (conj s)) *
            Gammaℝ (conj s) := (div_mul_cancel₀ _ hGammaConj).symm
      _ = riemannZeta (conj s) * Gammaℝ (conj s) := by
        rw [← hbaseConj]
      _ = Gammaℝ (conj s) * riemannZeta (conj s) := mul_comm _ _
  rw [hcompletedConj, hcompleted, GammaR_conj, hzeta, map_mul]

private theorem completedZeta_conj_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    RiemannHypothesis.completedZeta (conj s) =
      conj (RiemannHypothesis.completedZeta s) := by
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hsconj0 : conj s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg conj h
  have hsconj1 : conj s ≠ 1 := by
    intro h
    apply hs1
    simpa using congrArg conj h
  rw [(completedZeta_eventuallyEq_factorization hsconj0 hsconj1).self_of_nhds,
    (completedZeta_eventuallyEq_factorization hs0 hs1).self_of_nhds]
  change (1 / 2 : ℂ) * conj s * (conj s - 1) *
      completedRiemannZeta (conj s) =
    conj ((1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s)
  rw [completedRiemannZeta_conj_of_one_lt_re hs, map_mul, map_mul, map_mul]
  simp only [map_div₀, map_one, map_ofNat, map_sub]

/-- The entire completed zeta function is real-symmetric. -/
theorem completedZeta_conj (s : ℂ) :
    RiemannHypothesis.completedZeta (conj s) =
      conj (RiemannHypothesis.completedZeta s) := by
  let xi := RiemannHypothesis.completedZeta
  let reflected : ℂ → ℂ := conj ∘ xi ∘ conj
  have hxi : AnalyticOnNhd ℂ xi univ :=
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_completedZeta
  have hreflectedDiff : Differentiable ℂ reflected := by
    intro z
    dsimp [reflected]
    simpa [Function.comp_def] using
      (differentiable_completedZeta.differentiableAt
        (x := conj z)).conj_conj
  have hreflected : AnalyticOnNhd ℂ reflected univ :=
    analyticOnNhd_univ_iff_differentiable.mpr hreflectedDiff
  have heventually : reflected =ᶠ[nhds (2 : ℂ)] xi := by
    have hre : ∀ᶠ z : ℂ in nhds (2 : ℂ), 1 < z.re :=
      isOpen_lt continuous_const Complex.continuous_re |>.eventually_mem (by norm_num)
    filter_upwards [hre] with z hz
    dsimp [reflected, xi]
    have h := completedZeta_conj_of_one_lt_re hz
    simpa using congrArg conj h
  have hfun : reflected = xi :=
    AnalyticOnNhd.eq_of_eventuallyEq hreflected hxi heventually
  have h := congrFun hfun (conj s)
  simpa [reflected, xi, Function.comp_def] using h.symm

private theorem deriv_completedZeta_conj (s : ℂ) :
    deriv RiemannHypothesis.completedZeta (conj s) =
      conj (deriv RiemannHypothesis.completedZeta s) := by
  let xi := RiemannHypothesis.completedZeta
  have hfun : (conj ∘ xi ∘ conj) = xi := by
    funext z
    simpa [xi, Function.comp_def] using
      congrArg conj (completedZeta_conj z)
  have hder := congrArg deriv hfun
  rw [deriv_conj_conj] at hder
  have h := congrFun hder (conj s)
  simpa [xi, Function.comp_def] using h.symm

/-- The logarithmic derivative of completed zeta respects conjugation. -/
theorem logDeriv_completedZeta_conj (s : ℂ) :
    logDeriv RiemannHypothesis.completedZeta (conj s) =
      conj (logDeriv RiemannHypothesis.completedZeta s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_completedZeta_conj,
    completedZeta_conj, map_div₀]

private theorem deriv_completedZeta_one_sub (s : ℂ) :
    deriv RiemannHypothesis.completedZeta (1 - s) =
      -deriv RiemannHypothesis.completedZeta s := by
  let xi := RiemannHypothesis.completedZeta
  have hfun : (fun z : ℂ => xi (1 - z)) = xi := by
    funext z
    exact (RiemannHypothesis.functional_equation z).symm
  have hright : HasDerivAt (fun z : ℂ => xi (1 - z))
      (-deriv xi (1 - s)) s := by
    have hinner : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
      simpa using (hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id' s)
    have houter : HasDerivAt xi (deriv xi (1 - s)) (1 - s) :=
      differentiable_completedZeta.differentiableAt.hasDerivAt
    convert houter.comp s hinner using 1 <;> simp [xi]
  have heq : deriv (fun z : ℂ => xi (1 - z)) s = deriv xi s := by
    rw [hfun]
  rw [hright.deriv] at heq
  change -deriv xi (1 - s) = deriv xi s at heq
  change deriv xi (1 - s) = -deriv xi s
  linear_combination -heq

/-- Functional equation plus real symmetry folds the logarithmic derivative
around the critical line at a fixed positive height. -/
theorem logDeriv_completedZeta_one_sub_conj (s : ℂ) :
    logDeriv RiemannHypothesis.completedZeta (1 - conj s) =
      -conj (logDeriv RiemannHypothesis.completedZeta s) := by
  have hvalue :
      RiemannHypothesis.completedZeta (1 - conj s) =
        RiemannHypothesis.completedZeta (conj s) :=
    (RiemannHypothesis.functional_equation (conj s)).symm
  rw [logDeriv_apply, deriv_completedZeta_one_sub, hvalue,
    deriv_completedZeta_conj, completedZeta_conj, logDeriv_apply, map_div₀]
  ring

end RiemannVonMangoldt
end PrimeNumberTheorem
