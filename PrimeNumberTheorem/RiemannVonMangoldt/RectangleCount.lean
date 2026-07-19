import PrimeNumberTheorem.RiemannVonMangoldt.ZeroCount
import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZeta
import PrimeNumberTheorem.ExplicitFormulaAux
import ZeroFreeRegion.MeromorphicAux
import MathlibAux.LogDerivArgumentPrinciple

open Complex Filter Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

private def zeroCountRectangle (U T : ℝ) : Set ℂ :=
  [[(0 : ℝ), 1]] ×ℂ [[U, T]]

private noncomputable def zeroCountRectanglePoles (U T : ℝ) : Finset ℂ :=
  positiveNontrivialZerosBetween U T

private lemma completedZeta_zero_iff_mem_between_on_rectangle
    {U T : ℝ} (hU : 0 < U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (_hTgood : ExplicitFormulaAux.goodHeight T)
    {z : ℂ} (hz : z ∈ zeroCountRectangle U T) :
    RiemannHypothesis.completedZeta z = 0 ↔
      z ∈ zeroCountRectanglePoles U T := by
  rw [zeroCountRectangle, Complex.mem_reProdIm,
    Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hUT.le] at hz
  have him : 0 < z.im := hU.trans_le hz.2.1
  constructor
  · intro hzero
    have hre0 : z.re ≠ 0 := by
      intro hre
      exact completedZeta_ne_zero_of_re_eq_zero_of_im_ne_zero hre
        (ne_of_gt him) hzero
    have hre1 : z.re ≠ 1 := by
      intro hre
      exact completedZeta_ne_zero_of_re_eq_one_of_im_ne_zero hre
        (ne_of_gt him) hzero
    have hrePos : 0 < z.re :=
      lt_of_le_of_ne hz.1.1 hre0.symm
    have hreLt : z.re < 1 :=
      lt_of_le_of_ne hz.1.2 hre1
    have hzeta : riemannZeta z = 0 :=
      (completedZetaContourData.completed_eq_zero_iff_base_eq_zero
        (s := z) hrePos hreLt).mp hzero
    have hnzero : RiemannHypothesis.IsNontrivialZero z :=
      ⟨hzeta, hrePos, hreLt⟩
    have hUim : U < z.im := by
      apply lt_of_le_of_ne hz.2.1
      intro heq
      exact hUgood z hnzero (by
        simpa [abs_of_pos him] using heq.symm)
    exact mem_positiveNontrivialZerosBetween hU.le |>.mpr
      ⟨hnzero, hUim, hz.2.2⟩
  · intro hpole
    rcases (mem_positiveNontrivialZerosBetween hU.le).mp hpole with
      ⟨hzero, _hUim, _hT⟩
    exact
      (completedZetaContourData.completed_eq_zero_iff_base_eq_zero
        (s := z) hzero.2.1 hzero.2.2).mpr hzero.1

private lemma zeroCountRectanglePoles_mem_interior
    {U T : ℝ} (hU : 0 < U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    ∀ rho ∈ zeroCountRectanglePoles U T,
      0 < rho.re ∧ rho.re < 1 ∧ U < rho.im ∧ rho.im < T := by
  intro rho hrho
  rcases (mem_positiveNontrivialZerosBetween hU.le).mp hrho with
    ⟨hzero, hUim, himT⟩
  have him : 0 < rho.im := hU.trans hUim
  have himT' : rho.im < T := by
    apply lt_of_le_of_ne himT
    intro heq
    exact hTgood rho hzero (by
      simpa [abs_of_pos him] using heq)
  exact ⟨hzero.2.1, hzero.2.2, hUim, himT'⟩

theorem boundaryRectIntegral_logDeriv_completedZeta_eq_between_sum
    {U T : ℝ} (hU : 0 < U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    MathlibAux.boundaryRectIntegral
        (logDeriv RiemannHypothesis.completedZeta) 0 1 U T =
      (2 * Real.pi * I) *
        ∑ rho ∈ positiveNontrivialZerosBetween U T,
          (analyticOrderNatAt riemannZeta rho : ℂ) := by
  classical
  let poles := zeroCountRectanglePoles U T
  let multiplicity : ℂ → ℕ :=
    fun rho => analyticOrderNatAt riemannZeta rho
  have hxiAnalytic :
      AnalyticOnNhd ℂ RiemannHypothesis.completedZeta
        ([[(0 : ℝ), 1]] ×ℂ [[U, T]]) := by
    intro z _hz
    exact differentiable_completedZeta.analyticAt z
  have hzero : ∀ z ∈ ([[(0 : ℝ), 1]] ×ℂ [[U, T]]),
      RiemannHypothesis.completedZeta z = 0 ↔ z ∈ poles := by
    intro z hz
    exact completedZeta_zero_iff_mem_between_on_rectangle
      hU hUT hUgood hTgood (by
        simpa [zeroCountRectangle] using hz)
  have hpoles :
      ∀ rho ∈ poles,
        0 < rho.re ∧ rho.re < 1 ∧ U < rho.im ∧ rho.im < T :=
    zeroCountRectanglePoles_mem_interior hU hTgood
  have horder : ∀ rho ∈ poles,
      analyticOrderAt RiemannHypothesis.completedZeta rho =
        multiplicity rho := by
    intro rho hrho
    have hrhoData :=
      (mem_positiveNontrivialZerosBetween hU.le).mp hrho
    have htransfer :
        analyticOrderAt RiemannHypothesis.completedZeta rho =
          analyticOrderAt riemannZeta rho := by
      simpa [completedZetaContourData] using
        (completedZetaContourData.analyticOrderAt_completed_eq_base
          (s := rho) hrhoData.1.2.1 hrhoData.1.2.2)
    rw [htransfer]
    exact
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_eq_analyticOrderAt_of_ne_one
        (by
          intro hrho1
          have hre := congrArg Complex.re hrho1
          simp at hre
          linarith [hrhoData.1.2.2])).symm
  simpa [poles, zeroCountRectanglePoles, multiplicity] using
    (MathlibAux.boundaryRectIntegral_logDeriv_eq_finite_zero_multiplicity_sum
      poles multiplicity hxiAnalytic hzero hpoles horder)

theorem boundaryRectIntegral_logDeriv_completedZeta_eq_zeroCount_sub
    {U T : ℝ} (hU : 0 < U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    MathlibAux.boundaryRectIntegral
        (logDeriv RiemannHypothesis.completedZeta) 0 1 U T =
      (2 * Real.pi * I) *
        ((riemannZeroCount T - riemannZeroCount U : ℕ) : ℂ) := by
  rw [boundaryRectIntegral_logDeriv_completedZeta_eq_between_sum
    hU hUT hUgood hTgood]
  congr 1
  exact_mod_cast (riemannZeroCount_sub_eq_between hUT.le).symm

end RiemannVonMangoldt
end PrimeNumberTheorem
