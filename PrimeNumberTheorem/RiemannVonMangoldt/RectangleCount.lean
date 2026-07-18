import PrimeNumberTheorem.RiemannVonMangoldt.ZeroCount
import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZeta
import PrimeNumberTheorem.ExplicitFormulaAux
import ZeroFreeRegion.MeromorphicAux
import MathlibAux.BoundaryRectResidue

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
      (completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
        hrePos hreLt).mp hzero
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
      (completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
        hzero.2.1 hzero.2.2).mpr hzero.1

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
  let K := zeroCountRectangle U T
  let poles := zeroCountRectanglePoles U T
  let multiplicity : ℂ → ℕ :=
    fun rho => analyticOrderNatAt riemannZeta rho
  let raw : ℂ → ℂ := fun z =>
    logDeriv RiemannHypothesis.completedZeta z -
      ∑ rho ∈ poles, (multiplicity rho : ℂ) * (z - rho)⁻¹
  let g := toMeromorphicNFOn raw K
  have hxiAnalytic :
      AnalyticOnNhd ℂ RiemannHypothesis.completedZeta K := by
    intro z _hz
    exact differentiable_completedZeta.analyticAt z
  have hzero : ∀ z ∈ K,
      RiemannHypothesis.completedZeta z = 0 ↔ z ∈ poles := by
    intro z hz
    exact completedZeta_zero_iff_mem_between_on_rectangle
      hU hUT hUgood hTgood hz
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
    rw [analyticOrderAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip
      hrhoData.1.2.1 hrhoData.1.2.2]
    exact
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_eq_analyticOrderAt_of_ne_one
        (by
          intro hrho1
          have hre := congrArg Complex.re hrho1
          simp at hre
          linarith [hrhoData.1.2.2])).symm
  have hregular : AnalyticOnNhd ℂ g K := by
    exact
      ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts
        hxiAnalytic poles multiplicity hzero horder
  have hrawMeromorphic : MeromorphicOn raw K := by
    exact ZeroFreeRegion.meromorphicOn_logDeriv_sub_finset_principalParts
      hxiAnalytic.meromorphicOn poles multiplicity
  have hboundary : ∀ z ∈ K,
      ¬(0 < z.re ∧ z.re < 1 ∧ U < z.im ∧ z.im < T) →
      logDeriv RiemannHypothesis.completedZeta z =
        g z + ∑ rho ∈ poles, (z - rho)⁻¹ * (multiplicity rho : ℂ) := by
    intro z hzK hzBoundary
    have hzNotPole : z ∉ poles := by
      intro hzPole
      exact hzBoundary (hpoles z hzPole)
    have hxiNe : RiemannHypothesis.completedZeta z ≠ 0 := by
      intro hxi
      exact hzNotPole ((hzero z hzK).mp hxi)
    have hxiAnalytic : AnalyticAt ℂ RiemannHypothesis.completedZeta z :=
      differentiable_completedZeta.analyticAt z
    have hlogAnalytic :
        AnalyticAt ℂ (logDeriv RiemannHypothesis.completedZeta) z :=
      hxiAnalytic.deriv.div hxiAnalytic hxiNe
    have hsumAnalytic : AnalyticAt ℂ
        (fun w : ℂ =>
          ∑ rho ∈ poles, (multiplicity rho : ℂ) * (w - rho)⁻¹) z := by
      apply Finset.analyticAt_fun_sum
      intro rho hrho
      have hzr : z ≠ rho := by
        intro h
        subst rho
        exact hzNotPole hrho
      exact analyticAt_const.mul
        ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzr))
    have hrawAnalytic : AnalyticAt ℂ raw z := by
      simpa [raw] using hlogAnalytic.sub hsumAnalytic
    have hgEq : g z = raw z := by
      rw [show g z = toMeromorphicNFOn raw K z by rfl,
        toMeromorphicNFOn_eq_toMeromorphicNFAt hrawMeromorphic hzK,
        congrFun (toMeromorphicNFAt_eq_self.mpr
          hrawAnalytic.meromorphicNFAt) z]
    have hsumComm :
        (∑ rho ∈ poles, (multiplicity rho : ℂ) * (z - rho)⁻¹) =
          ∑ rho ∈ poles, (z - rho)⁻¹ * (multiplicity rho : ℂ) := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      ring
    dsimp [raw] at hgEq
    rw [← hsumComm]
    linear_combination -hgEq
  calc
    MathlibAux.boundaryRectIntegral
        (logDeriv RiemannHypothesis.completedZeta) 0 1 U T =
      MathlibAux.boundaryRectIntegral
        (fun z => g z +
          ∑ rho ∈ poles, (z - rho)⁻¹ * (multiplicity rho : ℂ))
        0 1 U T := by
      apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
      simpa [K, zeroCountRectangle] using hboundary
    _ = (2 * Real.pi * I) *
        ∑ rho ∈ poles, (multiplicity rho : ℂ) :=
      MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
        poles (fun rho => (multiplicity rho : ℂ))
        hregular.differentiableOn hpoles
    _ = (2 * Real.pi * I) *
        ∑ rho ∈ positiveNontrivialZerosBetween U T,
          (analyticOrderNatAt riemannZeta rho : ℂ) := by
      rfl

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
