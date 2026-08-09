import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicTailHalfBarrier
import PrimeNumberTheorem.RiemannVonMangoldt.CriticalLinePartition
import PrimeNumberTheorem.RiemannVonMangoldt.SelbergScale

/-!
# Inconsistency of the current right-edge tail certificate

The finite-strip tail certificate requires every strip endpoint to lie
strictly to the right of the critical line.  The preceding half-plane barrier
therefore forces every positive-ordinate nontrivial zero to have real part
strictly greater than `1 / 2`.

This cannot hold for zeta zeros.  Reflection across the critical line preserves
both nontrivial-zero status and positive ordinate, while replacing `rho.re` by
`1 - rho.re`.  Applying the barrier to a zero and its reflection gives two
incompatible strict inequalities.

The Riemann--von Mangoldt lower bound supplies a positive-ordinate nontrivial
zero, so the current right-edge tail certificate is unconditionally
uninhabited.  This is an audit theorem: it does not construct the missing
critical-half decomposition and does not prove a zero-free region.
-/

open Filter

noncomputable section

namespace PrimeNumberTheorem

/-- The all-height Riemann--von Mangoldt lower bound supplies at least one
positive-ordinate nontrivial zeta zero. -/
theorem exists_positiveOrdinate_nontrivialZero :
    ∃ rho : ℂ,
      RiemannHypothesis.IsNontrivialZero rho ∧ 0 < rho.im := by
  rcases
      RiemannVonMangoldt.exists_eventually_riemannZeroCount_ge_selbergScale with
    ⟨c, hc, hcount⟩
  obtain ⟨T, hcountT, hT⟩ :=
    (hcount.and (eventually_gt_atTop (2 : ℝ))).exists
  have hTpos : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hscale :
      0 < c * (T / (2 * Real.pi) * Real.log T) := by
    positivity
  have hcountReal :
      0 < (RiemannVonMangoldt.riemannZeroCount T : ℝ) :=
    hscale.trans_le hcountT
  have hcountNat :
      0 < RiemannVonMangoldt.riemannZeroCount T := by
    exact_mod_cast hcountReal
  have hne :
      RiemannVonMangoldt.positiveNontrivialZerosFinset T ≠ ∅ := by
    intro hempty
    unfold RiemannVonMangoldt.riemannZeroCount at hcountNat
    rw [hempty] at hcountNat
    simp at hcountNat
  obtain ⟨rho, hrho⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hmem :=
    RiemannVonMangoldt.mem_positiveNontrivialZerosFinset.mp hrho
  exact ⟨rho, hmem.1, hmem.2.1⟩

/-- A single positive-ordinate zeta zero and its critical-line reflection
already contradict the current right-edge tail certificate. -/
theorem
    not_nonempty_rightEdgeTailCertificate_of_positiveZero_and_reflection
    {beta : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (rho : ℂ)
    (hzero : RiemannHypothesis.IsNontrivialZero rho)
    (him : 0 < rho.im) :
    ¬Nonempty
      (ActualWeightedBalancedGoodHeightRightEdgeTailCertificate
        (beta := beta) sigma tau selection) := by
  rintro ⟨certificate⟩
  have hright :=
    certificate.positiveZeros_strictlyRightOfHalf
      hbetaHalf hbetaOne hsigma hsigmaOne htau hthreshold
  have hrhoRight : 1 / 2 < rho.re :=
    hright rho hzero him
  let reflected :=
    RiemannVonMangoldt.criticalLineReflection rho
  have hreflectedZero :
      RiemannHypothesis.IsNontrivialZero reflected := by
    exact
      RiemannVonMangoldt.isNontrivialZero_criticalLineReflection hzero
  have hreflectedIm : 0 < reflected.im := by
    simpa [reflected] using him
  have hreflectedRight : 1 / 2 < reflected.re :=
    hright reflected hreflectedZero hreflectedIm
  have hreflectedRe : reflected.re = 1 - rho.re := by
    simp [reflected, RiemannVonMangoldt.criticalLineReflection]
  rw [hreflectedRe] at hreflectedRight
  linarith

/-- The current right-edge tail certificate is unconditionally uninhabited.

The contradiction uses only the existence of a positive-ordinate nontrivial
zero, critical-line reflection symmetry, and the certificate's own
strict-right-half consequence.
-/
theorem not_nonempty_actualWeightedBalancedGoodHeightRightEdgeTailCertificate
    {beta : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta) :
    ¬Nonempty
      (ActualWeightedBalancedGoodHeightRightEdgeTailCertificate
        (beta := beta) sigma tau selection) := by
  obtain ⟨rho, hzero, him⟩ :=
    exists_positiveOrdinate_nontrivialZero
  exact
    not_nonempty_rightEdgeTailCertificate_of_positiveZero_and_reflection
      sigma tau selection hbetaHalf hbetaOne hsigma hsigmaOne htau
      hthreshold rho hzero him

end PrimeNumberTheorem
