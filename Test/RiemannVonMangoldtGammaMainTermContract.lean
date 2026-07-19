import PrimeNumberTheorem.RiemannVonMangoldt.GammaMainTerm

open Real

namespace PrimeNumberTheorem.RiemannVonMangoldt

example (T : ℝ) :
    riemannVonMangoldtMainTerm T =
      T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) -
        T / (2 * Real.pi) :=
  rfl

example (T : ℝ) :
    HardyTheorem.thetaModel T / Real.pi =
      riemannVonMangoldtMainTerm T - 1 / 8 :=
  thetaModel_div_pi_eq_riemannVonMangoldtMainTerm_sub_eighth T

example : ∃ kappa C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    |HardyTheorem.verticalGammaUnwrappedPhase T / Real.pi -
        riemannVonMangoldtMainTerm T - kappa| ≤ C / T :=
  exists_verticalGammaPhase_div_pi_sub_mainTerm_tendsto_const_inv

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ U T : ℝ, 1 ≤ U → 1 ≤ T →
    |(HardyTheorem.verticalGammaUnwrappedPhase T -
          HardyTheorem.verticalGammaUnwrappedPhase U) / Real.pi -
        (riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U)| ≤
      C / U + C / T :=
  exists_verticalGammaPhase_difference_sub_mainTerm_difference_le_inv_sum

end PrimeNumberTheorem.RiemannVonMangoldt
