import HardyTheorem.VerticalGammaAsymptotic

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

/-- The two leading terms in the Riemann-von Mangoldt zero-counting formula. -/
noncomputable def riemannVonMangoldtMainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) -
    T / (2 * Real.pi)

/-- The vertical Gamma phase model is exactly `pi` times the standard
Riemann-von Mangoldt main term, up to the fixed `-pi/8` shift. -/
theorem thetaModel_div_pi_eq_riemannVonMangoldtMainTerm_sub_eighth
    (T : ℝ) :
    HardyTheorem.thetaModel T / Real.pi =
      riemannVonMangoldtMainTerm T - 1 / 8 := by
  simp only [HardyTheorem.thetaModel, riemannVonMangoldtMainTerm]
  field_simp [Real.pi_ne_zero]

/-- After division by `pi`, the smooth vertical Gamma phase has exactly the
Riemann-von Mangoldt main term, a fixed additive constant, and an `O(1/T)`
error. -/
theorem exists_verticalGammaPhase_div_pi_sub_mainTerm_tendsto_const_inv :
    ∃ kappa C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      |HardyTheorem.verticalGammaUnwrappedPhase T / Real.pi -
          riemannVonMangoldtMainTerm T - kappa| ≤ C / T := by
  obtain ⟨kappa, C, hC, herr⟩ :=
    HardyTheorem.exists_verticalGammaUnwrappedPhase_sub_thetaModel_tendsto_const_inv
  refine ⟨kappa / Real.pi - 1 / 8, C / Real.pi,
    div_nonneg hC Real.pi_pos.le, ?_⟩
  intro T hT
  have hmodel :=
    thetaModel_div_pi_eq_riemannVonMangoldtMainTerm_sub_eighth T
  have hmain :
      riemannVonMangoldtMainTerm T =
        HardyTheorem.thetaModel T / Real.pi + 1 / 8 := by
    linarith
  have hrewrite :
      HardyTheorem.verticalGammaUnwrappedPhase T / Real.pi -
          riemannVonMangoldtMainTerm T -
            (kappa / Real.pi - 1 / 8) =
        (HardyTheorem.verticalGammaUnwrappedPhase T -
          HardyTheorem.thetaModel T - kappa) / Real.pi := by
    rw [hmain]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hrewrite, abs_div, abs_of_pos Real.pi_pos]
  calc
    |HardyTheorem.verticalGammaUnwrappedPhase T -
          HardyTheorem.thetaModel T - kappa| / Real.pi ≤
        (C / T) / Real.pi :=
      div_le_div_of_nonneg_right (herr T hT) Real.pi_pos.le
    _ = (C / Real.pi) / T := by ring

/-- Between two heights, the unknown additive phase constant cancels. The
normalized Gamma phase difference therefore differs from the difference of
the Riemann-von Mangoldt main terms by `O(1/U + 1/T)`. -/
theorem exists_verticalGammaPhase_difference_sub_mainTerm_difference_le_inv_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U T : ℝ, 1 ≤ U → 1 ≤ T →
      |(HardyTheorem.verticalGammaUnwrappedPhase T -
            HardyTheorem.verticalGammaUnwrappedPhase U) / Real.pi -
          (riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U)| ≤
        C / U + C / T := by
  obtain ⟨kappa, C, hC, herr⟩ :=
    exists_verticalGammaPhase_div_pi_sub_mainTerm_tendsto_const_inv
  refine ⟨C, hC, ?_⟩
  intro U T hU hT
  have hrewrite :
      (HardyTheorem.verticalGammaUnwrappedPhase T -
            HardyTheorem.verticalGammaUnwrappedPhase U) / Real.pi -
          (riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U) =
        (HardyTheorem.verticalGammaUnwrappedPhase T / Real.pi -
            riemannVonMangoldtMainTerm T - kappa) -
          (HardyTheorem.verticalGammaUnwrappedPhase U / Real.pi -
            riemannVonMangoldtMainTerm U - kappa) := by
    ring
  rw [hrewrite]
  calc
    |(HardyTheorem.verticalGammaUnwrappedPhase T / Real.pi -
          riemannVonMangoldtMainTerm T - kappa) -
        (HardyTheorem.verticalGammaUnwrappedPhase U / Real.pi -
          riemannVonMangoldtMainTerm U - kappa)| ≤
      |HardyTheorem.verticalGammaUnwrappedPhase T / Real.pi -
          riemannVonMangoldtMainTerm T - kappa| +
        |HardyTheorem.verticalGammaUnwrappedPhase U / Real.pi -
          riemannVonMangoldtMainTerm U - kappa| := abs_sub _ _
    _ ≤ C / T + C / U := add_le_add (herr T hT) (herr U hU)
    _ = C / U + C / T := by ring

end RiemannVonMangoldt
end PrimeNumberTheorem
