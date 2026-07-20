import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZeta
import PrimeNumberTheorem.LeftVerticalEdge

open Complex Filter

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

private lemma gamma_regular_of_ne_zero_of_riemannZeta_ne_zero
    {s : ℂ} (hs0 : s ≠ 0) (hzeta : riemannZeta s ≠ 0) :
    ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    apply hs0
    linear_combination 2 * hn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    simp only [Nat.cast_succ] at hn
    have hs : s = -2 * ((k : ℂ) + 1) := by
      linear_combination 2 * hn
    apply hzeta
    rw [hs]
    exact riemannZeta_neg_two_mul_nat_add_one k

private lemma logDeriv_completedZeta_eq_elementary_add_completed
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hcompleted : completedRiemannZeta s ≠ 0) :
    logDeriv RiemannHypothesis.completedZeta s =
      1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
  let F : ℂ → ℂ := fun z => (1 / 2) * z
  let G : ℂ → ℂ := fun z => z - 1
  have hFne : F s ≠ 0 := mul_ne_zero (by norm_num) hs0
  have hGne : G s ≠ 0 := sub_ne_zero.mpr hs1
  have hFdiff : DifferentiableAt ℂ F s := by
    dsimp [F]
    fun_prop
  have hGdiff : DifferentiableAt ℂ G s := by
    dsimp [G]
    fun_prop
  have hFGne : F s * G s ≠ 0 := mul_ne_zero hFne hGne
  have hFGdiff : DifferentiableAt ℂ (fun z => F z * G z) s :=
    hFdiff.mul hGdiff
  have hcompletedDiff : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs0 hs1
  have heq := completedZeta_eventuallyEq_factorization hs0 hs1
  have hlogeq :
      logDeriv RiemannHypothesis.completedZeta s =
        logDeriv (fun z : ℂ => F z * G z * completedRiemannZeta z) s := by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq]
    congr 1
    simpa [F, G] using heq.self_of_nhds
  have hFlog : logDeriv F s = 1 / s := by
    dsimp [F]
    rw [logDeriv_const_mul s (1 / 2) (by norm_num)]
    simp [logDeriv_id']
  have hGlog : logDeriv G s = 1 / (s - 1) := by
    simp [G, logDeriv_apply]
  rw [hlogeq,
    logDeriv_mul s hFGne hcompleted hFGdiff hcompletedDiff,
    logDeriv_mul s hFne hGne hFdiff hGdiff, hFlog, hGlog]

theorem logDeriv_completedZeta_eq_zeta_add_gamma
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv RiemannHypothesis.completedZeta s =
      1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
        Complex.digamma (s / 2) / 2 + logDeriv riemannZeta s := by
  have hsGamma :=
    gamma_regular_of_ne_zero_of_riemannZeta_ne_zero hs0 hzeta
  have hGammaDiff :=
    ExplicitFormulaResidues.differentiableAt_Gammaℝ_of_regular hsGamma
  have hGammaNe : Gammaℝ s ≠ 0 := by
    intro hzero
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hzero
    exact hsGamma n (by
      rw [hn]
      ring)
  have hcompleted : completedRiemannZeta s ≠ 0 := by
    intro hzero
    apply hzeta
    rw [riemannZeta_def_of_ne_zero hs0, hzero]
    simp
  have hzetaLog :=
    ExplicitFormulaResidues.logDeriv_riemannZeta_eq_completed_sub_Gammaℝ
      hs0 hs1 hGammaNe hGammaDiff hzeta
  have hcompletedLog :
      logDeriv completedRiemannZeta s =
        logDeriv riemannZeta s + logDeriv Gammaℝ s := by
    calc
      logDeriv completedRiemannZeta s =
          (logDeriv completedRiemannZeta s - logDeriv Gammaℝ s) +
            logDeriv Gammaℝ s := by ring
      _ = logDeriv riemannZeta s + logDeriv Gammaℝ s := by
        rw [← hzetaLog]
  rw [logDeriv_completedZeta_eq_elementary_add_completed hs0 hs1 hcompleted,
    hcompletedLog, ExplicitFormulaResidues.logDeriv_Gammaℝ hsGamma]
  ring

end RiemannVonMangoldt
end PrimeNumberTheorem
