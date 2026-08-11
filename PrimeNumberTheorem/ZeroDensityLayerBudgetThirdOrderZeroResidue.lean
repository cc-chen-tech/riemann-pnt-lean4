import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroPoleLSeriesBridge

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem.ExplicitFormulaResidues

noncomputable def thirdOrderZeroCore (x : ℝ) (z : ℂ) : ℂ :=
  -logDeriv riemannZeta z * (x : ℂ) ^ z

private lemma taylor_sum_three_eq
    (g : ℂ → ℂ) (z : ℂ) :
    (∑ i ∈ Finset.range 3,
      (z ^ i / (i.factorial : ℂ)) • iteratedDeriv i g 0) =
      g 0 + z * deriv g 0 +
        z ^ 2 * (iteratedDeriv 2 g 0 / 2) := by
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one]
  ring

/-- The cubic Laurent coefficient of the genuine third-order kernel at zero. -/
theorem thirdOrderZeroCore_zero
    (x : ℝ) :
    thirdOrderZeroCore x 0 =
      -deriv riemannZeta 0 / riemannZeta 0 := by
  simp [thirdOrderZeroCore, logDeriv_apply]
  ring

/-- The genuine third-order kernel has an explicit Laurent expansion at zero.
The simple residue is the quadratic Taylor coefficient of thirdOrderZeroCore. -/
theorem exists_analyticAt_eventuallyEq_thirdOrderExplicitFormulaIntegrand_zeroPrincipalParts
    {x : ℝ} (hx : 0 < x) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      (fun z : ℂ => thirdOrderExplicitFormulaIntegrand x z) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z : ℂ =>
          G z +
            z⁻¹ * (iteratedDeriv 2 (thirdOrderZeroCore x) 0 / 2) +
            z⁻¹ ^ 2 * deriv (thirdOrderZeroCore x) 0 +
            z⁻¹ ^ 3 * (-deriv riemannZeta 0 / riemannZeta 0)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hzeta0 : riemannZeta (0 : ℂ) ≠ 0 := by
    rw [riemannZeta_zero]
    norm_num
  have hpow_diff : Differentiable ℂ (fun z : ℂ => (x : ℂ) ^ z) :=
    (differentiable_id : Differentiable ℂ (fun z : ℂ => z)).const_cpow
      (Or.inl hx0)
  have hcore_analytic : AnalyticAt ℂ (thirdOrderZeroCore x) 0 := by
    exact
      (ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
        0 (by norm_num) hzeta0).neg.mul (hpow_diff.analyticAt 0)
  obtain ⟨G, hG, hTaylor⟩ :=
    hcore_analytic.exists_eq_sum_add_pow_mul 3
  have hTaylor' : ∀ z : ℂ,
      thirdOrderZeroCore x z =
        thirdOrderZeroCore x 0 +
          z * deriv (thirdOrderZeroCore x) 0 +
          z ^ 2 * (iteratedDeriv 2 (thirdOrderZeroCore x) 0 / 2) +
          z ^ 3 * G z := by
    intro z
    have h := hTaylor z
    rw [taylor_sum_three_eq] at h
    simpa [smul_eq_mul, add_assoc] using h
  refine ⟨G, hG, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz
  rw [PrimeNumberTheorem.thirdOrderExplicitFormulaIntegrand_eq_negLogDerivPerron]
  have hcore :
      (x : ℂ) ^ z *
          (-deriv riemannZeta z / riemannZeta z) =
        thirdOrderZeroCore x z := by
    simp only [thirdOrderZeroCore, logDeriv_apply]
    ring
  rw [hcore, hTaylor' z, thirdOrderZeroCore_zero]
  field_simp [hz0]
  ring

end PrimeNumberTheorem.ExplicitFormulaResidues
