import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderExplicitFormulaResidues

open Complex Set Filter Topology
open scoped BigOperators

private lemma taylor_sum_two_eq
    (g : ℂ → ℂ) (z : ℂ) :
    (∑ i ∈ Finset.range 2,
      (z ^ i / (i.factorial : ℂ)) • iteratedDeriv i g 0) =
      g 0 + z * deriv g 0 := by
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one]

private theorem exists_analyticOnNhd_secondTaylorQuotient
    {K : Set ℂ} {g : ℂ → ℂ} (h0 : 0 ∈ K)
    (hg : AnalyticOnNhd ℂ g K) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F K ∧
      ∀ z : ℂ, g z = g 0 + z * deriv g 0 + z ^ 2 * F z := by
  obtain ⟨F, hF0, hTaylor⟩ :=
    (hg 0 h0).exists_eq_sum_add_pow_mul 2
  have hTaylor' : ∀ z : ℂ,
      g z = g 0 + z * deriv g 0 + z ^ 2 * F z := by
    intro z
    have ht := hTaylor z
    rw [taylor_sum_two_eq] at ht
    simpa [smul_eq_mul, add_assoc] using ht
  refine ⟨F, ?_, hTaylor'⟩
  intro z hzK
  by_cases hz : z = 0
  · simpa [hz] using hF0
  · let Q : ℂ → ℂ := fun w =>
      (g w - (g 0 + w * deriv g 0)) / w ^ 2
    have hQ : AnalyticAt ℂ Q z := by
      have hpoly : AnalyticAt ℂ (fun w : ℂ => g 0 + w * deriv g 0) z := by
        fun_prop
      dsimp [Q]
      exact ((hg z hzK).fun_sub hpoly).div (analyticAt_id.pow 2)
        (pow_ne_zero 2 hz)
    apply hQ.congr
    filter_upwards [eventually_ne_nhds hz] with w hw
    dsimp [Q]
    have ht := hTaylor' w
    field_simp [hw]
    linear_combination ht

namespace PrimeNumberTheorem.ExplicitFormulaResidues

private lemma simplePoleTerm_div_sq_eq
    {z p r : ℂ} (hz : z ≠ 0) (hp : p ≠ 0) (hzp : z ≠ p) :
    ((z - p)⁻¹ * r) / z ^ 2 =
      (z - p)⁻¹ * (r / p ^ 2) -
        z⁻¹ * (r / p ^ 2) -
        z⁻¹ ^ 2 * (r / p) := by
  field_simp [hz, hp, sub_ne_zero.mpr hzp]
  ring

/-- Third-order regularization on a compact set containing zero. The cubic
principal part records the genuine zeta logarithmic-derivative pole at zero,
while every nonzero zeta zero keeps the expected residue divided by `p ^ 2`. -/
theorem exists_thirdOrderExplicitFormula_zeroPole_regularization
    {x : ℝ} (hx : 0 < x) {K : Set ℂ} (hK : IsCompact K)
    (h0K : 0 ∈ K) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ)
        (quadratic cubic : ℂ) (G : ℂ → ℂ),
      0 ∈ poles ∧
      (∀ p ∈ poles, p = 0 ∨ p ∈ K) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 0 then residue 0
        else if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
      AnalyticOnNhd ℂ G K ∧
      ∀ z ∈ K, z ∉ poles →
        thirdOrderExplicitFormulaIntegrand x z =
          G z + ∑ p ∈ poles, (z - p)⁻¹ * residue p +
            quadratic * z⁻¹ ^ 2 + cubic * z⁻¹ ^ 3 := by
  obtain ⟨poles, residue0, hpolesK, hpolesType, hpolesComplete,
      hresidue0, hraw, hg⟩ :=
    exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder
      hx hK
  have h0mem : 0 ∈ poles :=
    hpolesComplete 0 h0K (Or.inl rfl)
  let g : ℂ → ℂ :=
    toMeromorphicNFOn
      (fun z => explicitFormulaIntegrand x z -
        ∑ p ∈ poles, (z - p)⁻¹ * residue0 p) K
  have hrawg : ∀ z ∈ K, z ∉ poles →
      g z = explicitFormulaIntegrand x z -
        ∑ p ∈ poles, (z - p)⁻¹ * residue0 p := by
    simpa [g] using hraw
  have hgg : AnalyticOnNhd ℂ g K := by
    simpa [g] using hg
  let nonzeroPoles := poles.erase 0
  obtain ⟨F, hF, hTaylor⟩ :=
    exists_analyticOnNhd_secondTaylorQuotient h0K hgg
  let zeroResidue : ℂ :=
    deriv g 0 - ∑ p ∈ nonzeroPoles, residue0 p / p ^ 2
  let residue : ℂ → ℂ := fun p =>
    if p = 0 then zeroResidue else residue0 p / p ^ 2
  let quadratic : ℂ :=
    g 0 - ∑ p ∈ nonzeroPoles, residue0 p / p
  let cubic : ℂ := residue0 0
  refine ⟨poles, residue, quadratic, cubic, F,
    h0mem, hpolesK, hpolesType, ?_, ?_, hF, ?_⟩
  · intro p hp
    by_cases hp0 : p = 0
    · simp [residue, hp0]
    · rw [if_neg hp0]
      dsimp [residue]
      rw [if_neg hp0, hresidue0 p, if_neg hp0]
      by_cases hp1 : p = 1
      · simp [hp1]
      · simp only [if_neg hp1]
        field_simp [hp0]
  · dsimp [cubic]
    rw [hresidue0 0]
    simp
  · intro z hzK hzPoles
    have hz0 : z ≠ 0 := by
      intro hz
      subst z
      exact hzPoles h0mem
    have hzNonzeroPoles : z ∉ nonzeroPoles := by
      intro hz
      exact hzPoles (Finset.mem_of_mem_erase hz)
    have hpNonzero (p : ℂ) (hp : p ∈ nonzeroPoles) : p ≠ 0 :=
      Finset.ne_of_mem_erase hp
    have hpNotZ (p : ℂ) (hp : p ∈ nonzeroPoles) : z ≠ p := by
      intro hzp
      subst p
      exact hzNonzeroPoles hp
    have hsum :
        (∑ p ∈ nonzeroPoles, (z - p)⁻¹ * residue0 p) / z ^ 2 =
          (∑ p ∈ nonzeroPoles,
              (z - p)⁻¹ * (residue0 p / p ^ 2)) -
            z⁻¹ * (∑ p ∈ nonzeroPoles, residue0 p / p ^ 2) -
            z⁻¹ ^ 2 * (∑ p ∈ nonzeroPoles, residue0 p / p) := by
      rw [Finset.sum_div]
      calc
        _ = ∑ p ∈ nonzeroPoles,
            ((z - p)⁻¹ * (residue0 p / p ^ 2) -
              z⁻¹ * (residue0 p / p ^ 2) -
              z⁻¹ ^ 2 * (residue0 p / p)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact simplePoleTerm_div_sq_eq hz0
            (hpNonzero p hp) (hpNotZ p hp)
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
    have hsplit0 :
        (∑ p ∈ poles, (z - p)⁻¹ * residue0 p) =
          (∑ p ∈ nonzeroPoles, (z - p)⁻¹ * residue0 p) +
            z⁻¹ * residue0 0 := by
      have h := Finset.sum_erase_add poles
        (fun p => (z - p)⁻¹ * residue0 p) h0mem
      simpa [nonzeroPoles] using h.symm
    have hsplitResidue :
        (∑ p ∈ poles, (z - p)⁻¹ * residue p) =
          (∑ p ∈ nonzeroPoles,
              (z - p)⁻¹ * (residue0 p / p ^ 2)) +
            z⁻¹ * zeroResidue := by
      have h := (Finset.sum_erase_add poles
        (fun p => (z - p)⁻¹ * residue p) h0mem).symm
      have hnonzero :
          (∑ p ∈ nonzeroPoles, (z - p)⁻¹ * residue p) =
            ∑ p ∈ nonzeroPoles,
              (z - p)⁻¹ * (residue0 p / p ^ 2) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [residue, hpNonzero p hp]
      rw [hnonzero] at h
      simpa [nonzeroPoles, residue] using h
    have hbase := hrawg z hzK hzPoles
    have hbase' :
        explicitFormulaIntegrand x z =
          g z + ∑ p ∈ poles, (z - p)⁻¹ * residue0 p := by
      exact (eq_sub_iff_add_eq.mp hbase).symm
    have htaylor := hTaylor z
    rw [thirdOrderExplicitFormulaIntegrand]
    rw [hbase', add_div, hsplit0, add_div, hsum]
    rw [hsplitResidue]
    dsimp [zeroResidue, quadratic, cubic]
    field_simp [hz0]
    linear_combination z * htaylor

end PrimeNumberTheorem.ExplicitFormulaResidues
