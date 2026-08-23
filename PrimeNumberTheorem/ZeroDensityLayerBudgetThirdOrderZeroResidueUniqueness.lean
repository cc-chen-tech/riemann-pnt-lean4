import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderZeroResidue

open Complex Set Filter Topology

namespace PrimeNumberTheorem.ExplicitFormulaResidues

private noncomputable def thirdOrderLaurentModel
    (G : ℂ → ℂ) (simple quadratic cubic z : ℂ) : ℂ :=
  G z + z⁻¹ * simple + z⁻¹ ^ 2 * quadratic + z⁻¹ ^ 3 * cubic

private lemma tendsto_cube_mul_thirdOrderLaurentModel
    {G : ℂ → ℂ} {simple quadratic cubic : ℂ}
    (hG : AnalyticAt ℂ G 0) :
    Tendsto
      (fun z : ℂ => z ^ 3 *
        thirdOrderLaurentModel G simple quadratic cubic z)
      (𝓝[≠] (0 : ℂ)) (𝓝 cubic) := by
  let P : ℂ → ℂ := fun z =>
    z ^ 3 * G z + z ^ 2 * simple + z * quadratic + cubic
  have hP : ContinuousAt P 0 := by
    dsimp [P]
    fun_prop
  have ht : Tendsto P (𝓝[≠] (0 : ℂ)) (𝓝 cubic) := by
    have ht0 : Tendsto P (𝓝[≠] (0 : ℂ)) (𝓝 (P 0)) :=
      hP.tendsto.mono_left nhdsWithin_le_nhds
    simpa [P] using ht0
  have heq :
      (fun z : ℂ => z ^ 3 *
        thirdOrderLaurentModel G simple quadratic cubic z) =ᶠ[𝓝[≠] (0 : ℂ)]
      P := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz
    dsimp [thirdOrderLaurentModel, P]
    field_simp [hz0]
  exact ht.congr' heq.symm

private lemma tendsto_sq_mul_thirdOrderLaurentModel_sub_cubic
    {G : ℂ → ℂ} {simple quadratic cubic : ℂ}
    (hG : AnalyticAt ℂ G 0) :
    Tendsto
      (fun z : ℂ => z ^ 2 *
        (thirdOrderLaurentModel G simple quadratic cubic z -
          z⁻¹ ^ 3 * cubic))
      (𝓝[≠] (0 : ℂ)) (𝓝 quadratic) := by
  let P : ℂ → ℂ := fun z =>
    z ^ 2 * G z + z * simple + quadratic
  have hP : ContinuousAt P 0 := by
    dsimp [P]
    fun_prop
  have ht : Tendsto P (𝓝[≠] (0 : ℂ)) (𝓝 quadratic) := by
    have ht0 : Tendsto P (𝓝[≠] (0 : ℂ)) (𝓝 (P 0)) :=
      hP.tendsto.mono_left nhdsWithin_le_nhds
    simpa [P] using ht0
  have heq :
      (fun z : ℂ => z ^ 2 *
        (thirdOrderLaurentModel G simple quadratic cubic z -
          z⁻¹ ^ 3 * cubic)) =ᶠ[𝓝[≠] (0 : ℂ)]
      P := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz
    dsimp [thirdOrderLaurentModel, P]
    field_simp [hz0]
    ring
  exact ht.congr' heq.symm

private lemma tendsto_mul_thirdOrderLaurentModel_sub_higher
    {G : ℂ → ℂ} {simple quadratic cubic : ℂ}
    (hG : AnalyticAt ℂ G 0) :
    Tendsto
      (fun z : ℂ => z *
        (thirdOrderLaurentModel G simple quadratic cubic z -
          z⁻¹ ^ 2 * quadratic - z⁻¹ ^ 3 * cubic))
      (𝓝[≠] (0 : ℂ)) (𝓝 simple) := by
  let P : ℂ → ℂ := fun z => z * G z + simple
  have hP : ContinuousAt P 0 := by
    dsimp [P]
    fun_prop
  have ht : Tendsto P (𝓝[≠] (0 : ℂ)) (𝓝 simple) := by
    have ht0 : Tendsto P (𝓝[≠] (0 : ℂ)) (𝓝 (P 0)) :=
      hP.tendsto.mono_left nhdsWithin_le_nhds
    simpa [P] using ht0
  have heq :
      (fun z : ℂ => z *
        (thirdOrderLaurentModel G simple quadratic cubic z -
          z⁻¹ ^ 2 * quadratic - z⁻¹ ^ 3 * cubic)) =ᶠ[𝓝[≠] (0 : ℂ)]
      P := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz
    dsimp [thirdOrderLaurentModel, P]
    field_simp [hz0]
    ring
  exact ht.congr' heq.symm

private theorem thirdOrderLaurentCoefficients_unique
    {G₁ G₂ : ℂ → ℂ}
    {simple₁ quadratic₁ cubic₁ simple₂ quadratic₂ cubic₂ : ℂ}
    (hG₁ : AnalyticAt ℂ G₁ 0) (hG₂ : AnalyticAt ℂ G₂ 0)
    (heq :
      (fun z => thirdOrderLaurentModel G₁ simple₁ quadratic₁ cubic₁ z)
        =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => thirdOrderLaurentModel G₂ simple₂ quadratic₂ cubic₂ z)) :
    simple₁ = simple₂ ∧ quadratic₁ = quadratic₂ ∧ cubic₁ = cubic₂ := by
  have heqCube :
      (fun z : ℂ => z ^ 3 *
        thirdOrderLaurentModel G₁ simple₁ quadratic₁ cubic₁ z)
        =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ => z ^ 3 *
        thirdOrderLaurentModel G₂ simple₂ quadratic₂ cubic₂ z) := by
    filter_upwards [heq] with z hz
    rw [hz]
  have hcubic : cubic₁ = cubic₂ := by
    have h₁ := tendsto_cube_mul_thirdOrderLaurentModel
      (G := G₁) (simple := simple₁) (quadratic := quadratic₁) (cubic := cubic₁) hG₁
    have h₂ := tendsto_cube_mul_thirdOrderLaurentModel
      (G := G₂) (simple := simple₂) (quadratic := quadratic₂) (cubic := cubic₂) hG₂
    exact tendsto_nhds_unique h₁ (h₂.congr' heqCube.symm)
  have heqSq :
      (fun z : ℂ => z ^ 2 *
        (thirdOrderLaurentModel G₁ simple₁ quadratic₁ cubic₁ z -
          z⁻¹ ^ 3 * cubic₁))
        =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ => z ^ 2 *
        (thirdOrderLaurentModel G₂ simple₂ quadratic₂ cubic₂ z -
          z⁻¹ ^ 3 * cubic₂)) := by
    filter_upwards [heq] with z hz
    rw [hz, hcubic]
  have hquadratic : quadratic₁ = quadratic₂ := by
    have h₁ := tendsto_sq_mul_thirdOrderLaurentModel_sub_cubic
      (G := G₁) (simple := simple₁) (quadratic := quadratic₁) (cubic := cubic₁) hG₁
    have h₂ := tendsto_sq_mul_thirdOrderLaurentModel_sub_cubic
      (G := G₂) (simple := simple₂) (quadratic := quadratic₂) (cubic := cubic₂) hG₂
    exact tendsto_nhds_unique h₁ (h₂.congr' heqSq.symm)
  have heqOne :
      (fun z : ℂ => z *
        (thirdOrderLaurentModel G₁ simple₁ quadratic₁ cubic₁ z -
          z⁻¹ ^ 2 * quadratic₁ - z⁻¹ ^ 3 * cubic₁))
        =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z : ℂ => z *
        (thirdOrderLaurentModel G₂ simple₂ quadratic₂ cubic₂ z -
          z⁻¹ ^ 2 * quadratic₂ - z⁻¹ ^ 3 * cubic₂)) := by
    filter_upwards [heq] with z hz
    rw [hz, hquadratic, hcubic]
  have hsimple : simple₁ = simple₂ := by
    have h₁ := tendsto_mul_thirdOrderLaurentModel_sub_higher
      (G := G₁) (simple := simple₁) (quadratic := quadratic₁) (cubic := cubic₁) hG₁
    have h₂ := tendsto_mul_thirdOrderLaurentModel_sub_higher
      (G := G₂) (simple := simple₂) (quadratic := quadratic₂) (cubic := cubic₂) hG₂
    exact tendsto_nhds_unique h₁ (h₂.congr' heqOne.symm)
  exact ⟨hsimple, hquadratic, hcubic⟩


/-- Identify the simple-pole coefficient at zero in the genuine third-order zeta
regularization. The neighborhood hypothesis is what permits comparison of Laurent
coefficients on a punctured neighborhood of zero. -/
theorem exists_thirdOrderExplicitFormula_zeroPole_regularization_explicit_zero_residue
    {x : ℝ} (hx : 0 < x) {K : Set ℂ} (hK : IsCompact K)
    (hKnhds : K ∈ 𝓝 (0 : ℂ)) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ)
        (quadratic cubic : ℂ) (G : ℂ → ℂ),
      0 ∈ poles ∧
      (∀ p ∈ poles, p = 0 ∨ p ∈ K) ∧
      (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ poles, residue p =
        if p = 0 then residue 0
        else if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 3) ∧
      residue 0 = iteratedDeriv 2 (thirdOrderZeroCore x) 0 / 2 ∧
      cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
      AnalyticOnNhd ℂ G K ∧
      ∀ z ∈ K, z ∉ poles →
        thirdOrderExplicitFormulaIntegrand x z =
          G z + ∑ p ∈ poles, (z - p)⁻¹ * residue p +
            quadratic * z⁻¹ ^ 2 + cubic * z⁻¹ ^ 3 := by
  have h0K : (0 : ℂ) ∈ K := mem_of_mem_nhds hKnhds
  obtain ⟨poles, residue, quadratic, cubic, G, h0mem, hpolesK,
      hpolesType, hresidue, hcubic, hG, heq⟩ :=
    exists_thirdOrderExplicitFormula_zeroPole_regularization hx hK h0K
  let nonzeroPoles := poles.erase 0
  let localPrincipal : ℂ → ℂ := fun z =>
    ∑ p ∈ nonzeroPoles, (z - p)⁻¹ * residue p
  have hpNonzero : ∀ p ∈ nonzeroPoles, p ≠ 0 := by
    intro p hp
    exact Finset.ne_of_mem_erase hp
  have hlocalPrincipal : AnalyticAt ℂ localPrincipal 0 := by
    dsimp [localPrincipal]
    have hsum (s : Finset ℂ) (hs : ∀ p ∈ s, p ≠ 0) :
        AnalyticAt ℂ (fun z => ∑ p ∈ s, (z - p)⁻¹ * residue p) 0 := by
      induction s using Finset.induction_on with
      | empty =>
          simpa using
            (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) 0)
      | @insert p s hp ih =>
          have hp0 : p ≠ 0 := hs p (Finset.mem_insert_self p s)
          have hs' : ∀ q ∈ s, q ≠ 0 := by
            intro q hq
            exact hs q (Finset.mem_insert_of_mem hq)
          have hterm :
              AnalyticAt ℂ (fun z : ℂ => (z - p)⁻¹ * residue p) 0 := by
            exact ((analyticAt_id.sub analyticAt_const).inv
              (sub_ne_zero.mpr hp0.symm)).mul analyticAt_const
          simpa only [Finset.sum_insert hp, Pi.add_apply] using hterm.add (ih hs')
    exact hsum nonzeroPoles hpNonzero
  let localG : ℂ → ℂ := fun z => G z + localPrincipal z
  have hlocalG : AnalyticAt ℂ localG 0 := by
    exact (hG 0 h0K).add hlocalPrincipal
  have havoidNhd :
      ∀ᶠ z : ℂ in 𝓝 0, ∀ p ∈ nonzeroPoles, z ≠ p := by
    exact nonzeroPoles.eventually_all.mpr fun p hp =>
      eventually_ne_nhds (hpNonzero p hp).symm
  have havoid :
      ∀ᶠ z : ℂ in 𝓝[≠] 0, z ∉ poles := by
    have havoidNhd' :
        ∀ᶠ z : ℂ in 𝓝[≠] 0, ∀ p ∈ nonzeroPoles, z ≠ p :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds havoidNhd
    filter_upwards [havoidNhd', self_mem_nhdsWithin] with z hzAvoid hz0
    intro hzPole
    have hzNe : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz0
    have hzNonzero : z ∈ nonzeroPoles :=
      Finset.mem_erase.mpr ⟨hzNe, hzPole⟩
    exact hzAvoid z hzNonzero rfl
  have hKpunct : ∀ᶠ z : ℂ in 𝓝[≠] 0, z ∈ K :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hKnhds
  have hglobal :
      (fun z : ℂ => thirdOrderExplicitFormulaIntegrand x z) =ᶠ[𝓝[≠] 0]
        (fun z : ℂ =>
          thirdOrderLaurentModel localG (residue 0) quadratic cubic z) := by
    filter_upwards [hKpunct, havoid] with z hzK hzPoles
    have hsplit :
        (∑ p ∈ poles, (z - p)⁻¹ * residue p) =
          localPrincipal z + z⁻¹ * residue 0 := by
      have h := Finset.sum_erase_add poles
        (fun p => (z - p)⁻¹ * residue p) h0mem
      simpa [nonzeroPoles, localPrincipal] using h.symm
    rw [heq z hzK hzPoles, hsplit]
    dsimp [thirdOrderLaurentModel, localG]
    ring
  obtain ⟨Gzero, hGzero, hzero⟩ :=
    exists_analyticAt_eventuallyEq_thirdOrderExplicitFormulaIntegrand_zeroPrincipalParts
      hx
  have hmodels :
      (fun z : ℂ =>
          thirdOrderLaurentModel localG (residue 0) quadratic cubic z)
        =ᶠ[𝓝[≠] 0]
      (fun z : ℂ =>
          thirdOrderLaurentModel Gzero
            (iteratedDeriv 2 (thirdOrderZeroCore x) 0 / 2)
            (deriv (thirdOrderZeroCore x) 0)
            (-deriv riemannZeta 0 / riemannZeta 0) z) := by
    apply hglobal.symm.trans
    simpa [thirdOrderLaurentModel, mul_comm] using hzero
  have hunique :=
    thirdOrderLaurentCoefficients_unique hlocalG hGzero hmodels
  refine ⟨poles, residue, quadratic, cubic, G, h0mem, hpolesK,
    hpolesType, hresidue, hunique.1, hcubic, hG, heq⟩

end PrimeNumberTheorem.ExplicitFormulaResidues
