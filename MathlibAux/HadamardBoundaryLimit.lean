import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Passing interior three-lines bounds to a closed interval

This is a real-variable endpoint lemma.  It contains no complex analysis:
continuity of the boundary data lets an interpolation inequality on every
strictly smaller interval pass to the original closed interval.
-/

open Set Filter Topology

namespace MathlibAux

/-- A continuous nonnegative function satisfying the geometric interpolation
bound on every strict inner interval satisfies the corresponding bound on the
closed interval. -/
theorem le_endpoint_interp_of_continuousOn_of_inner_interp
    {f : ℝ → ℝ} {l u x : ℝ}
    (hlu : l < u) (hx : x ∈ Icc l u)
    (hf : ContinuousOn f (Icc l u))
    (hinner : ∀ l' u' : ℝ,
      l < l' → u' < u → l' < u' → x ∈ Icc l' u' →
      f x ≤ f l' ^ (1 - (x - l') / (u' - l')) *
        f u' ^ ((x - l') / (u' - l'))) :
    f x ≤ f l ^ (1 - (x - l) / (u - l)) *
      f u ^ ((x - l) / (u - l)) := by
  rcases eq_or_lt_of_le hx.1 with hxlEq | hlx
  · subst x
    simp
  rcases eq_or_lt_of_le hx.2 with hxuEq | hxu
  · subst x
    have hden : u - l ≠ 0 := sub_ne_zero.mpr hlu.ne'
    have hfrac : (u - l) / (u - l) = 1 := div_self hden
    rw [hfrac]
    simp
  let eps : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  let left : ℕ → ℝ := fun n => l + eps n
  let right : ℕ → ℝ := fun n => u - eps n
  have hdenTop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono'
      (l := atTop) (f₁ := fun n : ℕ => (n : ℝ))
    · exact Eventually.of_forall fun n => by norm_num
    · exact tendsto_natCast_atTop_atTop
  have heps : Tendsto eps atTop (𝓝 0) := by
    dsimp [eps]
    exact tendsto_const_nhds.div_atTop hdenTop
  have hepsPos : ∀ n, 0 < eps n := by
    intro n
    dsimp [eps]
    positivity
  have hepsLeft : ∀ᶠ n in atTop, eps n < x - l :=
    (tendsto_order.1 heps).2 (x - l) (sub_pos.mpr hlx)
  have hepsRight : ∀ᶠ n in atTop, eps n < u - x :=
    (tendsto_order.1 heps).2 (u - x) (sub_pos.mpr hxu)
  have hleftMem : ∀ᶠ n in atTop, left n ∈ Icc l u := by
    filter_upwards [hepsLeft] with n hn
    dsimp [left]
    constructor
    · linarith [hepsPos n]
    · linarith [hx.2]
  have hrightMem : ∀ᶠ n in atTop, right n ∈ Icc l u := by
    filter_upwards [hepsRight] with n hn
    dsimp [right]
    constructor
    · linarith [hx.1]
    · linarith [hepsPos n]
  have hleftTendsto : Tendsto left atTop (𝓝 l) := by
    dsimp [left]
    simpa using tendsto_const_nhds.add heps
  have hrightTendsto : Tendsto right atTop (𝓝 u) := by
    dsimp [right]
    simpa using tendsto_const_nhds.sub heps
  have hleftWithin : Tendsto left atTop (𝓝[Icc l u] l) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hleftTendsto, hleftMem⟩
  have hrightWithin : Tendsto right atTop (𝓝[Icc l u] u) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hrightTendsto, hrightMem⟩
  have hfLeft : Tendsto (fun n => f (left n)) atTop (𝓝 (f l)) :=
    (hf l ⟨le_rfl, hlu.le⟩).tendsto.comp hleftWithin
  have hfRight : Tendsto (fun n => f (right n)) atTop (𝓝 (f u)) :=
    (hf u ⟨hlu.le, le_rfl⟩).tendsto.comp hrightWithin
  let p : ℝ → ℝ := fun e =>
    1 - (x - (l + e)) / ((u - e) - (l + e))
  let q : ℝ → ℝ := fun e =>
    (x - (l + e)) / ((u - e) - (l + e))
  have hden0 : (u - 0) - (l + 0) ≠ 0 := by linarith
  have hpCont : ContinuousAt p 0 := by
    dsimp [p]
    fun_prop
  have hqCont : ContinuousAt q 0 := by
    dsimp [q]
    fun_prop
  have hpTendsto : Tendsto (fun n => p (eps n)) atTop (𝓝 (p 0)) :=
    hpCont.tendsto.comp heps
  have hqTendsto : Tendsto (fun n => q (eps n)) atTop (𝓝 (q 0)) :=
    hqCont.tendsto.comp heps
  have hp0 : 0 < p 0 := by
    dsimp [p]
    have hdenPos : 0 < u - l := sub_pos.mpr hlu
    have hdenNe : u - l ≠ 0 := hdenPos.ne'
    have heq : 1 - (x - l) / (u - l) = (u - x) / (u - l) := by
      field_simp [hdenNe]
      ring
    simpa [heq] using div_pos (sub_pos.mpr hxu) hdenPos
  have hq0 : 0 < q 0 := by
    dsimp [q]
    simpa using div_pos (sub_pos.mpr hlx) (sub_pos.mpr hlu)
  have hleftPow : Tendsto
      (fun n => f (left n) ^ p (eps n)) atTop
      (𝓝 (f l ^ p 0)) :=
    hfLeft.rpow hpTendsto (Or.inr hp0)
  have hrightPow : Tendsto
      (fun n => f (right n) ^ q (eps n)) atTop
      (𝓝 (f u ^ q 0)) :=
    hfRight.rpow hqTendsto (Or.inr hq0)
  have hRhs : Tendsto
      (fun n => f (left n) ^ p (eps n) *
        f (right n) ^ q (eps n)) atTop
      (𝓝 (f l ^ p 0 * f u ^ q 0)) :=
    hleftPow.mul hrightPow
  have hineq : ∀ᶠ n in atTop,
      f x ≤ f (left n) ^ p (eps n) *
        f (right n) ^ q (eps n) := by
    filter_upwards [hepsLeft, hepsRight] with n hnL hnR
    have hll : l < left n := by dsimp [left]; linarith [hepsPos n]
    have hru : right n < u := by dsimp [right]; linarith [hepsPos n]
    have hxl : left n ≤ x := by dsimp [left]; linarith
    have hxr : x ≤ right n := by dsimp [right]; linarith
    have hlr : left n < right n := by
      dsimp [left, right]
      linarith
    simpa [left, right, p, q] using
      hinner (left n) (right n) hll hru hlr ⟨hxl, hxr⟩
  have hlimit : f x ≤ f l ^ p 0 * f u ^ q 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hRhs hineq
  simpa [p, q] using hlimit

end MathlibAux
