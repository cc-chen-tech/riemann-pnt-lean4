import MathlibAux.IntegralAbsSignChange

open MeasureTheory Set

namespace MathlibAux

/-!
# Local sign changes from strict integral cancellation

The extra hypothesis says that the zero set contains no nonempty interval.
This is the precise topological input needed to strengthen the usual
intermediate-value zero to a genuine local sign-changing zero.
-/

/-- A continuous function which is negative at `a`, positive at `b`, and
nonzero somewhere in every nonempty interval has a negative-to-positive
local sign change between `a` and `b`. -/
theorem exists_negToPos_local_sign_change_of_dense_ne_zero
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (ha : f a < 0) (hb : 0 < f b)
    (hdense : ∀ x y : ℝ, x < y → ∃ z ∈ Set.Ioo x y, f z ≠ 0) :
    ∃ c ∈ Set.Ioo a b,
      (∀ ε > 0, ∃ x ∈ Set.Ioo (c - ε) c, f x < 0) ∧
        ∀ ε > 0, ∃ x ∈ Set.Ioo c (c + ε), 0 < f x := by
  let S : Set ℝ := {x | a ≤ x ∧ x ≤ b ∧ f x < 0}
  have hSne : S.Nonempty := ⟨a, le_rfl, hab.le, ha⟩
  have hSbdd : BddAbove S := ⟨b, fun _ hx => hx.2.1⟩
  let c : ℝ := sSup S
  have ha_le_c : a ≤ c := by
    exact hSne.some_mem.1.trans (le_csSup hSbdd hSne.some_mem)
  have hc_le_b : c ≤ b := by
    exact csSup_le hSne fun _ hx => hx.2.1
  have ha_lt_c : a < c := by
    have hnear : ∀ᶠ x : ℝ in nhds a, f x < 0 :=
      hf.continuousAt.eventually_lt continuousAt_const ha
    rw [Metric.eventually_nhds_iff] at hnear
    obtain ⟨δ, hδ, hbound⟩ := hnear
    let η : ℝ := min (δ / 2) ((b - a) / 2)
    have hη : 0 < η := by
      dsimp only [η]
      exact lt_min (half_pos hδ) (half_pos (sub_pos.mpr hab))
    have hηδ : η < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hηab : η < b - a :=
      (min_le_right _ _).trans_lt (half_lt_self (sub_pos.mpr hab))
    have hfaη : f (a + η) < 0 := by
      apply hbound
      simpa [Real.dist_eq, abs_of_nonneg hη.le] using hηδ
    have hmem : a + η ∈ S := by
      exact ⟨by linarith, by linarith, hfaη⟩
    have hle : a + η ≤ c := by
      exact le_csSup hSbdd hmem
    linarith
  have hc_lt_b : c < b := by
    have hnear : ∀ᶠ x : ℝ in nhds b, 0 < f x :=
      continuousAt_const.eventually_lt hf.continuousAt hb
    rw [Metric.eventually_nhds_iff] at hnear
    obtain ⟨δ, hδ, hbound⟩ := hnear
    have hub : ∀ x ∈ S, x ≤ b - δ / 2 := by
      intro x hx
      by_contra hnot
      have hxgt : b - δ / 2 < x := lt_of_not_ge hnot
      have hdist : dist x b < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.2.1)]
        linarith
      exact (not_lt_of_ge (hbound hdist).le) hx.2.2
    have hcle : c ≤ b - δ / 2 := csSup_le hSne hub
    linarith
  have hc_upper : ∀ x ∈ S, x ≤ c := fun _ hx => le_csSup hSbdd hx
  have hfc_nonpos : f c ≤ 0 := by
    by_contra hnot
    have hfc_pos : 0 < f c := lt_of_not_ge hnot
    have hnear : ∀ᶠ x : ℝ in nhds c, 0 < f x :=
      continuousAt_const.eventually_lt hf.continuousAt hfc_pos
    rw [Metric.eventually_nhds_iff] at hnear
    obtain ⟨δ, hδ, hbound⟩ := hnear
    have hlt : c - δ / 2 < sSup S := by
      simpa only [c] using sub_lt_self c (half_pos hδ)
    obtain ⟨x, hxS, hxgt⟩ := exists_lt_of_lt_csSup hSne hlt
    have hxc : x ≤ c := hc_upper x hxS
    have hdist : dist x c < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxc)]
      linarith
    exact (not_lt_of_ge (hbound hdist).le) hxS.2.2
  have hfc_nonneg : 0 ≤ f c := by
    by_contra hnot
    have hfc_neg : f c < 0 := lt_of_not_ge hnot
    have hnear : ∀ᶠ x : ℝ in nhds c, f x < 0 :=
      hf.continuousAt.eventually_lt continuousAt_const hfc_neg
    rw [Metric.eventually_nhds_iff] at hnear
    obtain ⟨δ, hδ, hbound⟩ := hnear
    let η : ℝ := min (δ / 2) ((b - c) / 2)
    have hη : 0 < η := by
      dsimp only [η]
      exact lt_min (half_pos hδ) (half_pos (sub_pos.mpr hc_lt_b))
    have hηδ : η < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    have hηcb : η < b - c :=
      (min_le_right _ _).trans_lt (half_lt_self (sub_pos.mpr hc_lt_b))
    have hfcη : f (c + η) < 0 := by
      apply hbound
      simpa [Real.dist_eq, abs_of_nonneg hη.le] using hηδ
    have hmem : c + η ∈ S := by
      exact ⟨by linarith, by linarith, hfcη⟩
    exact (not_lt_of_ge (hc_upper (c + η) hmem)) (by linarith)
  have hfc : f c = 0 := le_antisymm hfc_nonpos hfc_nonneg
  refine ⟨c, ⟨ha_lt_c, hc_lt_b⟩, ?_, ?_⟩
  · intro ε hε
    have hlt : c - ε < sSup S := by
      simpa only [c] using sub_lt_self c hε
    obtain ⟨x, hxS, hxgt⟩ := exists_lt_of_lt_csSup hSne hlt
    have hxc : x < c := (hc_upper x hxS).lt_of_ne fun h => by
      subst x
      exact (ne_of_lt hxS.2.2) hfc
    exact ⟨x, ⟨hxgt, hxc⟩, hxS.2.2⟩
  · intro ε hε
    let d : ℝ := min (c + ε) b
    have hcd : c < d := by
      dsimp only [d]
      exact lt_min (lt_add_of_pos_right c hε) hc_lt_b
    obtain ⟨x, hx, hxne⟩ := hdense c d hcd
    have hxcb : x ≤ b := hx.2.le.trans (min_le_right _ _)
    have hax : a ≤ x := ha_lt_c.le.trans hx.1.le
    have hfx_nonneg : 0 ≤ f x := by
      by_contra hnot
      have hxS : x ∈ S := ⟨hax, hxcb, lt_of_not_ge hnot⟩
      exact (not_lt_of_ge (hc_upper x hxS)) hx.1
    have hfx_pos : 0 < f x := lt_of_le_of_ne hfx_nonneg (Ne.symm hxne)
    refine ⟨x, ⟨hx.1, ?_⟩, hfx_pos⟩
    exact hx.2.trans_le (min_le_left _ _)

/-- Strict cancellation in an interval integral produces a genuine local
sign change when the continuous function's zero set contains no interval. -/
theorem exists_local_sign_change_of_abs_intervalIntegral_lt_intervalIntegral_abs
    {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (hstrict : |∫ x in a..b, f x| < ∫ x in a..b, |f x|)
    (hdense : ∀ x y : ℝ, x < y → ∃ z ∈ Set.Ioo x y, f z ≠ 0) :
    ∃ c ∈ Set.Ioo a b,
      ((∀ ε > 0, ∃ x ∈ Set.Ioo (c - ε) c, f x < 0) ∧
          ∀ ε > 0, ∃ x ∈ Set.Ioo c (c + ε), 0 < f x) ∨
        ((∀ ε > 0, ∃ x ∈ Set.Ioo (c - ε) c, 0 < f x) ∧
          ∀ ε > 0, ∃ x ∈ Set.Ioo c (c + ε), f x < 0) := by
  have hneg : ∃ x ∈ Set.Icc a b, f x < 0 := by
    by_contra hnot
    push Not at hnot
    have hnonneg : 0 ≤ ∫ x in a..b, f x :=
      intervalIntegral.integral_nonneg hab hnot
    have heq : (∫ x in a..b, |f x|) = ∫ x in a..b, f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact abs_of_nonneg (hnot x hx)
    rw [heq, abs_of_nonneg hnonneg] at hstrict
    exact lt_irrefl _ hstrict
  have hpos : ∃ x ∈ Set.Icc a b, 0 < f x := by
    by_contra hnot
    push Not at hnot
    have hnegint : 0 ≤ ∫ x in a..b, -f x :=
      intervalIntegral.integral_nonneg hab fun x hx =>
        neg_nonneg.mpr (hnot x hx)
    rw [intervalIntegral.integral_neg] at hnegint
    have hnonpos : (∫ x in a..b, f x) ≤ 0 := by linarith
    have heq : (∫ x in a..b, |f x|) = -∫ x in a..b, f x := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact abs_of_nonpos (hnot x hx)
    rw [heq, abs_of_nonpos hnonpos] at hstrict
    exact lt_irrefl _ hstrict
  obtain ⟨x, hx, hxneg⟩ := hneg
  obtain ⟨y, hy, hypos⟩ := hpos
  have hxyne : x ≠ y := by
    intro hxy
    subst y
    linarith
  rcases lt_or_gt_of_ne hxyne with hxy | hyx
  · obtain ⟨c, hc, hchange⟩ :=
      exists_negToPos_local_sign_change_of_dense_ne_zero
        hf hxy hxneg hypos hdense
    exact ⟨c, ⟨hx.1.trans_lt hc.1, hc.2.trans_le hy.2⟩, Or.inl hchange⟩
  · have hneg_dense : ∀ p q : ℝ, p < q →
        ∃ z ∈ Set.Ioo p q, (-f) z ≠ 0 := by
      intro p q hpq
      obtain ⟨z, hz, hz0⟩ := hdense p q hpq
      exact ⟨z, hz, neg_ne_zero.mpr hz0⟩
    obtain ⟨c, hc, hchange⟩ :=
      exists_negToPos_local_sign_change_of_dense_ne_zero
        hf.neg hyx (neg_neg_of_pos hypos) (neg_pos.mpr hxneg) hneg_dense
    refine ⟨c, ⟨hy.1.trans_lt hc.1, hc.2.trans_le hx.2⟩, Or.inr ?_⟩
    constructor
    · intro ε hε
      obtain ⟨z, hz, hzneg⟩ := hchange.1 ε hε
      exact ⟨z, hz, neg_lt_zero.mp hzneg⟩
    · intro ε hε
      obtain ⟨z, hz, hzpos⟩ := hchange.2 ε hε
      exact ⟨z, hz, neg_pos.mp hzpos⟩

end MathlibAux
