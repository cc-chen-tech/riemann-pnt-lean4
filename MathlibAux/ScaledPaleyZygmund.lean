import MathlibAux.PaleyZygmund

open MeasureTheory Set

namespace MathlibAux

/-!
# Scaled Paley--Zygmund bounds

This module packages the second/fourth-moment Paley--Zygmund argument in the
scaled form used by logarithmic windows in analytic number theory.
-/

/--
Suppose a set has measure `ε * L`, the second moment of `g` is larger than
`c2 * L`, and its fourth moment is at most `C4 * L`. Then a fixed proportion
of the set has squared magnitude larger than `θ * c2 / ε`.
-/
theorem measure_sq_largeSet_gt_of_scaled_moments
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {g : α → ℝ} {ε L c2 C4 θ : ℝ}
    (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (hmeasure : μ.real s = ε * L)
    (hε : 0 < ε) (hL : 0 < L)
    (hc2 : 0 < c2) (hC4 : 0 < C4)
    (hg : Measurable g)
    (hg4 : IntegrableOn (fun x => g x ^ 4) s μ)
    (hsecond : c2 * L < ∫ x in s, g x ^ 2 ∂μ)
    (hfourth : (∫ x in s, g x ^ 4 ∂μ) ≤ C4 * L)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ((1 - θ) ^ 2 * c2 ^ 2 / C4) * L <
      μ.real {x ∈ s | θ * c2 / ε < g x ^ 2} := by
  let I2 : ℝ := ∫ x in s, g x ^ 2 ∂μ
  let I4 : ℝ := ∫ x in s, g x ^ 4 ∂μ
  let moving : Set α :=
    {x ∈ s | θ * (I2 / μ.real s) < g x ^ 2}
  let fixed : Set α :=
    {x ∈ s | θ * c2 / ε < g x ^ 2}
  have hμs_pos : 0 < μ.real s := by
    rw [hmeasure]
    exact mul_pos hε hL
  have hg2_measurable : Measurable (fun x => g x ^ 2) :=
    hg.pow_const 2
  have hg2_sq_integrable :
      IntegrableOn (fun x => (g x ^ 2) ^ 2) s μ := by
    simpa [← pow_mul] using hg4
  have hpz :
      (1 - θ) ^ 2 * I2 ^ 2 ≤
        μ.real moving * I4 := by
    simpa only [I2, I4, moving, ← pow_mul] using
      (paleyZygmund_mul_secondMoment_le_measure
        hs hμs hμs_pos hg2_measurable
        (fun x _ => sq_nonneg (g x))
        hg2_sq_integrable hθ0 hθ1)
  have hmean :
      c2 / ε < I2 / μ.real s := by
    rw [hmeasure]
    apply (div_lt_div_iff₀ hε (mul_pos hε hL)).2
    simpa only [I2, mul_assoc, mul_left_comm, mul_comm] using
      (mul_lt_mul_of_pos_right hsecond hε)
  have hthreshold :
      θ * c2 / ε ≤ θ * (I2 / μ.real s) := by
    have := mul_le_mul_of_nonneg_left hmean.le hθ0
    simpa only [mul_div_assoc] using this
  have hmoving_subset_fixed : moving ⊆ fixed := by
    intro x hx
    exact ⟨hx.1, hthreshold.trans_lt hx.2⟩
  have hfixed_ne_top : μ fixed ≠ ⊤ :=
    measure_ne_top_of_subset (fun _ hx => hx.1) hμs
  have hmeasure_mono :
      μ.real moving ≤ μ.real fixed :=
    measureReal_mono hmoving_subset_fixed hfixed_ne_top
  have hsecond' : c2 * L < I2 := by
    simpa only [I2] using hsecond
  have hI2_pos : 0 < I2 := by
    exact (mul_pos hc2 hL).trans hsecond'
  have hI4_nonneg : 0 ≤ I4 := by
    dsimp only [I4]
    exact setIntegral_nonneg hs fun x _ => by positivity
  have htheta_sq_pos : 0 < (1 - θ) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr hθ1)
  have hsquares :
      (c2 * L) ^ 2 < I2 ^ 2 := by
    nlinarith [mul_pos hc2 hL]
  have hlower :
      (1 - θ) ^ 2 * (c2 * L) ^ 2 <
        (1 - θ) ^ 2 * I2 ^ 2 :=
    mul_lt_mul_of_pos_left hsquares htheta_sq_pos
  have hfourth' : I4 ≤ C4 * L := by
    simpa only [I4] using hfourth
  have hCL_pos : 0 < C4 * L := mul_pos hC4 hL
  have hproduct_upper :
      μ.real moving * I4 ≤ μ.real fixed * (C4 * L) := by
    calc
      μ.real moving * I4 ≤ μ.real moving * (C4 * L) :=
        mul_le_mul_of_nonneg_left hfourth' measureReal_nonneg
      _ ≤ μ.real fixed * (C4 * L) :=
        mul_le_mul_of_nonneg_right hmeasure_mono hCL_pos.le
  have hscaled :
      (1 - θ) ^ 2 * (c2 * L) ^ 2 <
        μ.real fixed * (C4 * L) :=
    hlower.trans_le (hpz.trans hproduct_upper)
  change
    ((1 - θ) ^ 2 * c2 ^ 2 / C4) * L <
      μ.real fixed
  apply lt_of_mul_lt_mul_right
  · calc
      (((1 - θ) ^ 2 * c2 ^ 2 / C4) * L) * (C4 * L) =
          (1 - θ) ^ 2 * (c2 * L) ^ 2 := by
        field_simp [hC4.ne']
      _ < μ.real fixed * (C4 * L) := hscaled
  · exact hCL_pos.le

end MathlibAux
