import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lag-integral budget decomposition

For the lag form of a translated-correlation double integral, the section
`max 0 (-τ) < v ≤ min H (H - τ)` has length exactly the triangle weight
`H - |τ|`.  Consequently a lag integrand that splits as `M τ + E v τ` with
`v`-independent main part separates into the triangle-kernel transform of `M`
plus an error integral bounded by `ε * H^2` when `|E| ≤ ε` pointwise.  This
is the budget interface for the Selberg short-window second moment: the main
part is discharged by oscillation (triangle-kernel Fourier transform), and
the error part costs one triangle area `H^2`.
-/

open MeasureTheory Set

namespace MathlibAux

/-- The section length of the diagonal region is the triangle weight. -/
theorem lagSection_length {H τ : ℝ} (_hH : 0 ≤ H) (hτ : τ ∈ Icc (-H) H) :
    min H (H - τ) - max 0 (-τ) = H - |τ| := by
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hτ
  rcases le_total (0 : ℝ) τ with h | h
  · rw [max_eq_left (by linarith : -τ ≤ (0 : ℝ)),
      min_eq_right (by linarith : H - τ ≤ H), abs_of_nonneg h]
    ring
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ -τ),
      min_eq_left (by linarith : H ≤ H - τ), abs_of_nonpos h]

/-- The lag inner integral of a jointly continuous integrand is continuous on
each half of the lag interval. -/
theorem continuousOn_lagInner_right {E : ℝ → ℝ → ℝ}
    (hE : Continuous (Function.uncurry E)) {H : ℝ} :
    ContinuousOn (fun τ => ∫ v in max 0 (-τ)..min H (H - τ), E v τ)
      (Icc (0 : ℝ) H) := by
  have hEswap : Continuous (fun p : ℝ × ℝ => E p.2 p.1) :=
    hE.comp continuous_swap
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := (0 : ℝ)) (f := fun τ v : ℝ => E v τ) hEswap
    (s := fun τ => H - τ) (continuous_const.sub continuous_id)
  apply ContinuousOn.congr hcont.continuousOn
  intro τ hτ
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hτ
  show (∫ v in max 0 (-τ)..min H (H - τ), E v τ) = ∫ t in (0 : ℝ)..H - τ, E t τ
  rw [max_eq_left (by linarith : -τ ≤ (0 : ℝ)),
    min_eq_right (by linarith : H - τ ≤ H)]

/-- The lag inner integral of a jointly continuous integrand is continuous on
the left half of the lag interval. -/
theorem continuousOn_lagInner_left {E : ℝ → ℝ → ℝ}
    (hE : Continuous (Function.uncurry E)) {H : ℝ} :
    ContinuousOn (fun τ => ∫ v in max 0 (-τ)..min H (H - τ), E v τ)
      (Icc (-H) (0 : ℝ)) := by
  have hEswap : Continuous (fun p : ℝ × ℝ => E p.2 p.1) :=
    hE.comp continuous_swap
  have hdiff : Continuous fun τ =>
      (∫ v in (0 : ℝ)..H, E v τ) - ∫ v in (0 : ℝ)..(-τ), E v τ := by
    apply Continuous.sub
    · exact
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (μ := volume) (f := fun τ v : ℝ => E v τ) hEswap 0 H
    · exact
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (μ := volume) (a₀ := (0 : ℝ)) (f := fun τ v : ℝ => E v τ) hEswap
          (s := fun τ => -τ) continuous_neg
  apply ContinuousOn.congr hdiff.continuousOn
  intro τ hτ
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hτ
  show (∫ v in max 0 (-τ)..min H (H - τ), E v τ) =
    (∫ v in (0 : ℝ)..H, E v τ) - ∫ v in (0 : ℝ)..(-τ), E v τ
  rw [max_eq_right (by linarith : (0 : ℝ) ≤ -τ),
    min_eq_left (by linarith : H ≤ H - τ)]
  exact (intervalIntegral.integral_interval_sub_left
    (μ := volume) (f := fun v : ℝ => E v τ)
    ((hE.comp (continuous_id.prodMk continuous_const)).intervalIntegrable
      (0 : ℝ) H)
    ((hE.comp (continuous_id.prodMk continuous_const)).intervalIntegrable
      (0 : ℝ) (-τ))).symm

/-- The lag inner integral of a jointly continuous integrand is continuous on
the whole lag interval. -/
theorem continuousOn_lagInner {E : ℝ → ℝ → ℝ}
    (hE : Continuous (Function.uncurry E)) {H : ℝ} (hH : 0 ≤ H) :
    ContinuousOn (fun τ => ∫ v in max 0 (-τ)..min H (H - τ), E v τ)
      (Icc (-H) H) := by
  rw [← Set.Icc_union_Icc_eq_Icc (by linarith : -H ≤ (0 : ℝ)) hH]
  exact (continuousOn_lagInner_left hE).union_of_isClosed
    (continuousOn_lagInner_right hE) isClosed_Icc isClosed_Icc

/-- The triangle weight integrates to the triangle area `H^2`. -/
theorem integral_triangleKernel_eq_sq {H : ℝ} (hH : 0 ≤ H) :
    (∫ τ in (-H)..H, (H - |τ|)) = H ^ 2 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun τ : ℝ => H - |τ|) volume a b :=
    fun a b => (continuous_const.sub continuous_id.abs).intervalIntegrable _ _
  have h1 := intervalIntegral.integral_interval_sub_left (hint (-H) H) (hint (-H) 0)
  have hneg : (∫ τ in (-H)..(0 : ℝ), (H - |τ|)) = ∫ τ in (0 : ℝ)..H, (H - τ) := by
    have h3 := intervalIntegral.integral_comp_neg
      (f := fun τ => H - |τ|) (a := -H) (b := (0 : ℝ))
    rw [neg_zero, neg_neg] at h3
    have hrw : (∫ τ in (0 : ℝ)..H, (H - τ)) = ∫ τ in (0 : ℝ)..H, (H - |τ|) := by
      apply intervalIntegral.integral_congr
      intro τ hτ
      have hτ0 : (0 : ℝ) ≤ τ := by
        rw [uIcc_of_le hH] at hτ
        exact (mem_Icc.mp hτ).1
      show H - τ = H - |τ|
      rw [abs_of_nonneg hτ0]
    rw [hrw, ← h3]
    apply intervalIntegral.integral_congr
    intro τ _hτ
    show H - |τ| = H - |-τ|
    rw [abs_neg]
  have hhalf : (∫ τ in (0 : ℝ)..H, (H - τ)) = H ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub
      (f := fun _ : ℝ => H) (g := fun τ : ℝ => τ) intervalIntegrable_const
      ((continuous_id).intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const, integral_id]
    simp
    ring
  rw [hneg] at h1
  have hright : (∫ τ in (0 : ℝ)..H, (H - |τ|)) = H ^ 2 / 2 := by
    have hrw : (∫ τ in (0 : ℝ)..H, (H - τ)) = ∫ τ in (0 : ℝ)..H, (H - |τ|) := by
      apply intervalIntegral.integral_congr
      intro τ hτ
      have hτ0 : (0 : ℝ) ≤ τ := by
        rw [uIcc_of_le hH] at hτ
        exact (mem_Icc.mp hτ).1
      show H - τ = H - |τ|
      rw [abs_of_nonneg hτ0]
    rw [← hrw, hhalf]
  rw [hright] at h1
  linarith

/-- A lag integrand `M τ + E v τ` with `v`-independent main part separates
into the triangle-kernel transform of `M` plus the error lag integral. -/
theorem intervalIntegral_lagIntegral_add {M : ℝ → ℝ} {E : ℝ → ℝ → ℝ}
    (hM : Continuous M) (hE : Continuous (Function.uncurry E))
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ), (M τ + E v τ)) =
      (∫ τ in (-H)..H, (H - |τ|) * M τ) +
        ∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ), E v τ := by
  have hM_int : IntervalIntegrable (fun τ => (H - |τ|) * M τ) volume (-H) H :=
    ((continuous_const.sub continuous_id.abs).mul hM).intervalIntegrable _ _
  have hE_int : IntervalIntegrable
      (fun τ => ∫ v in max 0 (-τ)..min H (H - τ), E v τ) volume (-H) H :=
    (continuousOn_lagInner hE hH).intervalIntegrable_of_Icc (by linarith)
  rw [← intervalIntegral.integral_add hM_int hE_int]
  apply intervalIntegral.integral_congr
  intro τ hτ
  have hτI : τ ∈ Icc (-H) H := by
    rw [uIcc_of_le (by linarith : -H ≤ H)] at hτ
    exact hτ
  have hlen := lagSection_length hH hτI
  have hEv_int : IntervalIntegrable (fun v => E v τ) volume
      (max 0 (-τ)) (min H (H - τ)) :=
    (hE.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  show (∫ v in max 0 (-τ)..min H (H - τ), (M τ + E v τ)) =
    (H - |τ|) * M τ + ∫ v in max 0 (-τ)..min H (H - τ), E v τ
  rw [intervalIntegral.integral_add intervalIntegrable_const hEv_int]
  rw [intervalIntegral.integral_const, smul_eq_mul, hlen]

/-- The error lag integral is bounded by the pointwise bound times the
triangle area `H^2`. -/
theorem abs_lagIntegral_le_of_forall_norm_le {E : ℝ → ℝ → ℝ}
    (hE : Continuous (Function.uncurry E)) {H ε : ℝ} (hH : 0 ≤ H) (_hε : 0 ≤ ε)
    (hbound : ∀ v τ : ℝ, |E v τ| ≤ ε) :
    |∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ), E v τ| ≤ ε * H ^ 2 := by
  classical
  have hEswap : Continuous (fun p : ℝ × ℝ => E p.2 p.1) :=
    hE.comp continuous_swap
  have hFeq_right : ∀ τ ∈ Icc (0 : ℝ) H,
      (∫ v in max 0 (-τ)..min H (H - τ), E v τ) =
        ∫ v in (0 : ℝ)..H - τ, E v τ := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hτ
    rw [max_eq_left (by linarith : -τ ≤ (0 : ℝ)),
      min_eq_right (by linarith : H - τ ≤ H)]
  have hFeq_left : ∀ τ ∈ Icc (-H) (0 : ℝ),
      (∫ v in max 0 (-τ)..min H (H - τ), E v τ) =
        ∫ v in (-τ)..H, E v τ := by
    intro τ hτ
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hτ
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ -τ),
      min_eq_left (by linarith : H ≤ H - τ)]
  have hright :
      |∫ τ in (0 : ℝ)..H, ∫ v in max 0 (-τ)..min H (H - τ), E v τ| ≤
        ε * (H ^ 2 / 2) := by
    have habs_int : IntervalIntegrable
        (fun τ => |∫ v in max 0 (-τ)..min H (H - τ), E v τ|) volume 0 H :=
      ((continuousOn_lagInner_right hE).abs).intervalIntegrable_of_Icc hH
    have hw_int : IntervalIntegrable (fun τ => ε * (H - τ)) volume 0 H :=
      (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _
    have hpt : ∀ τ ∈ Icc (0 : ℝ) H,
        |∫ v in max 0 (-τ)..min H (H - τ), E v τ| ≤ ε * (H - τ) := by
      intro τ hτ
      obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hτ
      rw [hFeq_right τ hτ]
      refine le_trans (intervalIntegral.abs_integral_le_integral_abs
        (by linarith : (0 : ℝ) ≤ H - τ)) ?_
      calc
        (∫ v in (0 : ℝ)..H - τ, |E v τ|) ≤ ∫ v in (0 : ℝ)..H - τ, ε :=
          intervalIntegral.integral_mono_on (by linarith : (0 : ℝ) ≤ H - τ)
            (((hE.comp (continuous_id.prodMk continuous_const)).abs)
              |>.intervalIntegrable _ _)
            intervalIntegrable_const
            (fun v _hv => hbound v τ)
        _ = ε * (H - τ) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
    calc
      |∫ τ in (0 : ℝ)..H, ∫ v in max 0 (-τ)..min H (H - τ), E v τ|
        ≤ ∫ τ in (0 : ℝ)..H,
            |∫ v in max 0 (-τ)..min H (H - τ), E v τ| :=
        intervalIntegral.abs_integral_le_integral_abs hH
      _ ≤ ∫ τ in (0 : ℝ)..H, ε * (H - τ) :=
        intervalIntegral.integral_mono_on hH habs_int hw_int hpt
      _ = ε * (H ^ 2 / 2) := by
        have htriangle :
            (∫ τ in (0 : ℝ)..H, (H - τ)) = H ^ 2 / 2 := by
          rw [intervalIntegral.integral_sub
            (f := fun _ : ℝ => H) (g := fun τ : ℝ => τ)
            intervalIntegrable_const ((continuous_id).intervalIntegrable _ _)]
          rw [intervalIntegral.integral_const, integral_id]
          simp
          ring
        calc
          (∫ τ in (0 : ℝ)..H, ε * (H - τ)) =
              ε * ∫ τ in (0 : ℝ)..H, (H - τ) :=
            intervalIntegral.integral_const_mul ε (fun τ : ℝ => H - τ)
          _ = ε * (H ^ 2 / 2) := by rw [htriangle]
  have hleft :
      |∫ τ in (-H)..(0 : ℝ), ∫ v in max 0 (-τ)..min H (H - τ), E v τ| ≤
        ε * (H ^ 2 / 2) := by
    have habs_int : IntervalIntegrable
        (fun τ => |∫ v in max 0 (-τ)..min H (H - τ), E v τ|) volume (-H) 0 :=
      ((continuousOn_lagInner_left hE).abs).intervalIntegrable_of_Icc (by linarith)
    have hw_int : IntervalIntegrable (fun τ => ε * (H + τ)) volume (-H) 0 :=
      (continuous_const.mul (continuous_const.add continuous_id)).intervalIntegrable _ _
    have hpt : ∀ τ ∈ Icc (-H) (0 : ℝ),
        |∫ v in max 0 (-τ)..min H (H - τ), E v τ| ≤ ε * (H + τ) := by
      intro τ hτ
      obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hτ
      rw [hFeq_left τ hτ]
      refine le_trans (intervalIntegral.abs_integral_le_integral_abs
        (by linarith : -τ ≤ H)) ?_
      calc
        (∫ v in (-τ)..H, |E v τ|) ≤ ∫ v in (-τ)..H, ε :=
          intervalIntegral.integral_mono_on (by linarith : -τ ≤ H)
            (((hE.comp (continuous_id.prodMk continuous_const)).abs)
              |>.intervalIntegrable _ _)
            intervalIntegrable_const
            (fun v _hv => hbound v τ)
        _ = ε * (H + τ) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
    calc
      |∫ τ in (-H)..(0 : ℝ), ∫ v in max 0 (-τ)..min H (H - τ), E v τ|
        ≤ ∫ τ in (-H)..(0 : ℝ),
            |∫ v in max 0 (-τ)..min H (H - τ), E v τ| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
      _ ≤ ∫ τ in (-H)..(0 : ℝ), ε * (H + τ) :=
        intervalIntegral.integral_mono_on (by linarith) habs_int hw_int hpt
      _ = ε * (H ^ 2 / 2) := by
        have htriangle :
            (∫ τ in (-H)..(0 : ℝ), (H + τ)) = H ^ 2 / 2 := by
          rw [intervalIntegral.integral_add
            (f := fun _ : ℝ => H) (g := fun τ : ℝ => τ)
            intervalIntegrable_const ((continuous_id).intervalIntegrable _ _)]
          rw [intervalIntegral.integral_const, integral_id]
          simp
          ring
        calc
          (∫ τ in (-H)..(0 : ℝ), ε * (H + τ)) =
              ε * ∫ τ in (-H)..(0 : ℝ), (H + τ) :=
            intervalIntegral.integral_const_mul ε (fun τ : ℝ => H + τ)
          _ = ε * (H ^ 2 / 2) := by rw [htriangle]
  have hF_int_full : IntervalIntegrable
      (fun τ => ∫ v in max 0 (-τ)..min H (H - τ), E v τ) volume (-H) H :=
    ((continuousOn_lagInner_left hE).intervalIntegrable_of_Icc (by linarith)).trans
      ((continuousOn_lagInner_right hE).intervalIntegrable_of_Icc hH)
  have hsplit := intervalIntegral.integral_interval_sub_left hF_int_full
    ((continuousOn_lagInner_left hE).intervalIntegrable_of_Icc (by linarith))
  rw [show (∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ), E v τ) =
      (∫ τ in (-H)..(0 : ℝ), ∫ v in max 0 (-τ)..min H (H - τ), E v τ) +
        ∫ τ in (0 : ℝ)..H, ∫ v in max 0 (-τ)..min H (H - τ), E v τ by
        linarith]
  calc
    |(∫ τ in (-H)..(0 : ℝ), ∫ v in max 0 (-τ)..min H (H - τ), E v τ) +
        ∫ τ in (0 : ℝ)..H, ∫ v in max 0 (-τ)..min H (H - τ), E v τ|
      ≤ |∫ τ in (-H)..(0 : ℝ), ∫ v in max 0 (-τ)..min H (H - τ), E v τ| +
          |∫ τ in (0 : ℝ)..H, ∫ v in max 0 (-τ)..min H (H - τ), E v τ| :=
      abs_add_le _ _
    _ ≤ ε * (H ^ 2 / 2) + ε * (H ^ 2 / 2) := add_le_add hleft hright
    _ = ε * H ^ 2 := by ring

end MathlibAux
