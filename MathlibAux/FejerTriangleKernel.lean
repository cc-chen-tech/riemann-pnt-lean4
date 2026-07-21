import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Triangle-kernel (Fejér) form of a translated-correlation double integral

The double integral of a translated continuous function over a square window
collapses to a one-dimensional integral against the triangle kernel:

```
∫_{v in 0..H} ∫_{w in 0..H} f (w - v) = ∫_{t in -H..H} (H - |t|) * f t .
```

The proof uses a primitive `G` of `f`, the substitution `w - v = t`, and one
integration by parts on each half-interval.  This is the geometric identity
behind the `sinc`-type decay of short-window second moments: the triangle
kernel is the Fourier transform of the squared rectangular window.
-/

open MeasureTheory Set

namespace MathlibAux

/-- A translated-correlation double integral over a square window equals the
triangle-kernel weighted integral of the function. -/
theorem intervalIntegral_pair_sub_eq_triangle_kernel
    {f : ℝ → ℝ} (hf : Continuous f) {H : ℝ} (hH : 0 ≤ H) :
    (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, f (w - v)) =
      ∫ τ in (-H)..H, (H - |τ|) * f τ := by
  classical
  set G : ℝ → ℝ := fun y => ∫ t in (0 : ℝ)..y, f t with hGdef
  have hG0 : G 0 = 0 := by
    have h : (∫ t in (0 : ℝ)..(0 : ℝ), f t) = 0 := intervalIntegral.integral_same
    exact h
  have hGderiv : ∀ x : ℝ, HasDerivAt G (f x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hGcont : Continuous G :=
    continuous_iff_continuousAt.mpr fun x => (hGderiv x).continuousAt
  have hsub : ∀ v : ℝ, (∫ w in (0 : ℝ)..H, f (w - v)) = G (H - v) - G (-v) := by
    intro v
    rw [intervalIntegral.integral_comp_sub_right]
    have hGdiff :
        (∫ t in (0 : ℝ)..(H - v), f t) - (∫ t in (0 : ℝ)..(-v), f t) =
          ∫ x in (-v)..H - v, f x :=
      intervalIntegral.integral_interval_sub_left
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
    rw [zero_sub]
    exact hGdiff.symm
  -- Integration by parts on the right half: ∫ (H - τ) f τ = ∫ G τ over 0..H.
  have hright :
      (∫ τ in (0 : ℝ)..H, (H - τ) * f τ) = ∫ τ in (0 : ℝ)..H, G τ := by
    have hu : ∀ x ∈ uIcc (0 : ℝ) H, HasDerivAt (fun τ => H - τ) (-1) x :=
      fun x _hx => by
        simpa using (hasDerivAt_id' x).const_sub H
    have hsum := intervalIntegral.integral_deriv_mul_eq_sub
      (u := fun τ => H - τ) (u' := fun _ => -1)
      (v := G) (v' := f)
      hu (fun x _hx => hGderiv x)
      intervalIntegrable_const (hf.intervalIntegrable _ _)
    have hsplit :
        (∫ τ in (0 : ℝ)..H, (-1) * G τ + (H - τ) * f τ) =
          (∫ τ in (0 : ℝ)..H, (-1) * G τ) + ∫ τ in (0 : ℝ)..H, (H - τ) * f τ :=
      intervalIntegral.integral_add
        ((hGcont.const_mul _).intervalIntegrable _ _)
        (((continuous_const.sub continuous_id).mul hf).intervalIntegrable _ _)
    have hneg : (∫ τ in (0 : ℝ)..H, (-1) * G τ) = -∫ τ in (0 : ℝ)..H, G τ := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro τ _hτ
      show (-1 : ℝ) * G τ = -G τ
      rw [neg_one_mul]
    have hbnd : (H - H) * G H - (H - 0) * G 0 = 0 := by
      rw [hG0]
      ring
    dsimp only at hsum
    rw [hsplit, hneg, hbnd] at hsum
    linarith
  -- Integration by parts on the left half: ∫ (H + τ) f τ = -∫ G τ over -H..0.
  have hleft :
      (∫ τ in (-H)..(0 : ℝ), (H + τ) * f τ) = -∫ τ in (-H)..(0 : ℝ), G τ := by
    have hu : ∀ x ∈ uIcc (-H) (0 : ℝ), HasDerivAt (fun τ => H + τ) 1 x :=
      fun x _hx => by
        simpa using (hasDerivAt_id' x).const_add H
    have hsum := intervalIntegral.integral_deriv_mul_eq_sub
      (u := fun τ => H + τ) (u' := fun _ => 1)
      (v := G) (v' := f)
      hu (fun x _hx => hGderiv x)
      intervalIntegrable_const (hf.intervalIntegrable _ _)
    have hsplit :
        (∫ τ in (-H)..(0 : ℝ), 1 * G τ + (H + τ) * f τ) =
          (∫ τ in (-H)..(0 : ℝ), 1 * G τ) + ∫ τ in (-H)..(0 : ℝ), (H + τ) * f τ :=
      intervalIntegral.integral_add
        ((hGcont.const_mul _).intervalIntegrable _ _)
        (((continuous_const.add continuous_id).mul hf).intervalIntegrable _ _)
    have hone : (∫ τ in (-H)..(0 : ℝ), 1 * G τ) = ∫ τ in (-H)..(0 : ℝ), G τ := by
      apply intervalIntegral.integral_congr
      intro τ _hτ
      show (1 : ℝ) * G τ = G τ
      rw [one_mul]
    have hbnd : (H + 0) * G 0 - (H + -H) * G (-H) = 0 := by
      rw [hG0]
      ring
    dsimp only at hsum
    rw [hsplit, hone, hbnd] at hsum
    linarith
  -- Substitutions collapsing the square integral to primitive integrals.
  have hright_sub :
      (∫ v in (0 : ℝ)..H, G (H - v)) = ∫ τ in (0 : ℝ)..H, G τ := by
    have := intervalIntegral.integral_comp_sub_left (f := G) (a := (0 : ℝ)) (b := H) H
    rw [sub_self, sub_zero] at this
    exact this
  have hleft_sub :
      (∫ v in (0 : ℝ)..H, G (-v)) = ∫ τ in (-H)..(0 : ℝ), G τ := by
    have hcomp : (∫ v in (0 : ℝ)..H, G (0 - v)) = ∫ τ in (0 : ℝ) - H..(0 : ℝ) - 0, G τ :=
      intervalIntegral.integral_comp_sub_left (f := G) (a := (0 : ℝ)) (b := H) 0
    rw [show (0 : ℝ) - H = -H by ring, show (0 : ℝ) - 0 = (0 : ℝ) by ring] at hcomp
    have hcongr : (∫ v in (0 : ℝ)..H, G (-v)) = ∫ v in (0 : ℝ)..H, G (0 - v) := by
      apply intervalIntegral.integral_congr
      intro v _hv
      show G (-v) = G (0 - v)
      rw [zero_sub]
    rw [hcongr, hcomp]
  -- Split the triangle-kernel integral at 0 and rewrite |τ| on each half.
  have hint : ∀ a b : ℝ,
      IntervalIntegrable (fun τ => (H - |τ|) * f τ) volume a b :=
    fun a b => (((continuous_const.sub continuous_id.abs).mul hf)).intervalIntegrable _ _
  have hsplit0 :
      (∫ τ in (-H)..H, (H - |τ|) * f τ) =
        (∫ τ in (-H)..(0 : ℝ), (H - |τ|) * f τ) +
          ∫ τ in (0 : ℝ)..H, (H - |τ|) * f τ := by
    have h1 := intervalIntegral.integral_interval_sub_left (hint (-H) H) (hint (-H) 0)
    have hs := intervalIntegral.integral_symm
      (f := fun τ => (H - |τ|) * f τ) (μ := volume) (0 : ℝ) H
    linarith
  have hleft_abs :
      (∫ τ in (-H)..(0 : ℝ), (H - |τ|) * f τ) =
        ∫ τ in (-H)..(0 : ℝ), (H + τ) * f τ := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    have hτ0 : τ ≤ 0 := by
      have hle : -H ≤ (0 : ℝ) := by linarith
      rw [uIcc_of_le hle] at hτ
      exact (mem_Icc.mp hτ).2
    show (H - |τ|) * f τ = (H + τ) * f τ
    rw [abs_of_nonpos hτ0, sub_neg_eq_add]
  have hright_abs :
      (∫ τ in (0 : ℝ)..H, (H - |τ|) * f τ) =
        ∫ τ in (0 : ℝ)..H, (H - τ) * f τ := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    have hτ0 : (0 : ℝ) ≤ τ := by
      rw [uIcc_of_le hH] at hτ
      exact (mem_Icc.mp hτ).1
    show (H - |τ|) * f τ = (H - τ) * f τ
    rw [abs_of_nonneg hτ0]
  -- Final assembly.
  calc
    (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, f (w - v))
      = ∫ v in (0 : ℝ)..H, (G (H - v) - G (-v)) := by
        apply intervalIntegral.integral_congr
        intro v _hv
        show (∫ w in (0 : ℝ)..H, f (w - v)) = G (H - v) - G (-v)
        exact hsub v
    _ = (∫ v in (0 : ℝ)..H, G (H - v)) - ∫ v in (0 : ℝ)..H, G (-v) :=
        intervalIntegral.integral_sub
          ((hGcont.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _)
          ((hGcont.comp continuous_neg).intervalIntegrable _ _)
    _ = (∫ τ in (0 : ℝ)..H, G τ) - ∫ τ in (-H)..(0 : ℝ), G τ := by
        rw [hright_sub, hleft_sub]
    _ = ∫ τ in (-H)..H, (H - |τ|) * f τ := by
        rw [hsplit0, hleft_abs, hright_abs, hleft, hright]
        ring

end MathlibAux
