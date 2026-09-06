import HardyTheorem.SelbergFirstMomentStirling
import HardyTheorem.SelbergMollifierNonvanishing
import MathlibAux.RectangleResidue

open Complex MeasureTheory Set
open scoped Interval

namespace HardyTheorem

/-!
# The finite S4 first-moment rectangle

The auxiliary product `zeta(s) * psi_X(s)^2` is holomorphic on every
rectangle whose lower height is at least one.  Cauchy's theorem then gives
the exact relation between the critical edge, the right edge, and the two
horizontal edges.  This module fixes all orientation signs before any
asymptotic estimates are inserted.
-/

/-- The S4 auxiliary product is holomorphic on the complete first-moment
rectangle once the rectangle lies above the pole at `s = 1`. -/
theorem differentiableOn_selbergFirstMomentAuxiliary_rectangle
    (X : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    DifferentiableOn ℂ (selbergFirstMomentAuxiliary X)
      ([[1 / 2, 2]] ×ℂ [[a, b]]) := by
  intro s hs
  have hsre : s.re ∈ [[(1 / 2 : ℝ), 2]] := by
    simpa [mem_reProdIm] using hs.1
  have hsim : s.im ∈ [[a, b]] := by
    simpa [mem_reProdIm] using hs.2
  have hs1 : s ≠ 1 := by
    intro hsone
    have him : s.im = 0 := by rw [hsone]; simp
    rw [uIcc_of_le hab] at hsim
    have ha0 : a ≤ 0 := by rw [← him]; exact hsim.1
    linarith
  have hM : DifferentiableAt ℂ (selbergSqrtZetaMollifier X) s := by
    unfold selbergSqrtZetaMollifier
    exact ((analyticOnNhd_selbergMollifier X
      (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))) s
        (Set.mem_univ s)).differentiableAt
  unfold selbergFirstMomentAuxiliary
  exact (((differentiableAt_riemannZeta hs1).mul hM).mul hM).differentiableWithinAt

/-- Cauchy's theorem for the S4 first-moment auxiliary product. -/
theorem boundaryRectIntegral_selbergFirstMomentAuxiliary_eq_zero
    (X : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    MathlibAux.boundaryRectIntegral (selbergFirstMomentAuxiliary X)
      (1 / 2) 2 a b = 0 := by
  exact MathlibAux.boundaryRectIntegral_eq_zero_of_differentiableOn
    (selbergFirstMomentAuxiliary X) (1 / 2) 2 a b
      (differentiableOn_selbergFirstMomentAuxiliary_rectangle X ha hab)

/-- Exact orientation-resolved contour identity.  The critical vertical edge
equals the right vertical edge plus `I` times top minus bottom. -/
theorem intervalIntegral_selbergFirstMomentAuxiliary_criticalLine_eq_right_add_horizontal
    (X : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b,
        selbergFirstMomentAuxiliary X ((1 / 2 : ℂ) + I * t)) =
      (∫ t in a..b,
        selbergFirstMomentAuxiliary X ((2 : ℂ) + I * t)) +
      I * ((∫ sigma in (1 / 2 : ℝ)..2,
          selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * b)) -
        (∫ sigma in (1 / 2 : ℝ)..2,
          selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * a))) := by
  have hzero := boundaryRectIntegral_selbergFirstMomentAuxiliary_eq_zero
    X ha hab
  let B : ℂ := ∫ sigma in (1 / 2 : ℝ)..2,
    selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * a)
  let U : ℂ := ∫ sigma in (1 / 2 : ℝ)..2,
    selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * b)
  let R : ℂ := ∫ t in a..b,
    selbergFirstMomentAuxiliary X ((2 : ℂ) + I * t)
  let L : ℂ := ∫ t in a..b,
    selbergFirstMomentAuxiliary X ((1 / 2 : ℂ) + I * t)
  have hzero' : B - U + I * R - I * L = 0 := by
    simpa [MathlibAux.boundaryRectIntegral, smul_eq_mul, B, U, R, L,
      mul_comm] using hzero
  have hIL : I * L = B - U + I * R := by
    linear_combination -hzero'
  have hresult : L = R + I * (U - B) := by
    calc
      L = (-I) * (I * L) := by rw [← mul_assoc, neg_mul, I_mul_I]; ring
      _ = (-I) * (B - U + I * R) := by rw [hIL]
      _ = (-I) * (B - U) + ((-I) * I) * R := by ring
      _ = R + I * (U - B) := by
        have hnegII : (-I) * I = (1 : ℂ) := by
          rw [neg_mul, I_mul_I]
          norm_num
        rw [hnegII]
        ring
  exact hresult

/-- The exact contour identity together with the uniform right-edge remainder
gives a quantitative lower bound on the critical vertical edge.  This is the
finite-`T` form used before choosing the mollifier length: both horizontal
edges remain visible and no asymptotic notation is hidden in the statement. -/
theorem norm_intervalIntegral_selbergFirstMomentAuxiliary_criticalLine_lower
    {X : ℕ} (hX : 2 ≤ X) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (b - a) - 16 / Real.log 2 -
          ‖∫ sigma in (1 / 2 : ℝ)..2,
              selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * b)‖ -
        ‖∫ sigma in (1 / 2 : ℝ)..2,
              selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * a)‖ ≤
      ‖∫ t in a..b,
          selbergFirstMomentAuxiliary X ((1 / 2 : ℂ) + I * t)‖ := by
  let B : ℂ := ∫ sigma in (1 / 2 : ℝ)..2,
    selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * a)
  let U : ℂ := ∫ sigma in (1 / 2 : ℝ)..2,
    selbergFirstMomentAuxiliary X ((sigma : ℂ) + I * b)
  let R : ℂ := ∫ t in a..b,
    selbergFirstMomentAuxiliary X ((2 : ℂ) + I * t)
  let L : ℂ := ∫ t in a..b,
    selbergFirstMomentAuxiliary X ((1 / 2 : ℂ) + I * t)
  let E : ℂ := ∫ t in a..b,
    (selbergFirstMomentAuxiliary X ((2 : ℂ) + I * t) - 1)
  have hcontour : L = R + I * (U - B) := by
    simpa [B, U, R, L] using
      intervalIntegral_selbergFirstMomentAuxiliary_criticalLine_eq_right_add_horizontal
        X ha hab
  have hpath : Continuous (fun t : ℝ =>
      selbergFirstMomentAuxiliary X ((2 : ℂ) + I * t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hs1 : (2 : ℂ) + I * (t : ℂ) ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      norm_num at hre
    have hM : DifferentiableAt ℂ (selbergSqrtZetaMollifier X)
        ((2 : ℂ) + I * t) := by
      exact ((analyticOnNhd_selbergMollifier X
        (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ)))
          ((2 : ℂ) + I * t) (Set.mem_univ _)).differentiableAt
    have hG : ContinuousAt (selbergFirstMomentAuxiliary X)
        ((2 : ℂ) + I * t) := by
      unfold selbergFirstMomentAuxiliary
      exact (((differentiableAt_riemannZeta hs1).mul hM).mul hM).continuousAt
    exact hG.comp_of_eq (by fun_prop) rfl
  have hGint : IntervalIntegrable (fun t : ℝ =>
      selbergFirstMomentAuxiliary X ((2 : ℂ) + I * t)) volume a b :=
    hpath.intervalIntegrable a b
  have hsplit := intervalIntegral.integral_sub hGint
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume a b)
  have hER : E = R - ((b - a : ℝ) : ℂ) := by
    simpa [E, R] using hsplit
  have hE :=
    norm_intervalIntegral_selbergFirstMomentAuxiliary_rightLine_sub_one_le
      hX (a := a) (b := b)
  have hLm : L - ((b - a : ℝ) : ℂ) = E + I * (U - B) := by
    rw [hcontour, hER]
    ring
  have hdiff : ‖L - ((b - a : ℝ) : ℂ)‖ ≤
      16 / Real.log 2 + (‖U‖ + ‖B‖) := by
    rw [hLm]
    calc
      ‖E + I * (U - B)‖ ≤ ‖E‖ + ‖I * (U - B)‖ := norm_add_le _ _
      _ ≤ 16 / Real.log 2 + (‖U‖ + ‖B‖) := by
        rw [norm_mul, norm_I, one_mul]
        exact add_le_add hE (norm_sub_le U B)
  have hm : ‖((b - a : ℝ) : ℂ)‖ = b - a := by
    rw [Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hab)]
  have hreverse := norm_le_norm_add_norm_sub L ((b - a : ℝ) : ℂ)
  rw [hm] at hreverse
  change (b - a) - 16 / Real.log 2 - ‖U‖ - ‖B‖ ≤ ‖L‖
  linarith

/-- On a dyadic rectangle, the two horizontal errors can be inserted into the
finite contour lower bound uniformly.  The remaining error
`X * sqrt (T / 2)` is explicit; choosing `X = o(sqrt T)` is deliberately left
to the later Selberg parameter module. -/
theorem exists_norm_intervalIntegral_selbergFirstMomentAuxiliary_dyadic_lower :
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, ∀ X : ℕ,
        T0 ≤ T → 2 ≤ X →
        T / 2 - 16 / Real.log 2 -
              2 * C * X * Real.sqrt (T / 2) ≤
          ‖∫ t in T / 2..T,
              selbergFirstMomentAuxiliary X ((1 / 2 : ℂ) + I * t)‖ := by
  obtain ⟨C, S0, hC, hS0, hhorizontal⟩ :=
    exists_norm_intervalIntegral_selbergFirstMomentAuxiliary_horizontal_le
  refine ⟨C, 2 * S0, hC, by linarith, ?_⟩
  intro T X hT hX
  have hTnonneg : 0 ≤ T := by linarith [hS0]
  have hhalfnonneg : 0 ≤ T / 2 := by positivity
  have hscale : S0 ≤ T / 2 := by linarith
  have habsT : |T| = T := abs_of_nonneg hTnonneg
  have habshalf : |T / 2| = T / 2 := abs_of_nonneg hhalfnonneg
  have hbottom := hhorizontal (T / 2) (T / 2) X hscale
    (by rw [habshalf]) (by rw [habshalf]; linarith) hX
  have htop := hhorizontal (T / 2) T X hscale
    (by rw [habsT]; linarith) (by rw [habsT]; ring_nf; exact le_rfl) hX
  have hcontour :=
    norm_intervalIntegral_selbergFirstMomentAuxiliary_criticalLine_lower
      hX (a := T / 2) (b := T) (by linarith [hS0]) (by linarith)
  linarith

end HardyTheorem
