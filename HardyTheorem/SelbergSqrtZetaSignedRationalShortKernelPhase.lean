import HardyTheorem.SelbergSqrtZetaSignedRationalShortKernel
import HardyTheorem.HardyPhaseCorrelation

/-!
# Phase velocity of the signed rational short kernel

The exact Hermitian kernel keeps a nonlinear theta phase.  Its height
derivative is the rational-frequency gap plus a slowly varying logarithmic
correction.  On a positive-height strip that correction is at most
`|v - w| / (2 * T)`.  This is the local input needed to separate stationary
and nonstationary frequency pairs without taking an absolute-value gap
majorant first.
-/

namespace HardyTheorem

open Set

/-- The height derivative of the exact rational short-kernel phase is its
rational-frequency gap plus the difference of the two theta velocities. -/
theorem deriv_selbergSqrtZetaSignedRationalShortKernelPhase
    (q r : ℚ) {v w t : ℝ}
    (htv : 0 < t + v) (htw : 0 < t + w) :
    deriv (selbergSqrtZetaSignedRationalShortKernelPhase q r v w) t =
      (selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r) +
        (1 / 2 : ℝ) * (Real.log (t + w) - Real.log (t + v)) := by
  have htheta (shift : ℝ) (hpos : 0 < t + shift) :
      HasDerivAt (fun x : ℝ => thetaModel (x + shift))
        ((1 / 2 : ℝ) * Real.log ((t + shift) / (2 * Real.pi))) t := by
    have hdiff : DifferentiableAt ℝ thetaModel (t + shift) := by
      change DifferentiableAt ℝ
        (fun y : ℝ =>
          y / 2 * Real.log (y / (2 * Real.pi)) -
            y / 2 - Real.pi / 8) (t + shift)
      fun_prop (disch := positivity)
    have hout := hdiff.hasDerivAt
    rw [deriv_thetaModel hpos] at hout
    simpa only [Function.comp_def, id_eq, mul_one] using
      hout.comp t ((hasDerivAt_id t).add_const shift)
  have hq :
      HasDerivAt
        (fun x : ℝ =>
          selbergSqrtZetaSignedRationalFrequency q * (x + w))
        (selbergSqrtZetaSignedRationalFrequency q) t := by
    simpa using
      ((hasDerivAt_id t).add_const w).const_mul
        (selbergSqrtZetaSignedRationalFrequency q)
  have hr :
      HasDerivAt
        (fun x : ℝ =>
          selbergSqrtZetaSignedRationalFrequency r * (x + v))
        (selbergSqrtZetaSignedRationalFrequency r) t := by
    simpa using
      ((hasDerivAt_id t).add_const v).const_mul
        (selbergSqrtZetaSignedRationalFrequency r)
  have hphase := ((htheta w htw).add hq).sub ((htheta v htv).add hr)
  have hphase' :
      HasDerivAt
        (fun x : ℝ =>
          thetaModel (x + w) +
              selbergSqrtZetaSignedRationalFrequency q * (x + w) -
            (thetaModel (x + v) +
              selbergSqrtZetaSignedRationalFrequency r * (x + v)))
        ((1 / 2 : ℝ) * Real.log ((t + w) / (2 * Real.pi)) +
            selbergSqrtZetaSignedRationalFrequency q -
          ((1 / 2 : ℝ) * Real.log ((t + v) / (2 * Real.pi)) +
            selbergSqrtZetaSignedRationalFrequency r)) t := by
    simpa only [Pi.add_apply, Pi.sub_apply] using hphase
  unfold selbergSqrtZetaSignedRationalShortKernelPhase
  rw [hphase'.deriv]
  rw [Real.log_div (ne_of_gt htw) (by positivity),
    Real.log_div (ne_of_gt htv) (by positivity)]
  ring

/-- The second height derivative is independent of the rational frequencies;
only the two short-window shifts remain. -/
theorem iteratedDeriv_two_selbergSqrtZetaSignedRationalShortKernelPhase
    (q r : ℚ) {v w t : ℝ}
    (htv : 0 < t + v) (htw : 0 < t + w) :
    iteratedDeriv 2
        (selbergSqrtZetaSignedRationalShortKernelPhase q r v w) t =
      1 / (2 * (t + w)) - 1 / (2 * (t + v)) := by
  have htheta :
      thetaModel = OscillatoryIntegral.hardyPhase 1 := by
    funext x
    simp [thetaModel, OscillatoryIntegral.hardyPhase]
    ring
  have hwCont : ContDiffAt ℝ 2
      (fun x : ℝ => OscillatoryIntegral.hardyPhase 1 (x + w)) t :=
    (OscillatoryIntegral.contDiffAt_hardyPhase_two (by norm_num) htw).comp t
      (contDiffAt_id.add contDiffAt_const)
  have hvCont : ContDiffAt ℝ 2
      (fun x : ℝ => OscillatoryIntegral.hardyPhase 1 (x + v)) t :=
    (OscillatoryIntegral.contDiffAt_hardyPhase_two (by norm_num) htv).comp t
      (contDiffAt_id.add contDiffAt_const)
  let linear : ℝ → ℝ := fun x =>
    selbergSqrtZetaSignedRationalFrequency q * (x + w) -
      selbergSqrtZetaSignedRationalFrequency r * (x + v)
  have hlinear : ContDiffAt ℝ 2 linear t := by
    dsimp only [linear]
    fun_prop
  have hlinearTwo : iteratedDeriv 2 linear t = 0 := by
    rw [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
    have hfirst :
        deriv linear =
          fun _ =>
            selbergSqrtZetaSignedRationalFrequency q -
              selbergSqrtZetaSignedRationalFrequency r := by
      funext x
      have hder :
          HasDerivAt linear
            (selbergSqrtZetaSignedRationalFrequency q -
              selbergSqrtZetaSignedRationalFrequency r) x := by
        simpa only [linear, id_eq, Pi.sub_apply, mul_one] using
          (((hasDerivAt_id x).add_const w).const_mul
            (selbergSqrtZetaSignedRationalFrequency q)).sub
          (((hasDerivAt_id x).add_const v).const_mul
            (selbergSqrtZetaSignedRationalFrequency r))
      exact hder.deriv
    rw [hfirst]
    simp
  unfold selbergSqrtZetaSignedRationalShortKernelPhase
  rw [htheta]
  rw [show
      (fun x : ℝ =>
        OscillatoryIntegral.hardyPhase 1 (x + w) +
            selbergSqrtZetaSignedRationalFrequency q * (x + w) -
          (OscillatoryIntegral.hardyPhase 1 (x + v) +
            selbergSqrtZetaSignedRationalFrequency r * (x + v))) =
        fun x : ℝ =>
          (OscillatoryIntegral.hardyPhase 1 (x + w) -
            OscillatoryIntegral.hardyPhase 1 (x + v)) + linear x by
      funext x
      dsimp only [linear]
      ring]
  rw [iteratedDeriv_fun_add (hwCont.sub hvCont) hlinear,
    iteratedDeriv_fun_sub hwCont hvCont]
  rw [show iteratedDeriv 2
          (fun x : ℝ => OscillatoryIntegral.hardyPhase 1 (x + w)) t =
        iteratedDeriv 2 (OscillatoryIntegral.hardyPhase 1) (t + w) by
      exact congrFun (iteratedDeriv_comp_add_const
        (n := 2) (f := OscillatoryIntegral.hardyPhase 1) (s := w)) t]
  rw [show iteratedDeriv 2
          (fun x : ℝ => OscillatoryIntegral.hardyPhase 1 (x + v)) t =
        iteratedDeriv 2 (OscillatoryIntegral.hardyPhase 1) (t + v) by
      exact congrFun (iteratedDeriv_comp_add_const
        (n := 2) (f := OscillatoryIntegral.hardyPhase 1) (s := v)) t]
  rw [OscillatoryIntegral.iteratedDeriv_two_hardyPhase (by norm_num) htw,
    OscillatoryIntegral.iteratedDeriv_two_hardyPhase (by norm_num) htv,
    hlinearTwo, add_zero]

/-- On a positive-height strip, the nonlinear theta contribution changes the
pure rational-frequency gap by at most `|v - w| / (2 * T)`. -/
theorem
    abs_deriv_selbergSqrtZetaSignedRationalShortKernelPhase_sub_frequencyGap_le
    (q r : ℚ) {T v w t : ℝ} (hT : 0 < T)
    (htv : T ≤ t + v) (htw : T ≤ t + w) :
    |deriv (selbergSqrtZetaSignedRationalShortKernelPhase q r v w) t -
        (selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r)| ≤
      |v - w| / (2 * T) := by
  have htvpos : 0 < t + v := hT.trans_le htv
  have htwpos : 0 < t + w := hT.trans_le htw
  rw [deriv_selbergSqrtZetaSignedRationalShortKernelPhase
    q r htvpos htwpos]
  have hlog :=
    OscillatoryIntegral.abs_log_sub_log_le_div hT htv htw
  calc
    |((selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r) +
          (1 / 2 : ℝ) * (Real.log (t + w) - Real.log (t + v))) -
        (selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r)| =
        (1 / 2 : ℝ) *
          |Real.log (t + w) - Real.log (t + v)| := by
      rw [show
          ((selbergSqrtZetaSignedRationalFrequency q -
              selbergSqrtZetaSignedRationalFrequency r) +
              (1 / 2 : ℝ) * (Real.log (t + w) - Real.log (t + v))) -
            (selbergSqrtZetaSignedRationalFrequency q -
              selbergSqrtZetaSignedRationalFrequency r) =
            (1 / 2 : ℝ) *
              (Real.log (t + w) - Real.log (t + v)) by ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2 : ℝ) * (|(t + w) - (t + v)| / T) := by
      gcongr
    _ = |v - w| / (2 * T) := by
      rw [show (t + w) - (t + v) = -(v - w) by ring, abs_neg]
      field_simp

/-- If the rational-frequency gap dominates the short-window scale, the exact
kernel phase is uniformly nonstationary and retains at least half that gap. -/
theorem
    half_abs_frequencyGap_le_abs_deriv_selbergSqrtZetaSignedRationalShortKernelPhase
    (q r : ℚ) {T H v w t : ℝ} (hT : 0 < T)
    (htv : T ≤ t + v) (htw : T ≤ t + w)
    (hvw : |v - w| ≤ H)
    (hsep :
      H / T ≤
        |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r|) :
    (1 / 2 : ℝ) *
        |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r| ≤
      |deriv
        (selbergSqrtZetaSignedRationalShortKernelPhase q r v w) t| := by
  let gap : ℝ :=
    selbergSqrtZetaSignedRationalFrequency q -
      selbergSqrtZetaSignedRationalFrequency r
  let velocity : ℝ :=
    deriv (selbergSqrtZetaSignedRationalShortKernelPhase q r v w) t
  have hperturb :
      |velocity - gap| ≤ |v - w| / (2 * T) := by
    simpa only [velocity, gap] using
      abs_deriv_selbergSqrtZetaSignedRationalShortKernelPhase_sub_frequencyGap_le
        q r hT htv htw
  have hwindow :
      |v - w| / (2 * T) ≤ H / (2 * T) :=
    div_le_div_of_nonneg_right hvw (by positivity : 0 ≤ 2 * T)
  have hscale :
      H / (2 * T) ≤ (1 / 2 : ℝ) * |gap| := by
    have hhalf :=
      mul_le_mul_of_nonneg_left hsep (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      H / (2 * T) = (1 / 2 : ℝ) * (H / T) := by
        field_simp
      _ ≤ (1 / 2 : ℝ) *
          |selbergSqrtZetaSignedRationalFrequency q -
            selbergSqrtZetaSignedRationalFrequency r| := hhalf
      _ = (1 / 2 : ℝ) * |gap| := rfl
  have herror : |velocity - gap| ≤ (1 / 2 : ℝ) * |gap| :=
    hperturb.trans (hwindow.trans hscale)
  have htriangle : |gap| ≤ |velocity - gap| + |velocity| := by
    calc
      |gap| = |-(velocity - gap) + velocity| := by
        congr 1
        ring
      _ ≤ |-(velocity - gap)| + |velocity| := abs_add_le _ _
      _ = |velocity - gap| + |velocity| := by rw [abs_neg]
  dsimp only [velocity, gap] at *
  linarith

private theorem monotoneOn_deriv_of_iteratedDeriv_two_nonneg_kernelPhase
    {F : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hsecond : ∀ x ∈ Icc a b, 0 ≤ iteratedDeriv 2 F x) :
    MonotoneOn (deriv F) (Icc a b) := by
  intro x hx y hy hxy
  have hsecond' : ∀ z ∈ interior (Icc a b),
      0 ≤ deriv (deriv F) z := by
    intro z hz
    simpa [show 2 = 1 + 1 by omega, iteratedDeriv_succ,
      iteratedDeriv_one] using hsecond z (interior_subset hz)
  have hgrowth := Convex.mul_sub_le_image_sub_of_le_deriv
    (convex_Icc a b)
    (by
      intro z hz
      exact ((hF z hz).derivWithin (m := 0)
        (by norm_num)).continuousAt.continuousWithinAt)
    (by
      intro z hz
      exact (((hF z (interior_subset hz)).derivWithin (m := 1)
        (by norm_num)).differentiableAt
          (by norm_num)).differentiableWithinAt)
    hsecond' x hx y hy hxy
  simpa using hgrowth

private theorem antitoneOn_deriv_of_iteratedDeriv_two_nonpos_kernelPhase
    {F : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x)
    (hsecond : ∀ x ∈ Icc a b, iteratedDeriv 2 F x ≤ 0) :
    AntitoneOn (deriv F) (Icc a b) := by
  intro x hx y hy hxy
  have hsecond' : ∀ z ∈ interior (Icc a b),
      deriv (deriv F) z ≤ 0 := by
    intro z hz
    simpa [show 2 = 1 + 1 by omega, iteratedDeriv_succ,
      iteratedDeriv_one] using hsecond z (interior_subset hz)
  have hgrowth := Convex.image_sub_le_mul_sub_of_deriv_le
    (convex_Icc a b)
    (by
      intro z hz
      exact ((hF z hz).derivWithin (m := 0)
        (by norm_num)).continuousAt.continuousWithinAt)
    (by
      intro z hz
      exact (((hF z (interior_subset hz)).derivWithin (m := 1)
        (by norm_num)).differentiableAt
          (by norm_num)).differentiableWithinAt)
    hsecond' x hx y hy hxy
  simpa using hgrowth

/-- Away from the short-window stationary band, the inner height integral in
the exact Hermitian kernel has reciprocal rational-frequency decay.  Unlike
the global gap budget, this estimate is applied before summing the complex
cross terms and therefore preserves their phase structure. -/
theorem
    norm_integral_cexp_selbergSqrtZetaSignedRationalShortKernelPhase_le_of_frequencyGap
    (q r : ℚ) {T a b H v w : ℝ}
    (hT : 0 < T) (hab : a ≤ b) (hTa : T ≤ a)
    (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hwindow : |v - w| ≤ H)
    (hgap :
      0 <
        |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r|)
    (hsep :
      H / T ≤
        |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r|) :
    ‖∫ t in a..b,
        Complex.exp
          (Complex.I *
            ((selbergSqrtZetaSignedRationalShortKernelPhase
              q r v w t : ℝ) : ℂ))‖ ≤
      8 /
        |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r| := by
  let F : ℝ → ℝ :=
    selbergSqrtZetaSignedRationalShortKernelPhase q r v w
  have htheta :
      thetaModel = OscillatoryIntegral.hardyPhase 1 := by
    funext x
    simp [thetaModel, OscillatoryIntegral.hardyPhase]
    ring
  have hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x := by
    intro x hx
    have hxv : 0 < x + v := by linarith [hT, hTa, hx.1]
    have hxw : 0 < x + w := by linarith [hT, hTa, hx.1]
    have hwCont : ContDiffAt ℝ 2
        (fun y : ℝ => OscillatoryIntegral.hardyPhase 1 (y + w)) x :=
      (OscillatoryIntegral.contDiffAt_hardyPhase_two
        (by norm_num) hxw).comp x
        (contDiffAt_id.add contDiffAt_const)
    have hvCont : ContDiffAt ℝ 2
        (fun y : ℝ => OscillatoryIntegral.hardyPhase 1 (y + v)) x :=
      (OscillatoryIntegral.contDiffAt_hardyPhase_two
        (by norm_num) hxv).comp x
        (contDiffAt_id.add contDiffAt_const)
    have hq : ContDiffAt ℝ 2
        (fun y : ℝ =>
          selbergSqrtZetaSignedRationalFrequency q * (y + w)) x := by
      fun_prop
    have hr : ContDiffAt ℝ 2
        (fun y : ℝ =>
          selbergSqrtZetaSignedRationalFrequency r * (y + v)) x := by
      fun_prop
    dsimp only [F]
    unfold selbergSqrtZetaSignedRationalShortKernelPhase
    rw [htheta]
    exact (hwCont.add hq).sub (hvCont.add hr)
  have hmono : MonotoneOn (deriv F) (Icc a b) ∨
      AntitoneOn (deriv F) (Icc a b) := by
    rcases le_total v w with hvw | hwv
    · right
      apply antitoneOn_deriv_of_iteratedDeriv_two_nonpos_kernelPhase hF
      intro x hx
      have hxv : 0 < x + v := by linarith [hT, hTa, hx.1]
      have hxw : 0 < x + w := by linarith [hT, hTa, hx.1]
      rw [show iteratedDeriv 2 F x =
          1 / (2 * (x + w)) - 1 / (2 * (x + v)) by
        exact
          iteratedDeriv_two_selbergSqrtZetaSignedRationalShortKernelPhase
            q r hxv hxw]
      apply sub_nonpos.mpr
      apply one_div_le_one_div_of_le
      · exact mul_pos (by norm_num) hxv
      · nlinarith
    · left
      apply monotoneOn_deriv_of_iteratedDeriv_two_nonneg_kernelPhase hF
      intro x hx
      have hxv : 0 < x + v := by linarith [hT, hTa, hx.1]
      have hxw : 0 < x + w := by linarith [hT, hTa, hx.1]
      rw [show iteratedDeriv 2 F x =
          1 / (2 * (x + w)) - 1 / (2 * (x + v)) by
        exact
          iteratedDeriv_two_selbergSqrtZetaSignedRationalShortKernelPhase
            q r hxv hxw]
      apply sub_nonneg.mpr
      apply one_div_le_one_div_of_le
      · exact mul_pos (by norm_num) hxw
      · nlinarith
  have haway : ∀ x ∈ Icc a b,
      |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r| / 2 ≤
        |deriv F x| := by
    intro x hx
    have hxv : T ≤ x + v := by linarith [hTa, hx.1]
    have hxw : T ≤ x + w := by linarith [hTa, hx.1]
    simpa only [F, div_eq_mul_inv, mul_comm, one_mul] using
      half_abs_frequencyGap_le_abs_deriv_selbergSqrtZetaSignedRationalShortKernelPhase
        q r hT hxv hxw hwindow hsep
  have hbound :=
    OscillatoryIntegral.norm_integral_cexp_phase_le_of_monotone_deriv_local
      hab (half_pos hgap) hF hmono haway
  calc
    ‖∫ t in a..b,
        Complex.exp
          (Complex.I *
            ((selbergSqrtZetaSignedRationalShortKernelPhase
              q r v w t : ℝ) : ℂ))‖ ≤
      4 /
          (|selbergSqrtZetaSignedRationalFrequency q -
              selbergSqrtZetaSignedRationalFrequency r| / 2) := by
      simpa only [F] using hbound
    _ = 8 /
        |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r| := by
      field_simp [ne_of_gt hgap]
      norm_num

end HardyTheorem
