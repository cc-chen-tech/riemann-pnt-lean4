import HardyTheorem.OscillatoryIntegral
import Mathlib.Analysis.Calculus.MeanValue

open Set

namespace HardyTheorem.OscillatoryIntegral

/-- The real logarithm is `1 / T`-Lipschitz on `[T, ∞)` when `T > 0`. -/
theorem abs_log_sub_log_le_div
    {T x y : ℝ} (hT : 0 < T) (hx : T ≤ x) (hy : T ≤ y) :
    |Real.log y - Real.log x| ≤ |y - x| / T := by
  have hdiff : ∀ z ∈ Ici T, DifferentiableAt ℝ Real.log z := by
    intro z hz
    exact Real.differentiableAt_log (ne_of_gt (hT.trans_le hz))
  have hderiv : ∀ z ∈ Ici T, ‖deriv Real.log z‖ ≤ 1 / T := by
    intro z hz
    have hzpos : 0 < z := hT.trans_le hz
    rw [Real.deriv_log, Real.norm_eq_abs, abs_inv, abs_of_pos hzpos]
    simpa only [one_div] using one_div_le_one_div_of_le hT hz
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hderiv (convex_Ici T) hx hy
  simpa only [Real.norm_eq_abs, div_eq_mul_inv, one_mul, mul_one, mul_comm] using h

/-- The phase occurring in a shifted cross term of the Hardy first model. -/
noncomputable def hardyPhaseCorrelation
    (m n : ℕ) (v w t : ℝ) : ℝ :=
  hardyPhase m (t + v) - hardyPhase n (t + w)

/-- The first derivative of a shifted Hardy-phase correlation. -/
theorem deriv_hardyPhaseCorrelation
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    deriv (hardyPhaseCorrelation m n v w) t =
      (1 / 2) * Real.log
          ((t + v) / (2 * Real.pi * ((m : ℝ) ^ 2))) -
        (1 / 2) * Real.log
          ((t + w) / (2 * Real.pi * ((n : ℝ) ^ 2))) := by
  have hmDiff : DifferentiableAt ℝ (fun x : ℝ => hardyPhase m (x + v)) t :=
    by
      simpa [Function.comp_def] using
        (((contDiffAt_hardyPhase_two hm htv).differentiableAt (by norm_num)).comp t
          ((hasDerivAt_id t).add_const v).differentiableAt)
  have hnDiff : DifferentiableAt ℝ (fun x : ℝ => hardyPhase n (x + w)) t :=
    by
      simpa [Function.comp_def] using
        (((contDiffAt_hardyPhase_two hn htw).differentiableAt (by norm_num)).comp t
          ((hasDerivAt_id t).add_const w).differentiableAt)
  unfold hardyPhaseCorrelation
  rw [deriv_fun_sub hmDiff hnDiff, deriv_comp_add_const,
    deriv_comp_add_const, deriv_hardyPhase hm htv,
    deriv_hardyPhase hn htw]

/-- The second derivative of a shifted Hardy-phase correlation is the
difference of two reciprocal heights. In particular, the dependence on the
Dirichlet indices disappears after two derivatives. -/
theorem iteratedDeriv_two_hardyPhaseCorrelation
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    iteratedDeriv 2 (hardyPhaseCorrelation m n v w) t =
      1 / (2 * (t + v)) - 1 / (2 * (t + w)) := by
  have hmCont : ContDiffAt ℝ 2 (fun x : ℝ => hardyPhase m (x + v)) t :=
    (contDiffAt_hardyPhase_two hm htv).comp t
      (contDiffAt_id.add contDiffAt_const)
  have hnCont : ContDiffAt ℝ 2 (fun x : ℝ => hardyPhase n (x + w)) t :=
    (contDiffAt_hardyPhase_two hn htw).comp t
      (contDiffAt_id.add contDiffAt_const)
  unfold hardyPhaseCorrelation
  rw [iteratedDeriv_fun_sub hmCont hnCont]
  rw [show iteratedDeriv 2 (fun x : ℝ => hardyPhase m (x + v)) t =
      iteratedDeriv 2 (hardyPhase m) (t + v) by
        exact congrFun (iteratedDeriv_comp_add_const
          (n := 2) (f := hardyPhase m) (s := v)) t]
  rw [show iteratedDeriv 2 (fun x : ℝ => hardyPhase n (x + w)) t =
      iteratedDeriv 2 (hardyPhase n) (t + w) by
        exact congrFun (iteratedDeriv_comp_add_const
          (n := 2) (f := hardyPhase n) (s := w)) t]
  rw [iteratedDeriv_two_hardyPhase hm htv,
    iteratedDeriv_two_hardyPhase hn htw]

/-- With equal shifts, the nonlinear common phase cancels completely: the
correlation derivative is the constant logarithmic frequency gap. -/
theorem deriv_hardyPhaseCorrelation_same_shift
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {v t : ℝ} (htv : 0 < t + v) :
    deriv (hardyPhaseCorrelation m n v v) t =
      Real.log n - Real.log m := by
  rw [deriv_hardyPhaseCorrelation hm hn htv htv]
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have htpos : 0 < t + v := htv
  rw [Real.log_div (ne_of_gt htpos) (by positivity),
    Real.log_div (ne_of_gt htpos) (by positivity)]
  rw [Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (by positivity : (m : ℝ) ^ 2 ≠ 0),
    Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (by positivity : (n : ℝ) ^ 2 ≠ 0)]
  rw [Real.log_pow]
  rw [Real.log_pow]
  ring

/-- A shifted correlation derivative is its logarithmic frequency gap plus
a height-shift correction. -/
theorem deriv_hardyPhaseCorrelation_eq_log_gap_add
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {v w t : ℝ} (htv : 0 < t + v) (htw : 0 < t + w) :
    deriv (hardyPhaseCorrelation m n v w) t =
      (Real.log n - Real.log m) +
        (1 / 2) * (Real.log (t + v) - Real.log (t + w)) := by
  rw [deriv_hardyPhaseCorrelation hm hn htv htw]
  rw [Real.log_div (ne_of_gt htv) (by positivity),
    Real.log_div (ne_of_gt htw) (by positivity)]
  rw [Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (by positivity : (m : ℝ) ^ 2 ≠ 0),
    Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (by positivity : (n : ℝ) ^ 2 ≠ 0)]
  rw [Real.log_pow, Real.log_pow]
  ring

/-- On a positive-height strip, shifting the two arguments changes the
correlation frequency by at most `|v-w| / (2T)`. -/
theorem abs_deriv_hardyPhaseCorrelation_sub_log_gap_le
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {T v w t : ℝ} (hT : 0 < T)
    (htv : T ≤ t + v) (htw : T ≤ t + w) :
    |deriv (hardyPhaseCorrelation m n v w) t -
        (Real.log n - Real.log m)| ≤
      |v - w| / (2 * T) := by
  have htvpos : 0 < t + v := hT.trans_le htv
  have htwpos : 0 < t + w := hT.trans_le htw
  rw [deriv_hardyPhaseCorrelation_eq_log_gap_add hm hn htvpos htwpos]
  have hlog := abs_log_sub_log_le_div hT htw htv
  calc
    |(Real.log n - Real.log m +
          1 / 2 * (Real.log (t + v) - Real.log (t + w))) -
        (Real.log n - Real.log m)| =
        (1 / 2) * |Real.log (t + v) - Real.log (t + w)| := by
      rw [show (Real.log n - Real.log m +
          1 / 2 * (Real.log (t + v) - Real.log (t + w))) -
          (Real.log n - Real.log m) =
          1 / 2 * (Real.log (t + v) - Real.log (t + w)) by ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2) * (|(t + v) - (t + w)| / T) := by
      gcongr
    _ = |v - w| / (2 * T) := by
      rw [show (t + v) - (t + w) = v - w by ring]
      field_simp

private theorem monotoneOn_deriv_of_iteratedDeriv_two_nonneg
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
      exact ((hF z hz).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt)
    (by
      intro z hz
      exact (((hF z (interior_subset hz)).derivWithin (m := 1)
        (by norm_num)).differentiableAt (by norm_num)).differentiableWithinAt)
    hsecond' x hx y hy hxy
  simpa using hgrowth

private theorem antitoneOn_deriv_of_iteratedDeriv_two_nonpos
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
      exact ((hF z hz).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt)
    (by
      intro z hz
      exact (((hF z (interior_subset hz)).derivWithin (m := 1)
        (by norm_num)).differentiableAt (by norm_num)).differentiableWithinAt)
    hsecond' x hx y hy hxy
  simpa using hgrowth

/-- Away from the shifted diagonal, a Hardy-phase cross term has the same
reciprocal logarithmic-gap bound as a linear exponential. -/
theorem norm_integral_cexp_hardyPhaseCorrelation_le_of_log_gap
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {T a b v w : ℝ} (hT : 0 < T) (hab : a ≤ b) (hTa : T ≤ a)
    (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hgap : 0 < |Real.log n - Real.log m|)
    (hshift : |v - w| / (2 * T) ≤
      |Real.log n - Real.log m| / 2) :
    ‖∫ t in a..b,
        Complex.exp (Complex.I * hardyPhaseCorrelation m n v w t)‖ ≤
      8 / |Real.log n - Real.log m| := by
  let F : ℝ → ℝ := hardyPhaseCorrelation m n v w
  have hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 2 F x := by
    intro x hx
    have hxv : 0 < x + v := by linarith [hT, hTa, hx.1]
    have hxw : 0 < x + w := by linarith [hT, hTa, hx.1]
    have hmCont : ContDiffAt ℝ 2 (fun y : ℝ => hardyPhase m (y + v)) x := by
      simpa [Function.comp_def] using
        (contDiffAt_hardyPhase_two hm hxv).comp x
          (contDiffAt_id.add contDiffAt_const)
    have hnCont : ContDiffAt ℝ 2 (fun y : ℝ => hardyPhase n (y + w)) x := by
      simpa [Function.comp_def] using
        (contDiffAt_hardyPhase_two hn hxw).comp x
          (contDiffAt_id.add contDiffAt_const)
    exact hmCont.sub hnCont
  have hmono : MonotoneOn (deriv F) (Icc a b) ∨
      AntitoneOn (deriv F) (Icc a b) := by
    rcases le_total v w with hvw | hwv
    · left
      apply monotoneOn_deriv_of_iteratedDeriv_two_nonneg hF
      intro x hx
      have hxvpos : 0 < x + v := by linarith [hT, hTa, hx.1]
      have hxwpos : 0 < x + w := by linarith [hT, hTa, hx.1]
      rw [iteratedDeriv_two_hardyPhaseCorrelation hm hn hxvpos hxwpos]
      · apply sub_nonneg.mpr
        apply one_div_le_one_div_of_le
        · exact mul_pos (by norm_num) hxvpos
        · nlinarith
    · right
      apply antitoneOn_deriv_of_iteratedDeriv_two_nonpos hF
      intro x hx
      have hxvpos : 0 < x + v := by linarith [hT, hTa, hx.1]
      have hxwpos : 0 < x + w := by linarith [hT, hTa, hx.1]
      rw [iteratedDeriv_two_hardyPhaseCorrelation hm hn hxvpos hxwpos]
      · apply sub_nonpos.mpr
        apply one_div_le_one_div_of_le
        · exact mul_pos (by norm_num) hxwpos
        · nlinarith
  have haway : ∀ x ∈ Icc a b,
      |Real.log n - Real.log m| / 2 ≤ |deriv F x| := by
    intro x hx
    have hxv : T ≤ x + v := by linarith [hTa, hx.1]
    have hxw : T ≤ x + w := by linarith [hTa, hx.1]
    have herr := abs_deriv_hardyPhaseCorrelation_sub_log_gap_le
      hm hn hT hxv hxw
    have htriangle : |Real.log n - Real.log m| ≤
        |deriv F x - (Real.log n - Real.log m)| + |deriv F x| := by
      calc
        |Real.log n - Real.log m| =
            |(Real.log n - Real.log m - deriv F x) + deriv F x| := by ring_nf
        _ ≤ |Real.log n - Real.log m - deriv F x| + |deriv F x| := abs_add_le _ _
        _ = |deriv F x - (Real.log n - Real.log m)| + |deriv F x| := by
          rw [abs_sub_comm]
    nlinarith
  have hbound := norm_integral_cexp_phase_le_of_monotone_deriv_local
    hab (half_pos hgap) hF hmono haway
  calc
    ‖∫ t in a..b,
        Complex.exp (Complex.I * hardyPhaseCorrelation m n v w t)‖ ≤
        4 / (|Real.log n - Real.log m| / 2) := by
      simpa only [F] using hbound
    _ = 8 / |Real.log n - Real.log m| := by
      field_simp [ne_of_gt hgap]
      norm_num

/-- Over a positive-height short window, the instantaneous frequency of one
Hardy phase moves by at most `v / (2T)` from its value at the left endpoint. -/
theorem abs_deriv_shifted_hardyPhase_sub_base_le
    {n : ℕ} (hn : n ≠ 0) {T t v : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hv : 0 ≤ v) :
    |deriv (fun x : ℝ => hardyPhase n (x + t)) v -
        deriv (hardyPhase n) t| ≤ v / (2 * T) := by
  have htpos : 0 < t := hT.trans_le hTt
  have htvpos : 0 < v + t := by linarith
  rw [deriv_comp_add_const, deriv_hardyPhase hn htvpos,
    deriv_hardyPhase hn htpos]
  have hlog := abs_log_sub_log_le_div hT hTt (by linarith : T ≤ v + t)
  have hden : 0 < 2 * Real.pi * (n : ℝ) ^ 2 := by positivity
  rw [Real.log_div (ne_of_gt htvpos) (ne_of_gt hden),
    Real.log_div (ne_of_gt htpos) (ne_of_gt hden)]
  calc
    |1 / 2 * (Real.log (v + t) - Real.log (2 * Real.pi * (n : ℝ) ^ 2)) -
        1 / 2 * (Real.log t - Real.log (2 * Real.pi * (n : ℝ) ^ 2))| =
        (1 / 2) * |Real.log (v + t) - Real.log t| := by
      rw [show 1 / 2 * (Real.log (v + t) -
            Real.log (2 * Real.pi * (n : ℝ) ^ 2)) -
          1 / 2 * (Real.log t - Real.log (2 * Real.pi * (n : ℝ) ^ 2)) =
          (1 / 2) * (Real.log (v + t) - Real.log t) by ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2) * (|(v + t) - t| / T) := by gcongr
    _ = v / (2 * T) := by
      rw [show (v + t) - t = v by ring, abs_of_nonneg hv]
      field_simp

/-- Away from its stationary point, the short integral of one Hardy phase is
bounded by the reciprocal base frequency.  The shift hypothesis makes the
bound uniform throughout the whole short window. -/
theorem norm_integral_cexp_shifted_hardyPhase_le_of_base_frequency
    {n : ℕ} (hn : n ≠ 0) {T t delta : ℝ}
    (hT : 0 < T) (hTt : T ≤ t) (hdelta : 0 ≤ delta)
    (hgap : 0 < |deriv (hardyPhase n) t|)
    (hshift : delta / (2 * T) ≤ |deriv (hardyPhase n) t| / 2) :
    ‖∫ v in 0..delta,
        Complex.exp (Complex.I * hardyPhase n (t + v))‖ ≤
      8 / |deriv (hardyPhase n) t| := by
  let F : ℝ → ℝ := fun v => hardyPhase n (v + t)
  have hF : ∀ x ∈ Icc (0 : ℝ) delta, ContDiffAt ℝ 2 F x := by
    intro x hx
    have hxtpos : 0 < x + t := by linarith [hT, hTt, hx.1]
    simpa only [F] using
      (contDiffAt_hardyPhase_two hn hxtpos).comp x
        (contDiffAt_id.add contDiffAt_const)
  have hmono : MonotoneOn (deriv F) (Icc (0 : ℝ) delta) := by
    apply monotoneOn_deriv_of_iteratedDeriv_two_nonneg hF
    intro x hx
    have hxtpos : 0 < x + t := by linarith [hT, hTt, hx.1]
    rw [show iteratedDeriv 2 F x =
        iteratedDeriv 2 (hardyPhase n) (x + t) by
      exact congrFun (iteratedDeriv_comp_add_const
        (n := 2) (f := hardyPhase n) (s := t)) x]
    rw [iteratedDeriv_two_hardyPhase hn hxtpos]
    positivity
  have haway : ∀ x ∈ Icc (0 : ℝ) delta,
      |deriv (hardyPhase n) t| / 2 ≤ |deriv F x| := by
    intro x hx
    have herr := abs_deriv_shifted_hardyPhase_sub_base_le
      hn hT hTt hx.1
    have hxshift : x / (2 * T) ≤ |deriv (hardyPhase n) t| / 2 := by
      exact (div_le_div_of_nonneg_right hx.2 (by positivity)).trans hshift
    have htriangle : |deriv (hardyPhase n) t| ≤
        |deriv F x - deriv (hardyPhase n) t| + |deriv F x| := by
      calc
        |deriv (hardyPhase n) t| =
            |(deriv (hardyPhase n) t - deriv F x) + deriv F x| := by ring_nf
        _ ≤ |deriv (hardyPhase n) t - deriv F x| + |deriv F x| :=
          abs_add_le _ _
        _ = |deriv F x - deriv (hardyPhase n) t| + |deriv F x| := by
          rw [abs_sub_comm]
    dsimp only [F] at herr ⊢
    nlinarith
  have hbound := norm_integral_cexp_phase_le_of_monotone_deriv_local
    hdelta (half_pos hgap) hF (Or.inl hmono) haway
  calc
    ‖∫ v in 0..delta,
        Complex.exp (Complex.I * hardyPhase n (t + v))‖ =
        ‖∫ v in 0..delta, Complex.exp (Complex.I * F v)‖ := by
      apply congrArg norm
      apply intervalIntegral.integral_congr
      intro v _hv
      simp only [F, add_comm]
    _ ≤ 4 / (|deriv (hardyPhase n) t| / 2) := hbound
    _ = 8 / |deriv (hardyPhase n) t| := by
      field_simp [ne_of_gt hgap]
      norm_num

end HardyTheorem.OscillatoryIntegral
