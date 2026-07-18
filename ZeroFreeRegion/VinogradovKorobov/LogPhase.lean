import ZeroFreeRegion.VinogradovKorobov.FirstDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ZeroFreeRegion.VinogradovKorobov

/-- Difference between two unit-length logarithmic increments separated by
`h`. -/
noncomputable def logIncrementDifference (h x : ℝ) : ℝ :=
  (Real.log (x + 1) - Real.log x) -
    (Real.log (x + h + 1) - Real.log (x + h))

/-- Algebraic normal form of the logarithmic increment difference. -/
lemma logIncrementDifference_eq {h x : ℝ} (hx : 0 < x) (hh : 0 < h) :
    logIncrementDifference h x =
      Real.log (1 + h / (x * (x + h + 1))) := by
  have hx1 : x + 1 ≠ 0 := by positivity
  have hxh : x + h ≠ 0 := by positivity
  have hxh1 : x + h + 1 ≠ 0 := by positivity
  have hx0 : x ≠ 0 := hx.ne'
  rw [logIncrementDifference, ← Real.log_div hx1 hx0,
    ← Real.log_div hxh1 hxh]
  rw [← Real.log_div (div_ne_zero hx1 hx0) (div_ne_zero hxh1 hxh)]
  congr 1
  field_simp
  ring

lemma logIncrementDifference_pos {h x : ℝ} (hx : 0 < x) (hh : 0 < h) :
    0 < logIncrementDifference h x := by
  rw [logIncrementDifference_eq hx hh]
  apply Real.log_pos
  have hden : 0 < x * (x + h + 1) := by positivity
  exact lt_add_of_pos_right 1 (div_pos hh hden)

lemma logIncrementDifference_le_fraction {h x : ℝ} (hx : 0 < x) (hh : 0 < h) :
    logIncrementDifference h x ≤ h / (x * (x + h + 1)) := by
  rw [logIncrementDifference_eq hx hh]
  have hden : 0 < x * (x + h + 1) := by positivity
  have harg : 0 < 1 + h / (x * (x + h + 1)) :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hh.le hden.le)
  have hlog := Real.log_le_sub_one_of_pos harg
  linarith

/-- The logarithmic increment difference decreases as the base point moves to
the right. -/
lemma antitoneOn_logIncrementDifference {h : ℝ} (hh : 0 < h) :
    AntitoneOn (logIncrementDifference h) (Set.Ioi 0) := by
  intro x hx y hy hxy
  rw [logIncrementDifference_eq hy hh, logIncrementDifference_eq hx hh]
  have hxpos : 0 < x := hx
  have hypos : 0 < y := hy
  have hdx : 0 < x * (x + h + 1) := by positivity
  have hdy : 0 < y * (y + h + 1) := by positivity
  have hden : x * (x + h + 1) ≤ y * (y + h + 1) := by
    exact mul_le_mul hxy (by linarith) (by positivity) (by positivity)
  have hfrac : h / (y * (y + h + 1)) ≤ h / (x * (x + h + 1)) := by
    exact (div_le_div_iff₀ hdy hdx).2 (mul_le_mul_of_nonneg_left hden hh.le)
  exact Real.strictMonoOn_log.monotoneOn
    (by exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hh.le hdy.le))
    (by exact add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hh.le hdx.le))
    (add_le_add_right hfrac 1)

/-- The phase produced by conjugating a logarithmic phase against a shift by
`h`. -/
noncomputable def logarithmicCorrelationPhase (t : ℝ) (h n : ℕ) : ℝ :=
  t * (Real.log n - Real.log (n + h))

lemma logarithmicCorrelationPhase_forwardDifference (t : ℝ) (h n : ℕ) :
    logarithmicCorrelationPhase t h (n + 1) -
        logarithmicCorrelationPhase t h n =
      t * logIncrementDifference h n := by
  unfold logarithmicCorrelationPhase logIncrementDifference
  push_cast
  ring_nf

lemma logarithmicCorrelationPhase_forwardDifference_pos
    {t : ℝ} {h n : ℕ} (ht : 0 < t) (hh : 0 < h) (hn : 0 < n) :
    0 < logarithmicCorrelationPhase t h (n + 1) -
      logarithmicCorrelationPhase t h n := by
  rw [logarithmicCorrelationPhase_forwardDifference]
  exact mul_pos ht (logIncrementDifference_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hh))

lemma logarithmicCorrelationPhase_forwardDifference_le_fraction
    {t : ℝ} {h n : ℕ} (ht : 0 ≤ t) (hh : 0 < h) (hn : 0 < n) :
    logarithmicCorrelationPhase t h (n + 1) -
        logarithmicCorrelationPhase t h n ≤
      t * (h : ℝ) / ((n : ℝ) * ((n : ℝ) + h + 1)) := by
  rw [logarithmicCorrelationPhase_forwardDifference]
  have hcore := logIncrementDifference_le_fraction
    (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hh)
  apply (mul_le_mul_of_nonneg_left hcore ht).trans_eq
  ring

lemma logarithmicCorrelationPhase_forwardDifference_antitone
    {t : ℝ} {h n : ℕ} (ht : 0 ≤ t) (hh : 0 < h) (hn : 0 < n) :
    logarithmicCorrelationPhase t h (n + 2) -
        logarithmicCorrelationPhase t h (n + 1) ≤
      logarithmicCorrelationPhase t h (n + 1) -
        logarithmicCorrelationPhase t h n := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    logarithmicCorrelationPhase_forwardDifference,
    logarithmicCorrelationPhase_forwardDifference]
  apply mul_le_mul_of_nonneg_left _ ht
  have hanti := antitoneOn_logIncrementDifference (Nat.cast_pos.mpr hh)
  have hresult :
      logIncrementDifference (h : ℝ) ((n + 1 : ℕ) : ℝ) ≤
        logIncrementDifference (h : ℝ) (n : ℝ) :=
    hanti
      (by simpa only [Set.mem_Ioi] using Nat.cast_pos.mpr hn)
      (by
        simp only [Set.mem_Ioi]
        positivity)
      (by norm_cast; omega)
  exact hresult

/-- Every later logarithmic correlation increment is bounded by the increment
at the start of the block. -/
lemma logarithmicCorrelationPhase_forwardDifference_le_start
    {t : ℝ} {h m : ℕ} (k : ℕ) (ht : 0 ≤ t) (hh : 0 < h) (hm : 0 < m) :
    logarithmicCorrelationPhase t h (m + (k + 1)) -
        logarithmicCorrelationPhase t h (m + k) ≤
      logarithmicCorrelationPhase t h (m + 1) -
        logarithmicCorrelationPhase t h m := by
  rw [show m + (k + 1) = (m + k) + 1 by omega,
    logarithmicCorrelationPhase_forwardDifference,
    logarithmicCorrelationPhase_forwardDifference]
  apply mul_le_mul_of_nonneg_left _ ht
  have hanti := antitoneOn_logIncrementDifference (Nat.cast_pos.mpr hh)
  exact hanti
    (by simpa only [Set.mem_Ioi] using Nat.cast_pos.mpr hm)
    (by
      simp only [Set.mem_Ioi]
      positivity)
    (by norm_cast; omega)

/-- Kusmin--Landau applied to a shifted logarithmic correlation phase.  The
upper-turn hypothesis is the remaining nonresonance condition used when this
bound estimates van der Corput autocorrelations. -/
theorem logarithmicCorrelation_kusminLandau_endpoint_bound
    (t : ℝ) (h m N : ℕ) (ht : 0 < t) (hh : 0 < h) (hm : 0 < m)
    (hlt : ∀ k ≤ N,
      logarithmicCorrelationPhase t h (m + (k + 1)) -
        logarithmicCorrelationPhase t h (m + k) < 2 * Real.pi) :
    ‖∑ k ∈ Finset.range (N + 1),
        phaseTerm (fun j ↦ logarithmicCorrelationPhase t h (m + j)) k‖ ≤
      ‖(Complex.exp (Complex.I *
        ((logarithmicCorrelationPhase t h (m + 1) -
          logarithmicCorrelationPhase t h m : ℝ) : ℂ)) - 1)⁻¹‖ +
      ‖(Complex.exp (Complex.I *
        ((logarithmicCorrelationPhase t h (m + (N + 1)) -
          logarithmicCorrelationPhase t h (m + N) : ℝ) : ℂ)) - 1)⁻¹‖ +
      (Real.cot ((logarithmicCorrelationPhase t h (m + (N + 1)) -
          logarithmicCorrelationPhase t h (m + N)) / 2) -
        Real.cot ((logarithmicCorrelationPhase t h (m + 1) -
          logarithmicCorrelationPhase t h m) / 2)) / 2 := by
  let f : ℕ → ℝ := fun j ↦ logarithmicCorrelationPhase t h (m + j)
  apply kusminLandau_endpoint_bound_antitone f N
  · intro k hk
    simpa only [f, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
      logarithmicCorrelationPhase_forwardDifference_pos ht hh (by omega : 0 < m + k)
  · intro k hk
    simpa only [f, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using hlt k hk
  · intro k hk
    simpa only [f, Nat.add_zero, Nat.zero_add, Nat.add_assoc] using
      logarithmicCorrelationPhase_forwardDifference_antitone ht.le hh (by omega : 0 < m + k)

end ZeroFreeRegion.VinogradovKorobov
