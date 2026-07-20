import PrimeNumberTheorem.RiemannVonMangoldt.GoodHeightAsymptotic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

/-- Derivative of the main term in the Riemann-von Mangoldt formula. -/
theorem hasDerivAt_riemannVonMangoldtMainTerm
    {T : ℝ} (hT : T ≠ 0) :
    HasDerivAt riemannVonMangoldtMainTerm
      (Real.log (T / (2 * Real.pi)) / (2 * Real.pi)) T := by
  have hc : 2 * Real.pi ≠ 0 := by positivity
  have harg : T / (2 * Real.pi) ≠ 0 := div_ne_zero hT hc
  have hlinear : HasDerivAt (fun x : ℝ => x / (2 * Real.pi))
      (1 / (2 * Real.pi)) T := by
    convert (hasDerivAt_id T).div_const (2 * Real.pi) using 1
  have hlog := hlinear.log harg
  unfold riemannVonMangoldtMainTerm
  convert (hlinear.mul hlog).sub hlinear using 1
  field_simp [hT, hc]
  ring

private theorem abs_mainTerm_sub_le_log_of_unit_interval
    {a b H : ℝ} (ha : 7 ≤ a) (hab : a < b)
    (hbH : b ≤ H) (hwidth : b - a ≤ 1) :
    |riemannVonMangoldtMainTerm b - riemannVonMangoldtMainTerm a| ≤
      Real.log (H + 5) := by
  let d : ℝ → ℝ := fun x =>
    Real.log (x / (2 * Real.pi)) / (2 * Real.pi)
  have hcont : ContinuousOn riemannVonMangoldtMainTerm (Set.Icc a b) := by
    intro x hx
    exact (hasDerivAt_riemannVonMangoldtMainTerm
      (by linarith [hx.1])).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt riemannVonMangoldtMainTerm (d x) x := by
    intro x hx
    exact hasDerivAt_riemannVonMangoldtMainTerm (by linarith [hx.1])
  rcases exists_hasDerivAt_eq_slope
      riemannVonMangoldtMainTerm d hab hcont hderiv with ⟨c, hc, hslope⟩
  have hpiOne : 1 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hpiSeven : 2 * Real.pi < 7 := by
    nlinarith [Real.pi_lt_d2]
  have hcpos : 0 < c := by linarith [hc.1]
  have hratioOne : 1 ≤ c / (2 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    linarith [hc.1]
  have hratioH : c / (2 * Real.pi) ≤ H + 5 := by
    have hratioC : c / (2 * Real.pi) ≤ c :=
      div_le_self hcpos.le hpiOne
    linarith [hc.2]
  have hlogNonneg : 0 ≤ Real.log (c / (2 * Real.pi)) :=
    Real.log_nonneg hratioOne
  have hlogH : Real.log (c / (2 * Real.pi)) ≤ Real.log (H + 5) := by
    exact Real.log_le_log (by positivity) hratioH
  have hdNonneg : 0 ≤ d c := by
    dsimp [d]
    positivity
  have hdBound : d c ≤ Real.log (H + 5) := by
    dsimp [d]
    calc
      Real.log (c / (2 * Real.pi)) / (2 * Real.pi) ≤
          Real.log (c / (2 * Real.pi)) :=
        div_le_self hlogNonneg hpiOne
      _ ≤ Real.log (H + 5) := hlogH
  have hdiff :
      riemannVonMangoldtMainTerm b - riemannVonMangoldtMainTerm a =
        (b - a) * d c := by
    rw [hslope]
    field_simp [sub_ne_zero.mpr hab.ne']
  rw [hdiff, abs_mul, abs_of_pos (sub_pos.mpr hab), abs_of_nonneg hdNonneg]
  calc
    (b - a) * d c ≤ 1 * Real.log (H + 5) := by
      exact mul_le_mul hwidth hdBound hdNonneg (by linarith)
    _ = Real.log (H + 5) := one_mul _

/-- The Riemann-von Mangoldt formula for the standard multiplicity-weighted
zero count, valid at every sufficiently large real height. -/
theorem exists_abs_riemannZeroCount_sub_mainTerm_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 8 ≤ T →
      |(riemannZeroCount T : ℝ) - riemannVonMangoldtMainTerm T| ≤
        C * (1 + Real.log (T + 6)) := by
  rcases exists_abs_riemannZeroCount_sub_mainTerm_le_log_of_goodHeight with
    ⟨Cgood, hCgood, hgood⟩
  refine ⟨Cgood + 1, by positivity, ?_⟩
  intro T hT
  rcases ExplicitFormulaAux.exists_goodHeight_Ioo (T - 1) with
    ⟨U, hUlow, hUhigh, hUgood⟩
  rcases ExplicitFormulaAux.exists_goodHeight_Ioo T with
    ⟨V, hVlow, hVhigh, hVgood⟩
  let L : ℝ := 1 + Real.log (T + 6)
  have hlogT : 0 ≤ Real.log (T + 6) :=
    Real.log_nonneg (by linarith)
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith
  have hlogUle : Real.log (U + 5) ≤ Real.log (T + 6) := by
    apply Real.log_le_log
    · linarith
    · linarith
  have hlogVle : Real.log (V + 5) ≤ Real.log (T + 6) := by
    apply Real.log_le_log
    · linarith
    · linarith
  have hUerr :
      |(riemannZeroCount U : ℝ) - riemannVonMangoldtMainTerm U| ≤
        Cgood * L := by
    calc
      _ ≤ Cgood * (1 + Real.log (U + 5)) :=
        hgood U (by linarith) hUgood
      _ ≤ Cgood * L := by
        apply mul_le_mul_of_nonneg_left _ hCgood
        dsimp [L]
        linarith
  have hVerr :
      |(riemannZeroCount V : ℝ) - riemannVonMangoldtMainTerm V| ≤
        Cgood * L := by
    calc
      _ ≤ Cgood * (1 + Real.log (V + 5)) :=
        hgood V (by linarith) hVgood
      _ ≤ Cgood * L := by
        apply mul_le_mul_of_nonneg_left _ hCgood
        dsimp [L]
        linarith
  have hmainLower :
      |riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U| ≤
        Real.log (T + 6) := by
    convert abs_mainTerm_sub_le_log_of_unit_interval
      (a := U) (b := T) (H := T + 1)
      (by linarith) (by linarith) (by linarith) (by linarith) using 1 <;> ring
  have hmainUpper :
      |riemannVonMangoldtMainTerm V - riemannVonMangoldtMainTerm T| ≤
        Real.log (T + 6) := by
    convert abs_mainTerm_sub_le_log_of_unit_interval
      (a := T) (b := V) (H := T + 1)
      (by linarith) hVlow (by linarith) (by linarith) using 1 <;> ring
  have hcountLower : (riemannZeroCount U : ℝ) ≤ riemannZeroCount T := by
    exact_mod_cast riemannZeroCount_mono (by linarith : U ≤ T)
  have hcountUpper : (riemannZeroCount T : ℝ) ≤ riemannZeroCount V := by
    exact_mod_cast riemannZeroCount_mono hVlow.le
  have hlower :
      riemannVonMangoldtMainTerm T - (riemannZeroCount T : ℝ) ≤
        (Cgood + 1) * L := by
    calc
      riemannVonMangoldtMainTerm T - (riemannZeroCount T : ℝ) ≤
          riemannVonMangoldtMainTerm T - (riemannZeroCount U : ℝ) := by
        linarith
      _ = (riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U) +
          (riemannVonMangoldtMainTerm U - (riemannZeroCount U : ℝ)) := by
        ring
      _ ≤ |riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U| +
          |(riemannZeroCount U : ℝ) - riemannVonMangoldtMainTerm U| := by
        have hbase : riemannVonMangoldtMainTerm U - (riemannZeroCount U : ℝ) ≤
            |(riemannZeroCount U : ℝ) - riemannVonMangoldtMainTerm U| := by
          simpa only [neg_sub] using
            (neg_le_abs ((riemannZeroCount U : ℝ) -
              riemannVonMangoldtMainTerm U))
        exact add_le_add (le_abs_self _) hbase
      _ ≤ Real.log (T + 6) + Cgood * L :=
        add_le_add hmainLower hUerr
      _ ≤ (Cgood + 1) * L := by
        dsimp [L]
        nlinarith
  have hupper :
      (riemannZeroCount T : ℝ) - riemannVonMangoldtMainTerm T ≤
        (Cgood + 1) * L := by
    calc
      (riemannZeroCount T : ℝ) - riemannVonMangoldtMainTerm T ≤
          (riemannZeroCount V : ℝ) - riemannVonMangoldtMainTerm T := by
        linarith
      _ = ((riemannZeroCount V : ℝ) - riemannVonMangoldtMainTerm V) +
          (riemannVonMangoldtMainTerm V - riemannVonMangoldtMainTerm T) := by
        ring
      _ ≤ |(riemannZeroCount V : ℝ) - riemannVonMangoldtMainTerm V| +
          |riemannVonMangoldtMainTerm V - riemannVonMangoldtMainTerm T| :=
        add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ Cgood * L + Real.log (T + 6) :=
        add_le_add hVerr hmainUpper
      _ ≤ (Cgood + 1) * L := by
        dsimp [L]
        nlinarith
  rw [abs_le]
  constructor <;> dsimp [L] at * <;> linarith

end RiemannVonMangoldt
end PrimeNumberTheorem
