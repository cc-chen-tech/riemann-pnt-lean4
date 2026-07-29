import PrimeNumberTheorem.CofinalExplicitFormula
import PrimeNumberTheorem.ExplicitFormulaSpatialVariation

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

/-!
# One good height for all natural samples

The moving-right contour theorem already chooses one height that controls all
natural samples.  This module removes the finite trivial-zero cutoff while
preserving that quantifier order.
-/

/-- One good height in every unit interval controls the standard
multiplicity-aware explicit formula simultaneously at every natural sample
`m >= 3`. -/
theorem
    exists_uniform_goodHeight_Icc_norm_nat_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 8 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight T ∧
        ∀ m : ℕ, 3 ≤ m →
          ‖explicitFormulaApproxWithMultiplicity (m : ℝ) T -
              (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
            C * (m : ℝ) *
              ((1 + Real.log (m : ℝ)) ^ 2 +
                (1 + Real.log (A + 6)) ^ 2) / T := by
  rcases
      exists_uniform_goodHeight_Icc_norm_nat_movingRight_truncatedExplicitFormula_sub_chebyshevPsi0_le
      with ⟨C0, hC0, hselect⟩
  refine ⟨C0 + 2, by positivity, ?_⟩
  intro A hA
  rcases hselect A hA with ⟨T, hTmem, hgood, hbound⟩
  have hTpos : 0 < T := by linarith [hTmem.1]
  refine ⟨T, hTmem, hgood, ?_⟩
  intro m hm
  let x : ℝ := m
  let Lm : ℝ := 1 + Real.log x
  let LA : ℝ := 1 + Real.log (A + 6)
  let B : ℝ := x * (Lm ^ 2 + LA ^ 2) / T
  have hx3 : 3 ≤ x := by
    dsimp [x]
    exact_mod_cast hm
  have hx : 1 < x := by linarith
  have hLmpos : 0 < Lm := by
    dsimp [Lm]
    have hlog : 0 < Real.log x := Real.log_pos hx
    linarith
  have hLApos : 0 < LA := by
    dsimp [LA]
    have hlog : 0 ≤ Real.log (A + 6) :=
      Real.log_nonneg (by linarith)
    linarith
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hleft := tendsto_oddVerticalExplicitBound_atTop hx hTpos.le
  rcases (Metric.tendsto_atTop.mp hleft) B hBpos with
    ⟨Nleft, hNleft⟩
  have htrivial := ExplicitFormulaAux.tendsto_finiteTrivialZeroSum_residues hx
  rcases (Metric.tendsto_atTop.mp htrivial) B hBpos with
    ⟨Ntrivial, hNtrivial⟩
  let N : ℕ := max Nleft Ntrivial
  let finite : ℂ :=
    ∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)),
      -((x : ℂ) ^ p) / p
  let zeroSum : ℂ :=
    ∑ rho ∈ nontrivialZerosFinset T,
      -(analyticOrderNatAt riemannZeta rho : ℂ) *
        (x : ℂ) ^ rho / rho
  let mainTerm : ℂ :=
    (x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 + zeroSum
  let logTerm : ℂ :=
    ((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)
  let left : ℝ :=
    (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
      x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
      (2 * Real.pi)
  have hleftDist := hNleft N (le_max_left _ _)
  have hleftNonneg : 0 ≤ left := by
    have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    have hlogN : 0 ≤ Real.log (2 * (N : ℝ) + T + 4) :=
      Real.log_nonneg (by
        have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith)
    dsimp [left]
    positivity
  have hleftRate : left ≤ B := by
    change dist left 0 < B at hleftDist
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hleftNonneg] at hleftDist
    exact hleftDist.le
  have htrivialDist := hNtrivial N (le_max_right _ _)
  have htrivialRate : ‖logTerm - finite‖ ≤ B := by
    have hforward : ‖finite - logTerm‖ < B := by
      change dist finite logTerm < B at htrivialDist
      simpa [dist_eq_norm] using htrivialDist
    rw [norm_sub_rev]
    exact hforward.le
  have hfinite :
      ‖finite + mainTerm - (chebyshevPsi0 x : ℂ)‖ ≤
        C0 * B + left := by
    have h := hbound m N hm
    calc
      ‖finite + mainTerm - (chebyshevPsi0 x : ℂ)‖ ≤
          C0 * x * (Lm ^ 2 + LA ^ 2) / T + left := by
        simpa [finite, mainTerm, zeroSum, left, Lm, LA, x] using h
      _ = C0 * B + left := by
        dsimp [B]
        ring
  have hzeroSum :
      zeroSum = -finiteNontrivialZeroSumWithMultiplicity x T := by
    dsimp [zeroSum, finiteNontrivialZeroSumWithMultiplicity]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro rho _hrho
    ring
  have happ :
      explicitFormulaApproxWithMultiplicity x T =
        mainTerm + logTerm := by
    dsimp [explicitFormulaApproxWithMultiplicity, mainTerm, logTerm]
    rw [hzeroSum]
    push_cast
    ring
  have hsplit :
      explicitFormulaApproxWithMultiplicity x T -
          (chebyshevPsi0 x : ℂ) =
        (finite + mainTerm - (chebyshevPsi0 x : ℂ)) +
          (logTerm - finite) := by
    rw [happ]
    ring
  change
    ‖explicitFormulaApproxWithMultiplicity x T -
        (chebyshevPsi0 x : ℂ)‖ ≤
      (C0 + 2) * x * (Lm ^ 2 + LA ^ 2) / T
  rw [hsplit]
  calc
    _ ≤ ‖finite + mainTerm - (chebyshevPsi0 x : ℂ)‖ +
        ‖logTerm - finite‖ := norm_add_le _ _
    _ ≤ (C0 * B + left) + B :=
      add_le_add hfinite htrivialRate
    _ ≤ (C0 * B + B) + B := by
      gcongr
    _ = (C0 + 2) * x * (Lm ^ 2 + LA ^ 2) / T := by
      dsimp [B]
      ring

end ExplicitFormulaResidues
end PrimeNumberTheorem
