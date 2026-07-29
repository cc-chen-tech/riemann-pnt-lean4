import PrimeNumberTheorem.ExplicitFormulaRealInterpolation

open Complex Filter Set Topology

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

/-!
# One good height for all real samples
-/

/-- One good height in every unit interval controls the standard
multiplicity-aware explicit formula simultaneously at every real sample
`x >= 3`.  The four displayed costs are respectively the natural-sample
Perron error, interpolation through the finite zero sum, the uniformly
bounded closed package, and the midpoint jump. -/
theorem
    exists_uniform_goodHeight_Icc_norm_real_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 8 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight T ∧
        ∀ x : ℝ, 3 ≤ x →
          ‖explicitFormulaApproxWithMultiplicity x T -
              (chebyshevPsi0 x : ℂ)‖ ≤
            C * x *
                ((1 + Real.log x) ^ 2 +
                  (1 + Real.log (A + 6)) ^ 2) / T +
              (1 + D * T * (1 + Real.log (T + 6))) +
              2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound +
              Real.log x := by
  rcases
      exists_uniform_goodHeight_Icc_norm_nat_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le
      with ⟨C, hC, hselect⟩
  rcases ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log with
    ⟨D, hD, hglobal⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA
  rcases hselect A hA with ⟨T, hTmem, hgood, hnat⟩
  have hT4 : 4 ≤ T := by linarith [hTmem.1]
  have hTpos : 0 < T := by linarith
  refine ⟨T, hTmem, hgood, ?_⟩
  intro x hx
  let m : ℕ := Nat.floor x
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hm : 3 ≤ m := by
    dsimp [m]
    exact Nat.le_floor hx
  have hmreal : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by linarith
  have hmx : (m : ℝ) ≤ x := by
    dsimp [m]
    exact Nat.floor_le hx0
  have hlogm_le_logx : Real.log (m : ℝ) ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn hmpos hxpos hmx
  have hlogm0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by linarith)
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlinear :
      1 + Real.log (m : ℝ) ≤ 1 + Real.log x := by
    linarith
  have hsquare :
      (1 + Real.log (m : ℝ)) ^ 2 ≤
        (1 + Real.log x) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hlinear 2
  have hfloor := hnat m hm
  have hnatural :
      C * (m : ℝ) *
            ((1 + Real.log (m : ℝ)) ^ 2 +
              (1 + Real.log (A + 6)) ^ 2) / T ≤
        C * x *
            ((1 + Real.log x) ^ 2 +
              (1 + Real.log (A + 6)) ^ 2) / T := by
    apply div_le_div_of_nonneg_right _ hTpos.le
    gcongr
  have habs : |x - (m : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hmx)]
    have hlt : x < (m : ℝ) + 1 := by
      dsimp [m]
      exact_mod_cast Nat.lt_floor_add_one x
    linarith
  have hglobalT :
      globalZeroMultiplicity T ≤
        D * T * (1 + Real.log (T + 6)) :=
    hglobal T hT4
  have hspatial :
      (1 + globalZeroMultiplicity T) * |x - (m : ℝ)| ≤
        1 + D * T * (1 + Real.log (T + 6)) := by
    calc
      (1 + globalZeroMultiplicity T) * |x - (m : ℝ)| ≤
          (1 + globalZeroMultiplicity T) * 1 :=
        mul_le_mul_of_nonneg_left habs
          (by
            linarith [ExplicitFormulaAux.globalZeroMultiplicity_nonneg T])
      _ = 1 + globalZeroMultiplicity T := by ring
      _ ≤ 1 + D * T * (1 + Real.log (T + 6)) := by
        linarith
  have hmidpoint :
      (Real.log (m : ℝ) + Real.log x) / 2 ≤ Real.log x := by
    linarith
  have hinterp :=
    ExplicitFormulaAux.norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_floor
      (x := x) (T := T)
      hx hfloor
  dsimp [m] at hnatural hspatial hmidpoint hinterp ⊢
  apply hinterp.trans
  linarith [hnatural, hspatial, hmidpoint]

end ExplicitFormulaResidues
end PrimeNumberTheorem
