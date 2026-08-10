import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalBalancedGoodHeight

open Complex Filter Set Topology

namespace PrimeNumberTheorem

/-- A zero-free width of `(sqrt b - epsilon) / sqrt (log x)` converts the
moving real-part exponent into the corresponding exponential square-root
decay, with no further loss. -/
theorem rpow_classicalZeroFreeWidth_le_exp_sqrt
    {b epsilon x T : ℝ}
    (hx : 1 < x)
    (hwidth :
      (Real.sqrt b - epsilon) / Real.sqrt (Real.log x) ≤
        b / Real.log (T + 6)) :
    x ^ (1 - b / Real.log (T + 6)) ≤
      x * Real.exp (-(Real.sqrt b - epsilon) *
        Real.sqrt (Real.log x)) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hxone : 1 ≤ x := hx.le
  let u : ℝ := Real.sqrt (Real.log x)
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hu : 0 < u := by
    dsimp [u]
    exact Real.sqrt_pos.2 hlogx
  have husquare : u ^ 2 = Real.log x := by
    dsimp [u]
    exact Real.sq_sqrt hlogx.le
  have hexponent :
      1 - b / Real.log (T + 6) ≤
        1 - (Real.sqrt b - epsilon) / u := by
    have hwidth' :
        (Real.sqrt b - epsilon) / u ≤
          b / Real.log (T + 6) := by
      simpa [u] using hwidth
    linarith
  calc
    x ^ (1 - b / Real.log (T + 6)) ≤
        x ^ (1 - (Real.sqrt b - epsilon) / u) :=
      Real.rpow_le_rpow_of_exponent_le hxone hexponent
    _ = x * Real.exp (-(Real.sqrt b - epsilon) * u) := by
      rw [Real.rpow_def_of_pos hxpos]
      have hrewrite :
          Real.log x * (1 - (Real.sqrt b - epsilon) / u) =
            u ^ 2 - (Real.sqrt b - epsilon) * u := by
        rw [← husquare]
        field_simp [hu.ne']
      rw [hrewrite,
        show u ^ 2 - (Real.sqrt b - epsilon) * u =
          u ^ 2 + (-(Real.sqrt b - epsilon) * u) by ring,
        Real.exp_add, husquare, Real.exp_log hxpos]
    _ = x * Real.exp (-(Real.sqrt b - epsilon) *
        Real.sqrt (Real.log x)) := by rfl

/-- The actual multiplicity-weighted finite zero sum at the optimally selected
good height has every epsilon-sharp classical square-root exponential rate.

The two displayed lower-threshold assumptions are explicit and become
automatic for sufficiently large `m`.  The logarithmic multiplicity factor is
kept visible. -/
theorem
    exists_norm_selectedClassicalBalancedFiniteZeroSum_le_exp_sqrt :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection)
        (epsilon : ℝ), 0 < epsilon → epsilon < Real.sqrt b →
        ∀ m : ℕ, 3 ≤ m →
          9 ≤ classicalBalancedHeightBase b (m : ℝ) →
          ((Real.sqrt b - epsilon) * Real.log 8) /
              (epsilon * Real.sqrt b) ≤
                Real.sqrt (Real.log (m : ℝ)) →
          ‖finiteNontrivialZeroSumWithMultiplicity
              (m : ℝ)
              (selectedClassicalBalancedGoodHeight b selection (m : ℝ))‖ ≤
            C * (m : ℝ) *
              Real.exp (-(Real.sqrt b - epsilon) *
                Real.sqrt (Real.log (m : ℝ))) *
              (1 + Real.log
                (selectedClassicalBalancedGoodHeight b selection (m : ℝ) +
                  6)) ^ 2 := by
  rcases
      ExplicitFormulaAux.exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_zeroFree_mul_log_sq
      with ⟨b, C, hb, hC, hzeros⟩
  refine ⟨b, C, hb, hC, ?_⟩
  intro selection epsilon hepsilon hepsilonSqrt m hm hbase hthreshold
  let x : ℝ := m
  let T : ℝ :=
    selectedClassicalBalancedGoodHeight b selection (m : ℝ)
  have hx : 1 < x := by
    dsimp [x]
    exact_mod_cast (show 1 < m by omega)
  have hselection :
      T ∈ Set.Icc
        (classicalBalancedHeightBase b x - 1)
        (classicalBalancedHeightBase b x) := by
    dsimp [T, x]
    have hA : 8 ≤ classicalBalancedHeightBase b (m : ℝ) - 1 := by
      linarith
    simpa [selectedClassicalBalancedGoodHeight] using
      selection.height_mem
        (classicalBalancedHeightBase b (m : ℝ) - 1) hA
  have hT : 4 ≤ T := by
    have hA : 8 ≤ classicalBalancedHeightBase b x - 1 := by
      dsimp [x] at hbase ⊢
      linarith
    exact le_trans (by norm_num) (hA.trans hselection.1)
  have hu : 0 < Real.sqrt (Real.log x) := by
    apply Real.sqrt_pos.2
    exact Real.log_pos hx
  have hwidth :
      (Real.sqrt b - epsilon) / Real.sqrt (Real.log x) ≤
        b / Real.log (T + 6) := by
    apply classicalBalancedHeight_zeroFreeWidth_ge
      hb hepsilon hepsilonSqrt hu
    · simpa [x] using hthreshold
    · exact hT
    · simpa [classicalBalancedHeightBase] using hselection.2
  have hrpow :
      x ^ (1 - b / Real.log (T + 6)) ≤
        x * Real.exp (-(Real.sqrt b - epsilon) *
          Real.sqrt (Real.log x)) :=
    rpow_classicalZeroFreeWidth_le_exp_sqrt hx hwidth
  calc
    ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
        C * x ^ (1 - b / Real.log (T + 6)) *
          (1 + Real.log (T + 6)) ^ 2 :=
      hzeros x T hx hT
    _ ≤ C *
        (x * Real.exp (-(Real.sqrt b - epsilon) *
          Real.sqrt (Real.log x))) *
          (1 + Real.log (T + 6)) ^ 2 := by
      gcongr
    _ = C * x *
        Real.exp (-(Real.sqrt b - epsilon) *
          Real.sqrt (Real.log x)) *
          (1 + Real.log (T + 6)) ^ 2 := by ring

end PrimeNumberTheorem
