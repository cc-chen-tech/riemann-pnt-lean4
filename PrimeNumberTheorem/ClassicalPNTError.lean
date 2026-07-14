import PrimeNumberTheorem.PNTFromDynamicPerron

open Filter Topology

namespace PrimeNumberTheorem

/-- The moving-height midpoint estimate has the standard de la Vallee Poussin
shape after absorbing its square-root-log polynomial factors into a slightly
weaker exponential. -/
theorem exists_nat_eventually_abs_chebyshevPsi0_sub_id_le_exp_neg_sqrt_log :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop,
      |chebyshevPsi0 (m : ℝ) - (m : ℝ)| ≤
        C * (m : ℝ) * Real.exp (-c * pntSqrtLog m) := by
  rcases ExplicitFormulaAux.exists_nat_abs_chebyshevPsi0_sub_id_le_exp_sqrt_log with
    ⟨a, C, U, ha, hC, hbound⟩
  let c : ℝ := min a (1 / 2 : ℝ) / 2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hac : 0 < a - c := by
    have hca : c ≤ a / 2 := by
      dsimp [c]
      linarith [min_le_left a (1 / 2 : ℝ)]
    linarith
  have hhalfc : 0 < (1 / 2 : ℝ) - c := by
    have hchalf : c ≤ (1 / 2 : ℝ) / 2 := by
      dsimp [c]
      linarith [min_le_right a (1 / 2 : ℝ)]
    linarith
  have hfour :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero (a - c) hac 4
  have htwo :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero
      ((1 / 2 : ℝ) - c) hhalfc 2
  have hfour_le : ∀ᶠ m : ℕ in atTop,
      pntSqrtLog m ^ 4 * Real.exp (-(a - c) * pntSqrtLog m) ≤ 1 :=
    ((tendsto_order.1 hfour).2 1 zero_lt_one).mono fun _ h => h.le
  have htwo_le : ∀ᶠ m : ℕ in atTop,
      pntSqrtLog m ^ 2 *
          Real.exp (-((1 / 2 : ℝ) - c) * pntSqrtLog m) ≤ 1 :=
    ((tendsto_order.1 htwo).2 1 zero_lt_one).mono fun _ h => h.le
  have hU : ∀ᶠ m : ℕ in atTop, U ≤ pntSqrtLog m :=
    (tendsto_atTop.1 tendsto_pntSqrtLog_atTop U)
  refine ⟨c, 2 * C, hc, mul_nonneg (by norm_num) hC, ?_⟩
  filter_upwards [eventually_ge_atTop 3, hU, hfour_le, htwo_le] with
      m hm hUm h4 h2
  have hpoint := hbound m hm (by simpa only [pntSqrtLog] using hUm)
  have hterm4 :
      pntSqrtLog m ^ 4 * Real.exp (-a * pntSqrtLog m) ≤
        Real.exp (-c * pntSqrtLog m) := by
    calc
      pntSqrtLog m ^ 4 * Real.exp (-a * pntSqrtLog m) =
          (pntSqrtLog m ^ 4 *
              Real.exp (-(a - c) * pntSqrtLog m)) *
            Real.exp (-c * pntSqrtLog m) := by
        rw [show -a * pntSqrtLog m =
            (-(a - c) * pntSqrtLog m) + (-c * pntSqrtLog m) by ring,
          Real.exp_add]
        ring
      _ ≤ 1 * Real.exp (-c * pntSqrtLog m) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ = Real.exp (-c * pntSqrtLog m) := one_mul _
  have hterm2 :
      pntSqrtLog m ^ 2 *
          Real.exp (-(1 / 2 : ℝ) * pntSqrtLog m) ≤
        Real.exp (-c * pntSqrtLog m) := by
    calc
      pntSqrtLog m ^ 2 *
          Real.exp (-(1 / 2 : ℝ) * pntSqrtLog m) =
          (pntSqrtLog m ^ 2 *
              Real.exp (-((1 / 2 : ℝ) - c) * pntSqrtLog m)) *
            Real.exp (-c * pntSqrtLog m) := by
        rw [show -(1 / 2 : ℝ) * pntSqrtLog m =
            (-((1 / 2 : ℝ) - c) * pntSqrtLog m) +
              (-c * pntSqrtLog m) by ring,
          Real.exp_add]
        ring
      _ ≤ 1 * Real.exp (-c * pntSqrtLog m) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (-c * pntSqrtLog m) := one_mul _
  calc
    |chebyshevPsi0 (m : ℝ) - (m : ℝ)| ≤
        C * (m : ℝ) *
          (pntSqrtLog m ^ 4 * Real.exp (-a * pntSqrtLog m) +
            pntSqrtLog m ^ 2 *
              Real.exp (-(1 / 2 : ℝ) * pntSqrtLog m)) := by
      simpa only [pntSqrtLog] using hpoint
    _ ≤ C * (m : ℝ) *
        (Real.exp (-c * pntSqrtLog m) +
          Real.exp (-c * pntSqrtLog m)) :=
      mul_le_mul_of_nonneg_left (add_le_add hterm4 hterm2)
        (mul_nonneg hC (Nat.cast_nonneg m))
    _ = (2 * C) * (m : ℝ) * Real.exp (-c * pntSqrtLog m) := by ring

/-- The von Mangoldt half-jump is smaller than the classical exponential
scale, so the same shape controls the right-continuous Chebyshev function on
natural arguments. -/
theorem exists_nat_eventually_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop,
      |chebyshevPsi (m : ℝ) - (m : ℝ)| ≤
        C * (m : ℝ) * Real.exp (-c * pntSqrtLog m) := by
  rcases exists_nat_eventually_abs_chebyshevPsi0_sub_id_le_exp_neg_sqrt_log with
    ⟨c, C, hc, hC, hmid⟩
  have hu : ∀ᶠ m : ℕ in atTop, 2 * c ≤ pntSqrtLog m :=
    tendsto_atTop.1 tendsto_pntSqrtLog_atTop (2 * c)
  refine ⟨c, C + 1, hc, add_nonneg hC zero_le_one, ?_⟩
  filter_upwards [hmid, eventually_ge_atTop 2, hu] with m hmidm hm hum
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmone
  have hu0 : 0 ≤ pntSqrtLog m := by
    exact Real.sqrt_nonneg _
  have hu_sq : pntSqrtLog m ^ 2 = Real.log (m : ℝ) := by
    simpa only [pntSqrtLog] using Real.sq_sqrt hlog0
  let scale : ℝ := (m : ℝ) * Real.exp (-c * pntSqrtLog m)
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hrpow_le : (m : ℝ) ^ (1 / 2 : ℝ) ≤ scale := by
    calc
      (m : ℝ) ^ (1 / 2 : ℝ) =
          Real.exp (Real.log (m : ℝ) * (1 / 2 : ℝ)) := by
        rw [Real.rpow_def_of_pos hmpos]
      _ ≤ Real.exp (Real.log (m : ℝ) + (-c * pntSqrtLog m)) := by
        apply Real.exp_le_exp.mpr
        rw [← hu_sq]
        nlinarith
      _ = scale := by
        dsimp [scale]
        rw [Real.exp_add, Real.exp_log hmpos]
  have hlog_le : Real.log (m : ℝ) ≤ 2 * scale := by
    calc
      Real.log (m : ℝ) ≤ (m : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        Real.log_le_rpow_div (Nat.cast_nonneg m) (by norm_num)
      _ = 2 * ((m : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ ≤ 2 * scale := mul_le_mul_of_nonneg_left hrpow_le (by norm_num)
  rcases jumpVonMangoldt_natCast_nonneg_le_log hm with ⟨hjump0, hjumpLog⟩
  have hjump : |jumpVonMangoldt (m : ℝ) / 2| ≤ scale := by
    rw [abs_of_nonneg (div_nonneg hjump0 (by norm_num))]
    calc
      jumpVonMangoldt (m : ℝ) / 2 ≤ Real.log (m : ℝ) / 2 :=
        div_le_div_of_nonneg_right hjumpLog (by norm_num)
      _ ≤ (2 * scale) / 2 :=
        div_le_div_of_nonneg_right hlog_le (by norm_num)
      _ = scale := by ring
  have hdecomp :
      chebyshevPsi (m : ℝ) - (m : ℝ) =
        (chebyshevPsi0 (m : ℝ) - (m : ℝ)) +
          jumpVonMangoldt (m : ℝ) / 2 := by
    rw [chebyshevPsi0]
    ring
  calc
    |chebyshevPsi (m : ℝ) - (m : ℝ)| =
        |(chebyshevPsi0 (m : ℝ) - (m : ℝ)) +
          jumpVonMangoldt (m : ℝ) / 2| := by rw [hdecomp]
    _ ≤ |chebyshevPsi0 (m : ℝ) - (m : ℝ)| +
        |jumpVonMangoldt (m : ℝ) / 2| := abs_add_le _ _
    _ ≤ C * scale + scale := by
      apply add_le_add
      · simpa [scale, mul_assoc] using hmidm
      · exact hjump
    _ = (C + 1) * (m : ℝ) * Real.exp (-c * pntSqrtLog m) := by
      dsimp [scale]
      ring

/-- The natural-point de la Vallee Poussin-form estimate extends to every
sufficiently large real input.  The decay constant is weakened once to compare the floor sample
with the real argument. -/
theorem exists_eventually_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |chebyshevPsi x - x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  rcases exists_nat_eventually_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log with
    ⟨c, C, hc, hC, hnat⟩
  rcases eventually_atTop.1 hnat with ⟨N, hN⟩
  let d : ℝ := c / 2
  have hd : 0 < d := div_pos hc (by norm_num)
  have hsqrtLogTop :
      Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hu : ∀ᶠ x : ℝ in atTop, d ≤ Real.sqrt (Real.log x) :=
    tendsto_atTop.1 hsqrtLogTop d
  refine ⟨d, C + 1, hd, add_nonneg hC zero_le_one, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ),
      eventually_ge_atTop (N : ℝ), hu] with x hx4 hxN hux
  let n : ℕ := Nat.floor x
  let scale : ℝ → ℝ := fun y => y * Real.exp (-d * Real.sqrt (Real.log y))
  have hxpos : 0 < x := by linarith
  have hx0 : 0 ≤ x := hxpos.le
  have hnN : N ≤ n := by
    dsimp [n]
    exact (Nat.le_floor_iff hx0).2 (by exact_mod_cast hxN)
  have hn2 : 2 ≤ n := by
    dsimp [n]
    apply (Nat.le_floor_iff hx0).2
    norm_num
    linarith
  have hnle : (n : ℝ) ≤ x := by
    dsimp [n]
    exact Nat.floor_le hx0
  have hxlt : x < (n : ℝ) + 1 := by
    dsimp [n]
    simpa using Nat.lt_floor_add_one x
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsqrtx0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrtx2 : 2 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num)]
    all_goals nlinarith
  have hsqrtx_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
  have hsqrt_le_half : Real.sqrt x ≤ x / 2 := by
    have hprod : 0 ≤ Real.sqrt x * (Real.sqrt x - 2) :=
      mul_nonneg hsqrtx0 (sub_nonneg.mpr hsqrtx2)
    nlinarith
  have hhalf_lt_n : x / 2 < (n : ℝ) := by
    have hone_le_half : 1 ≤ x / 2 := by linarith
    linarith
  have hsqrt_lt_n : Real.sqrt x < (n : ℝ) :=
    lt_of_le_of_lt hsqrt_le_half hhalf_lt_n
  have hlogLower : Real.log x / 2 ≤ Real.log (n : ℝ) := by
    rw [← Real.log_sqrt hx0]
    exact Real.log_le_log (Real.sqrt_pos.2 hxpos) hsqrt_lt_n.le
  have hsqrtLog :
      Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log (n : ℝ)) := by
    have hxSq := Real.sq_sqrt hlogx0
    have hnSq := Real.sq_sqrt hlogn0
    have hsx0 := Real.sqrt_nonneg (Real.log x)
    have hsn0 := Real.sqrt_nonneg (Real.log (n : ℝ))
    nlinarith
  have hexp :
      Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤
        Real.exp (-d * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hsqrtLog hc.le
    dsimp [d]
    linarith
  have hscalele :
      (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤ scale x := by
    calc
      (n : ℝ) * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) ≤
          x * Real.exp (-c * Real.sqrt (Real.log (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hnle (Real.exp_pos _).le
      _ ≤ x * Real.exp (-d * Real.sqrt (Real.log x)) :=
        mul_le_mul_of_nonneg_left hexp hx0
      _ = scale x := rfl
  have hnatx :
      |chebyshevPsi (n : ℝ) - (n : ℝ)| ≤ C * scale x := by
    calc
      |chebyshevPsi (n : ℝ) - (n : ℝ)| ≤
          C * (n : ℝ) * Real.exp (-c * pntSqrtLog n) := hN n hnN
      _ = C * ((n : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log (n : ℝ)))) := by
        simp only [pntSqrtLog]
        ring
      _ ≤ C * scale x := mul_le_mul_of_nonneg_left hscalele hC
  have hpsiEq : chebyshevPsi x = chebyshevPsi (n : ℝ) := by
    calc
      chebyshevPsi x = Chebyshev.psi x := chebyshevPsi_eq_mathlib x
      _ = Chebyshev.psi (n : ℝ) := by
        simpa [n] using Chebyshev.psi_eq_psi_coe_floor x
      _ = chebyshevPsi (n : ℝ) :=
        (chebyshevPsi_eq_mathlib (n : ℝ)).symm
  have hfloor : |(n : ℝ) - x| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hnle)]
    linarith
  have hscaleOne : 1 ≤ scale x := by
    have hsx0 := Real.sqrt_nonneg (Real.log x)
    have hsxSq := Real.sq_sqrt hlogx0
    have hprod :
        0 ≤ Real.sqrt (Real.log x) * (Real.sqrt (Real.log x) - d) :=
      mul_nonneg hsx0 (sub_nonneg.mpr hux)
    calc
      1 = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp (Real.log x + (-d * Real.sqrt (Real.log x))) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hsxSq, hprod]
      _ = scale x := by
        dsimp [scale]
        rw [Real.exp_add, Real.exp_log hxpos]
  have herrEq :
      chebyshevPsi x - x =
        (chebyshevPsi (n : ℝ) - (n : ℝ)) + ((n : ℝ) - x) := by
    rw [hpsiEq]
    ring
  calc
    |chebyshevPsi x - x| =
        |(chebyshevPsi (n : ℝ) - (n : ℝ)) + ((n : ℝ) - x)| := by
      rw [herrEq]
    _ ≤ |chebyshevPsi (n : ℝ) - (n : ℝ)| + |(n : ℝ) - x| :=
      abs_add_le _ _
    _ ≤ C * scale x + 1 := add_le_add hnatx hfloor
    _ ≤ C * scale x + scale x := by
      simpa [add_comm] using add_le_add_left hscaleOne (C * scale x)
    _ = (C + 1) * x * Real.exp (-d * Real.sqrt (Real.log x)) := by
      dsimp [scale]
      ring

/-- Classical de la Vallee Poussin-form Chebyshev remainder in pointwise form. -/
theorem exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |chebyshevPsi x - x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  rcases exists_eventually_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log with
    ⟨c, C, hc, hC, hbound⟩
  rcases eventually_atTop.1 hbound with ⟨X, hX⟩
  exact ⟨c, C, X, hc, hC, hX⟩

end PrimeNumberTheorem
