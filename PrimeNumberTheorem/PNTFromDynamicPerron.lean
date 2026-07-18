import PrimeNumberTheorem.PNTFiniteZeroSum

open Filter Topology Asymptotics

namespace PrimeNumberTheorem

/-- At an integer argument, the explicit-formula half-jump is the von Mangoldt
coefficient at that integer. -/
lemma jumpVonMangoldt_natCast_eq (m : ℕ) :
    jumpVonMangoldt (m : ℝ) = vonMangoldt m := by
  classical
  rw [jumpVonMangoldt]
  split_ifs with h
  · have hspec := Classical.choose_spec h
    have heq : Classical.choose h = m := by exact_mod_cast hspec.symm
    rw [heq]
  · exact (h ⟨m, rfl⟩).elim

/-- The natural-point half-jump is nonnegative and at most logarithmic. -/
lemma jumpVonMangoldt_natCast_nonneg_le_log {m : ℕ} (_hm : 2 ≤ m) :
    0 ≤ jumpVonMangoldt (m : ℝ) ∧
      jumpVonMangoldt (m : ℝ) ≤ Real.log (m : ℝ) := by
  rw [jumpVonMangoldt_natCast_eq, vonMangoldt_eq_mathlib]
  exact ⟨ArithmeticFunction.vonMangoldt_nonneg,
    ArithmeticFunction.vonMangoldt_le_log⟩

/-- The midpoint correction is negligible compared with its natural
argument. -/
theorem jumpVonMangoldt_natCast_isLittleO :
    (fun m : ℕ => jumpVonMangoldt (m : ℝ))
      =o[atTop] (fun m : ℕ => (m : ℝ)) := by
  have hlog :
      (fun m : ℕ => Real.log (m : ℝ))
        =o[atTop] (fun m : ℕ => (m : ℝ)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  have hjumpLog :
      (fun m : ℕ => jumpVonMangoldt (m : ℝ))
        =O[atTop] (fun m : ℕ => Real.log (m : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 2] with m hm
    rcases jumpVonMangoldt_natCast_nonneg_le_log hm with ⟨hjump0, hjump⟩
    have hlog0 : 0 ≤ Real.log (m : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
    simpa [Real.norm_eq_abs, abs_of_nonneg hjump0, abs_of_nonneg hlog0] using hjump
  exact hjumpLog.trans_isLittleO hlog

/-- The right-continuous Chebyshev error is `o(m)` on natural arguments. -/
theorem chebyshevPsi_sub_id_nat_isLittleO :
    (fun m : ℕ => chebyshevPsi (m : ℝ) - (m : ℝ))
      =o[atTop] (fun m : ℕ => (m : ℝ)) := by
  have hmid := ExplicitFormulaAux.chebyshevPsi0_sub_id_nat_isLittleO
  have hjump := jumpVonMangoldt_natCast_isLittleO.const_mul_left (1 / 2 : ℝ)
  have hsum := hmid.add hjump
  apply hsum.congr'
  · filter_upwards with m
    simp only [ExplicitFormulaAux.chebyshevPsi0]
    ring
  · exact EventuallyEq.rfl

/-- The natural-point `o(m)` estimate, together with the floor identity for
Chebyshev's function, proves the real-variable Chebyshev PNT. -/
theorem PNTForm3_proved : PNTForm3 := by
  have hratio := chebyshevPsi_sub_id_nat_isLittleO.tendsto_div_nhds_zero
  have hnat :
      Tendsto (fun m : ℕ => chebyshevPsi (m : ℝ) / (m : ℝ))
        atTop (𝓝 1) := by
    have hsum :
        Tendsto (fun m : ℕ =>
          1 + (chebyshevPsi (m : ℝ) - (m : ℝ)) / (m : ℝ))
          atTop (𝓝 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add hratio
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    field_simp [hm0]
    ring
  have hfloorNat :
      Tendsto (fun x : ℝ =>
        chebyshevPsi ((Nat.floor x : ℕ) : ℝ) / (Nat.floor x : ℝ))
        atTop (𝓝 1) :=
    hnat.comp tendsto_nat_floor_atTop
  have hfloorRatio :
      Tendsto (fun x : ℝ => (Nat.floor x : ℝ) / x) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop
  have hproduct := hfloorNat.mul hfloorRatio
  have hproduct' :
      Tendsto (fun x : ℝ =>
        (chebyshevPsi (Nat.floor x : ℝ) / (Nat.floor x : ℝ)) *
          ((Nat.floor x : ℝ) / x)) atTop (𝓝 1) := by
    simpa only [one_mul] using hproduct
  rw [PNTForm3]
  apply hproduct'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ x := by linarith
  have hxne : x ≠ 0 := by linarith
  have hn1 : 1 ≤ Nat.floor x := by
    have hfloor := Nat.floor_mono hx
    simpa using hfloor
  have hnne : (Nat.floor x : ℝ) ≠ 0 := by
    exact_mod_cast (show Nat.floor x ≠ 0 by omega)
  have hpsiEq : chebyshevPsi x = chebyshevPsi (Nat.floor x : ℝ) := by
    calc
      chebyshevPsi x = Chebyshev.psi x := chebyshevPsi_eq_mathlib x
      _ = Chebyshev.psi (Nat.floor x : ℝ) := by
        simpa using Chebyshev.psi_eq_psi_coe_floor x
      _ = chebyshevPsi (Nat.floor x : ℝ) :=
        (chebyshevPsi_eq_mathlib (Nat.floor x : ℝ)).symm
  rw [hpsiEq]
  field_simp [hnne, hxne]

/-- Error-term form of the unconditional Chebyshev PNT. -/
theorem chebyshevPsi_sub_id_isLittleO :
    (fun x : ℝ => chebyshevPsi x - x)
      =o[atTop] (fun x : ℝ => x) :=
  PNTForm3_error_isLittleO_id PNTForm3_proved

/-- Unconditional prime number theorem in the logarithmic-integral form. -/
theorem PNTForm2_proved : PNTForm2 :=
  PNTForm2_of_PNTForm3 PNTForm3_proved

/-- Unconditional prime number theorem in the classical `π(x) log x / x`
form. -/
theorem PNTForm1_proved : PNTForm1 :=
  PNTForm1_of_PNTForm3 PNTForm3_proved

/-- All three project PNT formulations are now proved unconditionally. -/
theorem pnt_forms_proved : PNTForm1 ∧ PNTForm2 ∧ PNTForm3 :=
  ⟨PNTForm1_proved, PNTForm2_proved, PNTForm3_proved⟩

end PrimeNumberTheorem
