import PrimeNumberTheorem.CofinalExplicitFormula
import PrimeNumberTheorem.GlobalZeroCount
import ZeroFreeRegion.MeromorphicAux

open Complex Filter Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

/-- Under RH, the midpoint Chebyshev error has the expected RH scale at every
natural sample.  The proof combines the uniform polynomial-height contour
formula with the multiplicity-aware finite-zero estimate; the constant is
independent of the sample and of the selected good height. -/
theorem exists_nat_abs_chebyshevPsi0_sub_id_le_sqrt_mul_one_add_log_sq_of_RH
    (hRH : RiemannHypothesis.Statement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m →
      |chebyshevPsi0 (m : ℝ) - (m : ℝ)| ≤
        C * Real.sqrt (m : ℝ) * (1 + Real.log (m : ℝ)) ^ 2 := by
  rcases
      exists_nat_goodHeight_pow_five_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_nat_sq
      with ⟨Cc, hCc, hcontour⟩
  rcases
      exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_sqrt_mul_log_sq_of_RH hRH
      with ⟨Cz, hCz, hzeros⟩
  let K : ℝ := ‖deriv riemannZeta 0 / riemannZeta 0‖ + 1
  let C : ℝ := Cc + 36 * Cz + K
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m hm
  let x : ℝ := m
  let B : ℝ := 1 + Real.log x
  let logTerm : ℂ :=
    ((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ)
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hm
  have hx : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hBone : 1 ≤ B := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := hBone.trans' zero_le_one
  have hBsq : 1 ≤ B ^ 2 := by nlinarith [sq_nonneg (B - 1)]
  have hsqrt : 1 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num)]
    all_goals nlinarith
  rcases hcontour m hm with ⟨T, hTmem, _hgood, happrox⟩
  have hT4 : 4 ≤ T := by
    have hxpow : (32 : ℝ) ≤ x ^ 5 := by
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx2 5
      norm_num at hpow ⊢
      exact hpow
    linarith [hTmem.1]
  have hTlog : 1 + Real.log (T + 6) ≤ 6 * B := by
    have hxpow7 : x ^ 5 + 7 ≤ 2 * x ^ 5 := by
      have hxpow : (32 : ℝ) ≤ x ^ 5 := by
        have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx2 5
        norm_num at hpow ⊢
        exact hpow
      linarith
    have hTplus : T + 6 ≤ 2 * x ^ 5 := by linarith [hTmem.2, hxpow7]
    have hlogT : Real.log (T + 6) ≤ Real.log (2 * x ^ 5) :=
      Real.log_le_log (by linarith) hTplus
    have hlogmul : Real.log (2 * x ^ 5) = Real.log 2 + 5 * Real.log x := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero 5 hxpos.ne'), Real.log_pow]
      norm_num
    have hlogtwo : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx2
    rw [hlogmul] at hlogT
    dsimp [B]
    linarith
  have hTlog0 : 0 ≤ 1 + Real.log (T + 6) := by
    have : 0 ≤ Real.log (T + 6) := Real.log_nonneg (by linarith)
    linarith
  have hTlogSq : (1 + Real.log (T + 6)) ^ 2 ≤ 36 * B ^ 2 := by
    calc
      (1 + Real.log (T + 6)) ^ 2 ≤ (6 * B) ^ 2 :=
        pow_le_pow_left₀ hTlog0 hTlog 2
      _ = 36 * B ^ 2 := by ring
  have hzero := hzeros x T hxpos hT4
  have hzero' :
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
        36 * Cz * Real.sqrt x * B ^ 2 := by
    calc
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
          Cz * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 := hzero
      _ ≤ Cz * Real.sqrt x * (36 * B ^ 2) := by
        gcongr
      _ = 36 * Cz * Real.sqrt x * B ^ 2 := by ring
  let q : ℝ := x ^ (-2 : ℝ)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqquarter : q ≤ (1 / 4 : ℝ) := by
    dsimp [q]
    calc
      x ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx2 (by norm_num)
      _ = 1 / 4 := by norm_num [Real.rpow_neg_natCast]
  have hq1 : q < 1 := by linarith
  have hgeom : (q / 2) * q ^ 0 / (1 - q) ≤ 1 := by
    rw [pow_zero, mul_one, div_le_iff₀ (sub_pos.mpr hq1)]
    linarith
  have hlogTerm : ‖logTerm‖ ≤ 1 := by
    have htail :=
      ExplicitFormulaAux.norm_finiteTrivialZeroSum_residues_sub_logTerm_le_geometric
        hx 0
    have htail' : ‖(0 : ℂ) - logTerm‖ ≤ (q / 2) * q ^ 0 / (1 - q) := by
      simpa [finiteTrivialZeroSum, logTerm, q] using htail
    have := htail'.trans hgeom
    simpa using this
  have hdecomp :
      ((chebyshevPsi0 x - x : ℝ) : ℂ) =
        ((chebyshevPsi0 x : ℂ) - explicitFormulaApproxWithMultiplicity x T) +
          (-finiteNontrivialZeroSumWithMultiplicity x T -
            deriv riemannZeta 0 / riemannZeta 0 + logTerm) := by
    dsimp [explicitFormulaApproxWithMultiplicity, logTerm]
    push_cast
    ring
  have hconstScale : K ≤ K * Real.sqrt x * B ^ 2 := by
    have hone : 1 ≤ Real.sqrt x * B ^ 2 := by nlinarith [hBsq]
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hone)]
  have hcontour' :
      ‖explicitFormulaApproxWithMultiplicity x T - (chebyshevPsi0 x : ℂ)‖ ≤
        Cc * B ^ 2 := by
    simpa [x, B] using happrox
  change |chebyshevPsi0 x - x| ≤ C * Real.sqrt x * B ^ 2
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdecomp]
  calc
    _ ≤ ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApproxWithMultiplicity x T‖ +
          (‖finiteNontrivialZeroSumWithMultiplicity x T‖ +
            ‖deriv riemannZeta 0 / riemannZeta 0‖ + ‖logTerm‖) := by
      calc
        _ ≤ ‖(chebyshevPsi0 x : ℂ) - explicitFormulaApproxWithMultiplicity x T‖ +
              ‖-finiteNontrivialZeroSumWithMultiplicity x T -
                deriv riemannZeta 0 / riemannZeta 0 + logTerm‖ := norm_add_le _ _
        _ ≤ _ := by
          gcongr
          calc
            _ ≤ ‖-finiteNontrivialZeroSumWithMultiplicity x T -
                    deriv riemannZeta 0 / riemannZeta 0‖ + ‖logTerm‖ := norm_add_le _ _
            _ ≤ (‖finiteNontrivialZeroSumWithMultiplicity x T‖ +
                    ‖deriv riemannZeta 0 / riemannZeta 0‖) + ‖logTerm‖ := by
              gcongr
              calc
                ‖-finiteNontrivialZeroSumWithMultiplicity x T -
                    deriv riemannZeta 0 / riemannZeta 0‖ ≤
                    ‖-finiteNontrivialZeroSumWithMultiplicity x T‖ +
                      ‖deriv riemannZeta 0 / riemannZeta 0‖ := norm_sub_le _ _
                _ = ‖finiteNontrivialZeroSumWithMultiplicity x T‖ +
                      ‖deriv riemannZeta 0 / riemannZeta 0‖ := by rw [norm_neg]
    _ ≤ Cc * B ^ 2 +
          (36 * Cz * Real.sqrt x * B ^ 2 + K) := by
      rw [norm_sub_rev]
      apply add_le_add hcontour'
      calc
        ‖finiteNontrivialZeroSumWithMultiplicity x T‖ +
              ‖deriv riemannZeta 0 / riemannZeta 0‖ + ‖logTerm‖ ≤
            36 * Cz * Real.sqrt x * B ^ 2 +
              ‖deriv riemannZeta 0 / riemannZeta 0‖ + 1 := by
          exact add_le_add (add_le_add hzero' le_rfl) hlogTerm
        _ = 36 * Cz * Real.sqrt x * B ^ 2 + K := by dsimp [K]; ring
    _ ≤ Cc * Real.sqrt x * B ^ 2 +
          (36 * Cz * Real.sqrt x * B ^ 2 +
            K * Real.sqrt x * B ^ 2) := by
      have hcontourScale : Cc * B ^ 2 ≤ Cc * Real.sqrt x * B ^ 2 := by
        have hBscale : B ^ 2 ≤ Real.sqrt x * B ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) (sq_nonneg B)]
        calc
          Cc * B ^ 2 ≤ Cc * (Real.sqrt x * B ^ 2) :=
            mul_le_mul_of_nonneg_left hBscale hCc
          _ = Cc * Real.sqrt x * B ^ 2 := by ring
      exact add_le_add hcontourScale (add_le_add_right hconstScale _)
    _ = C * Real.sqrt x * B ^ 2 := by dsimp [C]; ring

/-- Natural-point RH error bound in the exact `sqrt m * log² m` normalization
used by `RH_PsiErrorBound`. -/
theorem exists_nat_abs_chebyshevPsi0_sub_id_le_sqrt_mul_log_sq_of_RH
    (hRH : RiemannHypothesis.Statement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m →
      |chebyshevPsi0 (m : ℝ) - (m : ℝ)| ≤
        C * Real.sqrt (m : ℝ) * (Real.log (m : ℝ)) ^ 2 := by
  rcases
      exists_nat_abs_chebyshevPsi0_sub_id_le_sqrt_mul_one_add_log_sq_of_RH hRH
      with ⟨C0, hC0, hbound⟩
  let L2 : ℝ := Real.log 2
  let K : ℝ := 1 + 1 / L2
  let C : ℝ := C0 * K ^ 2
  have hL2 : 0 < L2 := by
    dsimp [L2]
    exact Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m hm
  let x : ℝ := m
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hm
  have hxone : 1 ≤ x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hL2le : L2 ≤ Real.log x := by
    dsimp [L2]
    exact Real.log_le_log (by norm_num) hx2
  have honeDiv : 1 ≤ Real.log x / L2 := by
    rw [le_div_iff₀ hL2]
    simpa using hL2le
  have hlinear : 1 + Real.log x ≤ K * Real.log x := by
    dsimp [K]
    rw [div_eq_mul_inv] at honeDiv ⊢
    nlinarith
  have hsquare : (1 + Real.log x) ^ 2 ≤ K ^ 2 * (Real.log x) ^ 2 := by
    calc
      (1 + Real.log x) ^ 2 ≤ (K * Real.log x) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hlinear 2
      _ = K ^ 2 * (Real.log x) ^ 2 := by ring
  apply (hbound m hm).trans
  calc
    C0 * Real.sqrt (m : ℝ) * (1 + Real.log (m : ℝ)) ^ 2 ≤
        C0 * Real.sqrt x * (K ^ 2 * (Real.log x) ^ 2) := by
      dsimp [x]
      gcongr
    _ = C * Real.sqrt (m : ℝ) * (Real.log (m : ℝ)) ^ 2 := by
      dsimp [C, x]
      ring

private lemma jumpVonMangoldt_natCast_eq (m : ℕ) :
    jumpVonMangoldt (m : ℝ) = vonMangoldt m := by
  classical
  rw [jumpVonMangoldt]
  split_ifs with h
  · have hspec := Classical.choose_spec h
    have heq : Classical.choose h = m := by exact_mod_cast hspec.symm
    rw [heq]
  · exact (h ⟨m, rfl⟩).elim

private lemma jumpVonMangoldt_natCast_nonneg_le_log {m : ℕ} (_hm : 2 ≤ m) :
    0 ≤ jumpVonMangoldt (m : ℝ) ∧
      jumpVonMangoldt (m : ℝ) ≤ Real.log (m : ℝ) := by
  rw [jumpVonMangoldt_natCast_eq, vonMangoldt_eq_mathlib]
  exact ⟨ArithmeticFunction.vonMangoldt_nonneg,
    ArithmeticFunction.vonMangoldt_le_log⟩

/-- The preceding midpoint estimate also controls the right-continuous
Chebyshev function at natural samples; the half-jump is absorbed using
`Λ(m) ≤ log m`. -/
theorem exists_nat_abs_chebyshevPsi_sub_id_le_sqrt_mul_log_sq_of_RH
    (hRH : RiemannHypothesis.Statement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m →
      |chebyshevPsi (m : ℝ) - (m : ℝ)| ≤
        C * Real.sqrt (m : ℝ) * (Real.log (m : ℝ)) ^ 2 := by
  rcases exists_nat_abs_chebyshevPsi0_sub_id_le_sqrt_mul_log_sq_of_RH hRH with
    ⟨C0, hC0, hmidpoint⟩
  let L2 : ℝ := Real.log 2
  let Kj : ℝ := 1 / (2 * L2)
  let C : ℝ := C0 + Kj
  have hL2 : 0 < L2 := by
    dsimp [L2]
    exact Real.log_pos (by norm_num)
  have hKj : 0 ≤ Kj := by dsimp [Kj]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m hm
  let x : ℝ := m
  let L : ℝ := Real.log x
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hm
  have hxone : 1 ≤ x := by linarith
  have hL0 : 0 ≤ L := by dsimp [L]; exact Real.log_nonneg hxone
  have hL2le : L2 ≤ L := by
    dsimp [L2, L]
    exact Real.log_le_log (by norm_num) hx2
  have hsqrt : 1 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num)]
    all_goals nlinarith
  have hprod : L * L2 ≤ Real.sqrt x * L ^ 2 := by
    calc
      L * L2 ≤ L * L := mul_le_mul_of_nonneg_left hL2le hL0
      _ = L ^ 2 := by ring
      _ ≤ Real.sqrt x * L ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) (sq_nonneg L)]
  have hlogScale : L / 2 ≤ Kj * Real.sqrt x * L ^ 2 := by
    have hden : 0 < 2 * L2 := by positivity
    calc
      L / 2 = (L * L2) / (2 * L2) := by field_simp
      _ ≤ (Real.sqrt x * L ^ 2) / (2 * L2) :=
        div_le_div_of_nonneg_right hprod hden.le
      _ = Kj * Real.sqrt x * L ^ 2 := by dsimp [Kj]; ring
  rcases jumpVonMangoldt_natCast_nonneg_le_log hm with ⟨hjump0, hjump⟩
  have hjumpScale : jumpVonMangoldt x / 2 ≤ Kj * Real.sqrt x * L ^ 2 :=
    (div_le_div_of_nonneg_right hjump (by norm_num)).trans hlogScale
  have hsplit :
      chebyshevPsi x - x =
        (chebyshevPsi0 x - x) + jumpVonMangoldt x / 2 := by
    simp [chebyshevPsi0]
    ring
  rw [hsplit]
  calc
    |(chebyshevPsi0 x - x) + jumpVonMangoldt x / 2| ≤
        |chebyshevPsi0 x - x| + |jumpVonMangoldt x / 2| := abs_add_le _ _
    _ ≤ C0 * Real.sqrt x * L ^ 2 + Kj * Real.sqrt x * L ^ 2 := by
      apply add_le_add
      · simpa [x, L] using hmidpoint m hm
      · rw [abs_of_nonneg (div_nonneg hjump0 (by norm_num))]
        exact hjumpScale
    _ = C * Real.sqrt (m : ℝ) * (Real.log (m : ℝ)) ^ 2 := by
      dsimp [C, x, L]
      ring

/-- The forward RH error implication.  The natural-point estimate is extended
to all large real `x` using `ψ(x) = ψ(floor x)`, monotonicity of the RH scale,
and the unit-size floor error. -/
theorem RH_PsiErrorBound_of_RiemannHypothesis
    (hRH : RiemannHypothesis.Statement) : RH_PsiErrorBound := by
  rcases exists_nat_abs_chebyshevPsi_sub_id_le_sqrt_mul_log_sq_of_RH hRH with
    ⟨C0, hC0, hnat⟩
  rw [RH_PsiErrorBound]
  refine Asymptotics.IsBigO.of_bound (C0 + 1) ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1 + 2)] with x hx
  let n : ℕ := Nat.floor x
  let scale : ℝ → ℝ := fun y => Real.sqrt y * (Real.log y) ^ 2
  have hxpos : 0 < x := by nlinarith [Real.exp_pos 1]
  have hx0 : 0 ≤ x := hxpos.le
  have hx2 : (2 : ℝ) ≤ x := by nlinarith [Real.exp_pos 1]
  have hn2 : 2 ≤ n := by
    dsimp [n]
    exact (Nat.le_floor_iff hx0).2 hx2
  have hnle : (n : ℝ) ≤ x := by
    dsimp [n]
    exact Nat.floor_le hx0
  have hxlt : x < (n : ℝ) + 1 := by
    dsimp [n]
    simpa using Nat.lt_floor_add_one x
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn2)
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsqrtle : Real.sqrt (n : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hnle
  have hlogle : Real.log (n : ℝ) ≤ Real.log x :=
    Real.log_le_log hnpos hnle
  have hlogsqle : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log x) ^ 2 :=
    pow_le_pow_left₀ hlogn0 hlogle 2
  have hscalele : scale (n : ℝ) ≤ scale x := by
    dsimp [scale]
    exact mul_le_mul hsqrtle hlogsqle (sq_nonneg _) (Real.sqrt_nonneg x)
  have hpsiEq : chebyshevPsi x = chebyshevPsi (n : ℝ) := by
    calc
      chebyshevPsi x = Chebyshev.psi x := chebyshevPsi_eq_mathlib x
      _ = Chebyshev.psi (n : ℝ) := by
        simpa [n] using Chebyshev.psi_eq_psi_coe_floor x
      _ = chebyshevPsi (n : ℝ) := (chebyshevPsi_eq_mathlib (n : ℝ)).symm
  have hnatx :
      |chebyshevPsi (n : ℝ) - (n : ℝ)| ≤ C0 * scale x := by
    calc
      |chebyshevPsi (n : ℝ) - (n : ℝ)| ≤
          C0 * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := hnat n hn2
      _ = C0 * scale (n : ℝ) := by dsimp [scale]; ring
      _ ≤ C0 * scale x := mul_le_mul_of_nonneg_left hscalele hC0
  have hfloor : |(n : ℝ) - x| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hnle)]
    linarith
  have hexple : Real.exp 1 ≤ x := by linarith
  have hlogone : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxpos).2 hexple
  have hsqrtone : 1 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num)]
    all_goals nlinarith
  have hscaleone : 1 ≤ scale x := by
    dsimp [scale]
    have hlogsqone : 1 ≤ (Real.log x) ^ 2 := by nlinarith
    nlinarith [mul_le_mul hsqrtone hlogsqone zero_le_one (Real.sqrt_nonneg x)]
  have herrEq :
      chebyshevPsi x - x =
        (chebyshevPsi (n : ℝ) - (n : ℝ)) + ((n : ℝ) - x) := by
    rw [hpsiEq]
    ring
  have hscale0 : 0 ≤ scale x := by
    dsimp [scale]
    exact mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hscale0]
  calc
    |chebyshevPsi x - x| =
        |(chebyshevPsi (n : ℝ) - (n : ℝ)) + ((n : ℝ) - x)| := by rw [herrEq]
    _ ≤ |chebyshevPsi (n : ℝ) - (n : ℝ)| + |(n : ℝ) - x| := abs_add_le _ _
    _ ≤ C0 * scale x + 1 := add_le_add hnatx hfloor
    _ ≤ C0 * scale x + scale x := add_le_add_right hscaleone _
    _ = (C0 + 1) * scale x := by ring

/-- RH implies the corresponding Chebyshev-`theta` error bound. -/
theorem RH_ThetaErrorBound_of_RiemannHypothesis
    (hRH : RiemannHypothesis.Statement) : RH_ThetaErrorBound :=
  RH_ThetaErrorBound_of_RH_PsiErrorBound
    (RH_PsiErrorBound_of_RiemannHypothesis hRH)

/-- Forward von Koch implication from RH to the prime-counting `Li` error
bound.  The explicit-formula argument supplies the `psi` estimate and the
existing quantitative partial-summation theorem supplies this endpoint. -/
theorem RH_PrimeCountingLiErrorBound_of_RiemannHypothesis
    (hRH : RiemannHypothesis.Statement) : RH_PrimeCountingLiErrorBound :=
  RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound
    (RH_PsiErrorBound_of_RiemannHypothesis hRH)

/-- Forward RH implication in the pointwise textbook prime-counting
normalization. -/
theorem RH_ErrorBound_of_RiemannHypothesis
    (hRH : RiemannHypothesis.Statement) : RH_ErrorBound :=
  RH_ErrorBound_of_RH_PsiErrorBound
    (RH_PsiErrorBound_of_RiemannHypothesis hRH)

/-- The RH-scale Chebyshev-`ψ` error is equivalent to the Riemann hypothesis.
The forward implication is the quantitative explicit-formula argument above;
the reverse implication is the proved Mellin/Landau zero-exclusion bridge. -/
theorem riemannHypothesis_iff_RH_PsiErrorBound :
    RiemannHypothesis.Statement ↔ RH_PsiErrorBound := by
  constructor
  · exact RH_PsiErrorBound_of_RiemannHypothesis
  · intro hψ
    exact PrimeNumberTheorem.rh_statement_iff_mathlib.mp
      (ZeroFreeRegion.riemannHypothesis_of_RH_PsiErrorBound hψ)

end ExplicitFormulaResidues
end PrimeNumberTheorem
