import PrimeNumberTheorem.ExplicitFormulaUniformNaturalHeight
import PrimeNumberTheorem.PNTFromDynamicPerron
import PrimeNumberTheorem.VKEdgeZeroClusterClosedTermsL2

open Complex Set

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

/-!
# Floor and midpoint bookkeeping for real explicit-formula samples
-/

/-- The real jump of Chebyshev's function is nonnegative and bounded by the
logarithm at every `x >= 1`. -/
theorem jumpVonMangoldt_nonneg_le_log
    {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ PrimeNumberTheorem.jumpVonMangoldt x ∧
      PrimeNumberTheorem.jumpVonMangoldt x ≤ Real.log x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  classical
  rw [PrimeNumberTheorem.jumpVonMangoldt]
  split_ifs with h
  · have hchoose := Classical.choose_spec h
    rw [vonMangoldt_eq_mathlib]
    constructor
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · calc
        ArithmeticFunction.vonMangoldt (Classical.choose h) ≤
            Real.log ((Classical.choose h : ℕ) : ℝ) :=
          ArithmeticFunction.vonMangoldt_le_log
        _ = Real.log x := by rw [← hchoose]
  · exact ⟨le_rfl, hlog⟩

/-- Chebyshev's right-continuous `psi` is unchanged when a real argument is
replaced by its natural floor. -/
theorem chebyshevPsi_eq_floor (x : ℝ) :
    chebyshevPsi x =
      chebyshevPsi (Nat.floor x : ℝ) := by
  calc
    chebyshevPsi x = Chebyshev.psi x := chebyshevPsi_eq_mathlib x
    _ = Chebyshev.psi (Nat.floor x : ℝ) := by
      simpa using Chebyshev.psi_eq_psi_coe_floor x
    _ = chebyshevPsi (Nat.floor x : ℝ) :=
      (chebyshevPsi_eq_mathlib (Nat.floor x : ℝ)).symm

/-- Exact midpoint correction between a real sample and its natural floor. -/
theorem chebyshevPsi0_sub_floor_eq (x : ℝ) :
    chebyshevPsi0 x - chebyshevPsi0 (Nat.floor x : ℝ) =
      (PrimeNumberTheorem.jumpVonMangoldt (Nat.floor x : ℝ) -
        PrimeNumberTheorem.jumpVonMangoldt x) / 2 := by
  rw [chebyshevPsi0, chebyshevPsi0, chebyshevPsi_eq_floor x]
  ring

/-- The midpoint discrepancy between `x` and `floor x` costs at most the two
logarithmic jumps. -/
theorem abs_chebyshevPsi0_sub_floor_le_log
    {x : ℝ} (hx : 3 ≤ x) :
    |chebyshevPsi0 x - chebyshevPsi0 (Nat.floor x : ℝ)| ≤
      (Real.log (Nat.floor x : ℝ) + Real.log x) / 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hm : 3 ≤ Nat.floor x := by
    apply Nat.le_floor
    norm_num
    exact hx
  have hm1 : (1 : ℝ) ≤ (Nat.floor x : ℝ) := by
    exact_mod_cast (show 1 ≤ Nat.floor x by omega)
  rcases jumpVonMangoldt_natCast_nonneg_le_log
      (show 2 ≤ Nat.floor x by omega) with
    ⟨hjm0, hjm⟩
  rcases jumpVonMangoldt_nonneg_le_log
      (show 1 ≤ x by linarith) with
    ⟨hjx0, hjx⟩
  rw [chebyshevPsi0_sub_floor_eq]
  have habs :
      |PrimeNumberTheorem.jumpVonMangoldt (Nat.floor x : ℝ) -
          PrimeNumberTheorem.jumpVonMangoldt x| ≤
        Real.log (Nat.floor x : ℝ) + Real.log x := by
    calc
      |PrimeNumberTheorem.jumpVonMangoldt (Nat.floor x : ℝ) -
          PrimeNumberTheorem.jumpVonMangoldt x| ≤
          |PrimeNumberTheorem.jumpVonMangoldt (Nat.floor x : ℝ)| +
            |PrimeNumberTheorem.jumpVonMangoldt x| := abs_sub _ _
      _ = PrimeNumberTheorem.jumpVonMangoldt (Nat.floor x : ℝ) +
            PrimeNumberTheorem.jumpVonMangoldt x := by
          rw [abs_of_nonneg hjm0, abs_of_nonneg hjx0]
      _ ≤ Real.log (Nat.floor x : ℝ) + Real.log x :=
        add_le_add hjm hjx
  rw [abs_div]
  norm_num
  exact div_le_div_of_nonneg_right habs (by norm_num)

/-- At fixed height, the complete explicit-formula approximation differs
between `x` and `floor x` by the moving-zero variation plus two uniformly
bounded closed packages. -/
theorem norm_explicitFormulaApproxWithMultiplicity_sub_floor_le
    {x T : ℝ} (hx : 3 ≤ x) :
    ‖explicitFormulaApproxWithMultiplicity x T -
        explicitFormulaApproxWithMultiplicity (Nat.floor x : ℝ) T‖ ≤
      (1 + globalZeroMultiplicity T) *
          |x - (Nat.floor x : ℝ)| +
        2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound := by
  have hxpos : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hm : 3 ≤ Nat.floor x := by
    apply Nat.le_floor
    norm_num
    exact hx
  have hmreal : (3 : ℝ) ≤ (Nat.floor x : ℝ) := by
    exact_mod_cast hm
  have hmpos : 0 < (Nat.floor x : ℝ) := by linarith
  have hm1 : 1 ≤ (Nat.floor x : ℝ) := by linarith
  have hlogx : 1 ≤ Real.log x := by
    exact (Real.le_log_iff_exp_le hxpos).2
      (Real.exp_one_lt_three.le.trans hx)
  have hlogm : 1 ≤ Real.log (Nat.floor x : ℝ) := by
    exact (Real.le_log_iff_exp_le hmpos).2
      (Real.exp_one_lt_three.le.trans hmreal)
  let closed : ℝ → ℂ :=
    ZeroForcedOscillation.zeroPackageClosedTerms
  have happ (z : ℝ) (hz : 0 < z) :
      explicitFormulaApproxWithMultiplicity z T =
        ((z : ℂ) - finiteNontrivialZeroSumWithMultiplicity z T) -
          closed (Real.log z) := by
    dsimp [closed, ZeroForcedOscillation.zeroPackageClosedTerms,
      explicitFormulaApproxWithMultiplicity]
    rw [Real.exp_log hz]
    ring
  have hmove :=
    norm_main_sub_finiteZeroSum_sub_le
      (T := T) hx1 hm1
  have hclosedx :
      ‖closed (Real.log x)‖ ≤
        VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound := by
    exact
      VKEdgePiOverTwo.norm_zeroPackageClosedTerms_le_uniformBound hlogx
  have hclosedm :
      ‖closed (Real.log (Nat.floor x : ℝ))‖ ≤
        VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound := by
    exact
      VKEdgePiOverTwo.norm_zeroPackageClosedTerms_le_uniformBound hlogm
  rw [happ x hxpos, happ (Nat.floor x : ℝ) hmpos]
  calc
    ‖(((x : ℂ) - finiteNontrivialZeroSumWithMultiplicity x T) -
          closed (Real.log x)) -
        (((Nat.floor x : ℝ) : ℂ) -
            finiteNontrivialZeroSumWithMultiplicity (Nat.floor x : ℝ) T -
          closed (Real.log (Nat.floor x : ℝ)))‖ ≤
        ‖((x : ℂ) - finiteNontrivialZeroSumWithMultiplicity x T) -
          (((Nat.floor x : ℝ) : ℂ) -
            finiteNontrivialZeroSumWithMultiplicity (Nat.floor x : ℝ) T)‖ +
          ‖closed (Real.log x) -
            closed (Real.log (Nat.floor x : ℝ))‖ := by
      have hrearrange :
          (((x : ℂ) - finiteNontrivialZeroSumWithMultiplicity x T) -
              closed (Real.log x)) -
            ((((Nat.floor x : ℝ) : ℂ) -
                finiteNontrivialZeroSumWithMultiplicity (Nat.floor x : ℝ) T) -
              closed (Real.log (Nat.floor x : ℝ))) =
            (((x : ℂ) - finiteNontrivialZeroSumWithMultiplicity x T) -
              (((Nat.floor x : ℝ) : ℂ) -
                finiteNontrivialZeroSumWithMultiplicity (Nat.floor x : ℝ) T)) -
              (closed (Real.log x) -
                closed (Real.log (Nat.floor x : ℝ))) := by ring
      rw [hrearrange]
      exact norm_sub_le _ _
    _ ≤ (1 + globalZeroMultiplicity T) *
          |x - (Nat.floor x : ℝ)| +
        (‖closed (Real.log x)‖ +
          ‖closed (Real.log (Nat.floor x : ℝ))‖) := by
      exact add_le_add hmove (norm_sub_le _ _)
    _ ≤ (1 + globalZeroMultiplicity T) *
          |x - (Nat.floor x : ℝ)| +
        2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound := by
      gcongr
      linarith

/-- Any natural-point bound at `floor x` promotes to a real-point bound at
`x`, with every interpolation cost displayed explicitly. -/
theorem
    norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_floor
    {x T B : ℝ} (hx : 3 ≤ x)
    (hfloor :
      ‖explicitFormulaApproxWithMultiplicity (Nat.floor x : ℝ) T -
          (chebyshevPsi0 (Nat.floor x : ℝ) : ℂ)‖ ≤ B) :
    ‖explicitFormulaApproxWithMultiplicity x T -
        (chebyshevPsi0 x : ℂ)‖ ≤
      B +
        (1 + globalZeroMultiplicity T) *
          |x - (Nat.floor x : ℝ)| +
        2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound +
        (Real.log (Nat.floor x : ℝ) + Real.log x) / 2 := by
  have happ :=
    norm_explicitFormulaApproxWithMultiplicity_sub_floor_le
      (T := T) hx
  have hpsi := abs_chebyshevPsi0_sub_floor_le_log hx
  have hdecomp :
      explicitFormulaApproxWithMultiplicity x T -
          (chebyshevPsi0 x : ℂ) =
        (explicitFormulaApproxWithMultiplicity (Nat.floor x : ℝ) T -
          (chebyshevPsi0 (Nat.floor x : ℝ) : ℂ)) +
        (explicitFormulaApproxWithMultiplicity x T -
          explicitFormulaApproxWithMultiplicity (Nat.floor x : ℝ) T) +
        ((chebyshevPsi0 (Nat.floor x : ℝ) -
          chebyshevPsi0 x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hdecomp]
  calc
    _ ≤
        ‖explicitFormulaApproxWithMultiplicity (Nat.floor x : ℝ) T -
          (chebyshevPsi0 (Nat.floor x : ℝ) : ℂ)‖ +
        ‖explicitFormulaApproxWithMultiplicity x T -
          explicitFormulaApproxWithMultiplicity (Nat.floor x : ℝ) T‖ +
        ‖((chebyshevPsi0 (Nat.floor x : ℝ) -
          chebyshevPsi0 x : ℝ) : ℂ)‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add_left (norm_add_le _ _) _)
    _ ≤ B +
        ((1 + globalZeroMultiplicity T) *
          |x - (Nat.floor x : ℝ)| +
          2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound) +
        (Real.log (Nat.floor x : ℝ) + Real.log x) / 2 := by
      rw [norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact add_le_add (add_le_add hfloor happ) hpsi
    _ = B +
        (1 + globalZeroMultiplicity T) *
          |x - (Nat.floor x : ℝ)| +
        2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound +
        (Real.log (Nat.floor x : ℝ) + Real.log x) / 2 := by ring

end ExplicitFormulaAux
end PrimeNumberTheorem
