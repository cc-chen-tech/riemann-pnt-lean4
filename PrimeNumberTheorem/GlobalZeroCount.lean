import PrimeNumberTheorem.QuantitativeGoodHeight
import Mathlib.NumberTheory.Harmonic.Bounds

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

/-- Total analytic multiplicity of the nontrivial zeta zeros of absolute
ordinate at most `T`. -/
noncomputable def globalZeroMultiplicity (T : ℝ) : ℝ :=
  ∑ ρ ∈ nontrivialZerosFinset T,
    (analyticOrderNatAt riemannZeta ρ : ℝ)

lemma globalZeroMultiplicity_nonneg (T : ℝ) :
    0 ≤ globalZeroMultiplicity T := by
  unfold globalZeroMultiplicity
  exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- Total analytic multiplicity of the nontrivial zeta zeros of absolute
ordinate at most `T`, weighted by the reciprocal of the zero's norm. -/
noncomputable def globalReciprocalZeroMultiplicity (T : ℝ) : ℝ :=
  ∑ ρ ∈ nontrivialZerosFinset T,
    (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖

lemma globalReciprocalZeroMultiplicity_nonneg (T : ℝ) :
    0 ≤ globalReciprocalZeroMultiplicity T := by
  unfold globalReciprocalZeroMultiplicity
  exact Finset.sum_nonneg fun ρ _ =>
    div_nonneg (Nat.cast_nonneg _) (norm_nonneg ρ)

private noncomputable def integerZeroWindow (n : ℕ) : Finset ℂ :=
  (nontrivialZerosFinset ((n : ℝ) + 2)).filter fun ρ : ℂ =>
    (n : ℝ) - 1 / 4 ≤ |ρ.im| ∧ |ρ.im| ≤ (n : ℝ) + 5 / 4

private lemma localZeroMultiplicity_nat (n : ℕ) :
    localZeroMultiplicity (n : ℝ) =
      ∑ ρ ∈ integerZeroWindow n,
        (analyticOrderNatAt riemannZeta ρ : ℝ) := by
  rfl

/-- Every high zero in the `n`th floor fiber belongs to the fixed-width local
window centered at `n`. -/
private lemma floorFiber_subset_integerZeroWindow
    {T : ℝ} {n : ℕ} :
    (nontrivialZerosFinset T).filter (fun ρ : ℂ =>
      ¬|ρ.im| ≤ 4 ∧ Nat.floor |ρ.im| = n) ⊆ integerZeroWindow n := by
  intro ρ hρ
  rcases Finset.mem_filter.mp hρ with ⟨hρT, hhigh, hfloor⟩
  rcases mem_nontrivialZerosFinset.mp hρT with ⟨hzero, _hρT⟩
  have him_nonneg : 0 ≤ |ρ.im| := abs_nonneg _
  have hn_le : (n : ℝ) ≤ |ρ.im| := by
    rw [← hfloor]
    exact Nat.floor_le him_nonneg
  have him_lt : |ρ.im| < (n : ℝ) + 1 := by
    rw [← hfloor]
    exact Nat.lt_floor_add_one _
  apply Finset.mem_filter.mpr
  refine ⟨mem_nontrivialZerosFinset.mpr ⟨hzero, ?_⟩, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-- The number of nontrivial zeta zeros up to height `T`, counted with analytic
multiplicity, is `O(T log T)`.  This is obtained by covering the high zeros by
integer translates of the fixed-width Jensen window. -/
theorem exists_globalZeroMultiplicity_le_mul_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      globalZeroMultiplicity T ≤ C * T * (1 + Real.log (T + 6)) := by
  classical
  rcases exists_localZeroMultiplicity_le_log_bound with ⟨B, hB, hlocal⟩
  let M₀ : ℝ := globalZeroMultiplicity 4
  refine ⟨M₀ + 2 * B, add_nonneg (globalZeroMultiplicity_nonneg 4)
    (mul_nonneg (by norm_num) hB), ?_⟩
  intro T hT
  let S := nontrivialZerosFinset T
  let Slow := S.filter fun ρ : ℂ => |ρ.im| ≤ 4
  let Shigh := S.filter fun ρ : ℂ => ¬|ρ.im| ≤ 4
  let I := Finset.Icc 4 (Nat.floor T)
  let f : ℂ → ℝ := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ)
  have hTnonneg : 0 ≤ T := by linarith
  have hsplit : (∑ ρ ∈ S, f ρ) =
      (∑ ρ ∈ Slow, f ρ) + ∑ ρ ∈ Shigh, f ρ := by
    symm
    exact Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ => |ρ.im| ≤ 4) f
  have hlow_subset : Slow ⊆ nontrivialZerosFinset 4 := by
    intro ρ hρ
    rcases Finset.mem_filter.mp hρ with ⟨hρS, him⟩
    exact mem_nontrivialZerosFinset.mpr
      ⟨(mem_nontrivialZerosFinset.mp hρS).1, him⟩
  have hlow : (∑ ρ ∈ Slow, f ρ) ≤ M₀ := by
    dsimp [M₀, globalZeroMultiplicity]
    exact Finset.sum_le_sum_of_subset_of_nonneg hlow_subset
      (fun ρ _hρ _hnot => Nat.cast_nonneg _)
  have hmaps (ρ : ℂ) (hρ : ρ ∈ Shigh) : Nat.floor |ρ.im| ∈ I := by
    rcases Finset.mem_filter.mp hρ with ⟨hρS, hnotlow⟩
    have himT := (mem_nontrivialZerosFinset.mp hρS).2
    apply Finset.mem_Icc.mpr
    constructor
    · apply Nat.le_floor
      exact (lt_of_not_ge hnotlow).le
    · exact Nat.floor_mono himT
  have hfiber : (∑ ρ ∈ Shigh, f ρ) =
      ∑ n ∈ I, ∑ ρ ∈ Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n), f ρ := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps f
  have hfiber_le (n : ℕ) (hn : n ∈ I) :
      (∑ ρ ∈ Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n), f ρ) ≤
        B * (1 + Real.log (T + 6)) := by
    have hn4 : 4 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnTfloor : n ≤ Nat.floor T := (Finset.mem_Icc.mp hn).2
    have hnT : (n : ℝ) ≤ T := by
      exact (Nat.cast_le.mpr hnTfloor).trans (Nat.floor_le hTnonneg)
    have hsubset :
        Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n) ⊆ integerZeroWindow n := by
      intro ρ hρ
      rcases Finset.mem_filter.mp hρ with ⟨hρhigh, hfloor⟩
      rcases Finset.mem_filter.mp hρhigh with ⟨hρS, hnotlow⟩
      apply floorFiber_subset_integerZeroWindow
      exact Finset.mem_filter.mpr ⟨hρS, hnotlow, hfloor⟩
    have hsum_local :
        (∑ ρ ∈ Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n), f ρ) ≤
          localZeroMultiplicity (n : ℝ) := by
      rw [localZeroMultiplicity_nat]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun ρ _hρ _hnot => Nat.cast_nonneg _)
    have hlocaln := hlocal (n : ℝ) (by exact_mod_cast hn4)
    have hlog : Real.log ((n : ℝ) + 6) ≤ Real.log (T + 6) := by
      apply Real.log_le_log
      · positivity
      · linarith
    have hscale : B * (1 + Real.log ((n : ℝ) + 6)) ≤
        B * (1 + Real.log (T + 6)) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hB
    exact hsum_local.trans (hlocaln.trans hscale)
  have hhigh : (∑ ρ ∈ Shigh, f ρ) ≤
      2 * B * T * (1 + Real.log (T + 6)) := by
    rw [hfiber]
    calc
      (∑ n ∈ I, ∑ ρ ∈ Shigh.filter
          (fun ρ : ℂ => Nat.floor |ρ.im| = n), f ρ) ≤
          ∑ _n ∈ I, B * (1 + Real.log (T + 6)) :=
        Finset.sum_le_sum fun n hn => hfiber_le n hn
      _ = (I.card : ℝ) * (B * (1 + Real.log (T + 6))) := by
        simp
      _ ≤ (2 * T) * (B * (1 + Real.log (T + 6))) := by
        have hI_subset : I ⊆ Finset.range (Nat.floor T + 1) := by
          intro n hn
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
        have hcard_nat : I.card ≤ Nat.floor T + 1 := by
          simpa using Finset.card_le_card hI_subset
        have hcard_real : (I.card : ℝ) ≤ T + 1 := by
          calc
            (I.card : ℝ) ≤ (Nat.floor T : ℝ) + 1 := by exact_mod_cast hcard_nat
            _ ≤ T + 1 := by linarith [Nat.floor_le hTnonneg]
        have hcard_two : (I.card : ℝ) ≤ 2 * T := by linarith
        have hfactor_nonneg : 0 ≤ B * (1 + Real.log (T + 6)) := by
          apply mul_nonneg hB
          have : 0 ≤ Real.log (T + 6) := Real.log_nonneg (by linarith)
          linarith
        exact mul_le_mul_of_nonneg_right hcard_two hfactor_nonneg
      _ = 2 * B * T * (1 + Real.log (T + 6)) := by ring
  have hlog_nonneg : 0 ≤ Real.log (T + 6) := Real.log_nonneg (by linarith)
  have hTL : 1 ≤ T * (1 + Real.log (T + 6)) := by nlinarith
  change (∑ ρ ∈ S, f ρ) ≤ _
  rw [hsplit]
  dsimp [M₀] at hlow ⊢
  nlinarith [globalZeroMultiplicity_nonneg 4]

/-- The reciprocal-norm weighted analytic multiplicity of nontrivial zeta
zeros up to height `T` is `O(log^2 T)`. -/
theorem exists_globalReciprocalZeroMultiplicity_le_log_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      globalReciprocalZeroMultiplicity T ≤
        C * (1 + Real.log (T + 6)) ^ 2 := by
  classical
  rcases exists_localZeroMultiplicity_le_log_bound with ⟨B, hB, hlocal⟩
  let M₀ : ℝ := globalReciprocalZeroMultiplicity 4
  refine ⟨M₀ + B, add_nonneg (globalReciprocalZeroMultiplicity_nonneg 4) hB, ?_⟩
  intro T hT
  let S := nontrivialZerosFinset T
  let Slow := S.filter fun ρ : ℂ => |ρ.im| ≤ 4
  let Shigh := S.filter fun ρ : ℂ => ¬|ρ.im| ≤ 4
  let I := Finset.Icc 4 (Nat.floor T)
  let f : ℂ → ℝ := fun ρ =>
    (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖
  have hTnonneg : 0 ≤ T := by linarith
  have hsplit : (∑ ρ ∈ S, f ρ) =
      (∑ ρ ∈ Slow, f ρ) + ∑ ρ ∈ Shigh, f ρ := by
    symm
    exact Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ => |ρ.im| ≤ 4) f
  have hlow_subset : Slow ⊆ nontrivialZerosFinset 4 := by
    intro ρ hρ
    rcases Finset.mem_filter.mp hρ with ⟨hρS, him⟩
    exact mem_nontrivialZerosFinset.mpr
      ⟨(mem_nontrivialZerosFinset.mp hρS).1, him⟩
  have hlow : (∑ ρ ∈ Slow, f ρ) ≤ M₀ := by
    dsimp [M₀, globalReciprocalZeroMultiplicity]
    exact Finset.sum_le_sum_of_subset_of_nonneg hlow_subset
      (fun ρ _hρ _hnot => div_nonneg (Nat.cast_nonneg _) (norm_nonneg ρ))
  have hmaps (ρ : ℂ) (hρ : ρ ∈ Shigh) : Nat.floor |ρ.im| ∈ I := by
    rcases Finset.mem_filter.mp hρ with ⟨hρS, hnotlow⟩
    have himT := (mem_nontrivialZerosFinset.mp hρS).2
    apply Finset.mem_Icc.mpr
    constructor
    · apply Nat.le_floor
      exact (lt_of_not_ge hnotlow).le
    · exact Nat.floor_mono himT
  have hfiber : (∑ ρ ∈ Shigh, f ρ) =
      ∑ n ∈ I, ∑ ρ ∈ Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n), f ρ := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps f
  have hfiber_le (n : ℕ) (hn : n ∈ I) :
      (∑ ρ ∈ Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n), f ρ) ≤
        B * (1 + Real.log (T + 6)) / (n : ℝ) := by
    have hn4 : 4 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnTfloor : n ≤ Nat.floor T := (Finset.mem_Icc.mp hn).2
    have hnT : (n : ℝ) ≤ T := by
      exact (Nat.cast_le.mpr hnTfloor).trans (Nat.floor_le hTnonneg)
    have hnpos : 0 < (n : ℝ) := by positivity
    have hsubset :
        Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n) ⊆ integerZeroWindow n := by
      intro ρ hρ
      rcases Finset.mem_filter.mp hρ with ⟨hρhigh, hfloor⟩
      rcases Finset.mem_filter.mp hρhigh with ⟨hρS, hnotlow⟩
      apply floorFiber_subset_integerZeroWindow
      exact Finset.mem_filter.mpr ⟨hρS, hnotlow, hfloor⟩
    have hweighted :
        (∑ ρ ∈ Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n), f ρ) ≤
          (∑ ρ ∈ Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n),
            (analyticOrderNatAt riemannZeta ρ : ℝ)) / (n : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro ρ hρ
      rcases Finset.mem_filter.mp hρ with ⟨hρhigh, hfloor⟩
      have hn_im : (n : ℝ) ≤ |ρ.im| := by
        rw [← hfloor]
        exact Nat.floor_le (abs_nonneg _)
      have hn_norm : (n : ℝ) ≤ ‖ρ‖ :=
        hn_im.trans (Complex.abs_im_le_norm ρ)
      dsimp [f]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hnpos hn_norm
    have hsum_local :
        (∑ ρ ∈ Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n),
          (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ localZeroMultiplicity (n : ℝ) := by
      rw [localZeroMultiplicity_nat]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun ρ _hρ _hnot => Nat.cast_nonneg _)
    have hlocaln := hlocal (n : ℝ) (by exact_mod_cast hn4)
    have hlog : Real.log ((n : ℝ) + 6) ≤ Real.log (T + 6) := by
      apply Real.log_le_log
      · positivity
      · linarith
    have hscale : B * (1 + Real.log ((n : ℝ) + 6)) ≤
        B * (1 + Real.log (T + 6)) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hB
    calc
      (∑ ρ ∈ Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n), f ρ) ≤
          (∑ ρ ∈ Shigh.filter (fun ρ : ℂ => Nat.floor |ρ.im| = n),
            (analyticOrderNatAt riemannZeta ρ : ℝ)) / (n : ℝ) := hweighted
      _ ≤ localZeroMultiplicity (n : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hsum_local hnpos.le
      _ ≤ (B * (1 + Real.log ((n : ℝ) + 6))) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlocaln hnpos.le
      _ ≤ B * (1 + Real.log (T + 6)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hscale hnpos.le
  have hreciprocal_sum :
      (∑ n ∈ I, (n : ℝ)⁻¹) ≤ 1 + Real.log (T + 6) := by
    have hI_subset : I ⊆ Finset.Icc 1 (Nat.floor T) := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1.trans' (by norm_num),
        (Finset.mem_Icc.mp hn).2⟩
    have hsum_harmonic :
        (∑ n ∈ I, (n : ℝ)⁻¹) ≤ (harmonic (Nat.floor T) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_le_sum_of_subset_of_nonneg hI_subset
        (fun n _hn _hnot => inv_nonneg.mpr (Nat.cast_nonneg n))
    have hharmonic : (harmonic (Nat.floor T) : ℝ) ≤ 1 + Real.log T :=
      harmonic_floor_le_one_add_log T (by linarith)
    have hlog : Real.log T ≤ Real.log (T + 6) := by
      apply Real.log_le_log
      · linarith
      · linarith
    linarith
  have hhigh : (∑ ρ ∈ Shigh, f ρ) ≤
      B * (1 + Real.log (T + 6)) ^ 2 := by
    rw [hfiber]
    calc
      (∑ n ∈ I, ∑ ρ ∈ Shigh.filter
          (fun ρ : ℂ => Nat.floor |ρ.im| = n), f ρ) ≤
          ∑ n ∈ I, B * (1 + Real.log (T + 6)) / (n : ℝ) :=
        Finset.sum_le_sum fun n hn => hfiber_le n hn
      _ = B * (1 + Real.log (T + 6)) * ∑ n ∈ I, (n : ℝ)⁻¹ := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.mul_sum]
      _ ≤ B * (1 + Real.log (T + 6)) *
          (1 + Real.log (T + 6)) := by
        apply mul_le_mul_of_nonneg_left hreciprocal_sum
        exact mul_nonneg hB (by
          have := Real.log_nonneg (show 1 ≤ T + 6 by linarith)
          linarith)
      _ = B * (1 + Real.log (T + 6)) ^ 2 := by ring
  have hlog_nonneg : 0 ≤ Real.log (T + 6) := Real.log_nonneg (by linarith)
  have hlog_sq : 1 ≤ (1 + Real.log (T + 6)) ^ 2 := by nlinarith
  change (∑ ρ ∈ S, f ρ) ≤ _
  rw [hsplit]
  dsimp [M₀] at hlow ⊢
  nlinarith [globalReciprocalZeroMultiplicity_nonneg 4]

/-- Under RH, the multiplicity-aware zero sum in the truncated explicit formula
is controlled by `sqrt x` times the reciprocal zero-multiplicity sum. -/
theorem norm_finiteNontrivialZeroSumWithMultiplicity_le_sqrt_mul_globalReciprocal_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x T : ℝ} (hx : 0 < x) :
    ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
      Real.sqrt x * globalReciprocalZeroMultiplicity T := by
  classical
  unfold finiteNontrivialZeroSumWithMultiplicity
  calc
    ‖∑ ρ ∈ nontrivialZerosFinset T,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        ∑ ρ ∈ nontrivialZerosFinset T,
          ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ :=
      norm_sum_le _ _
    _ = ∑ ρ ∈ nontrivialZerosFinset T,
          Real.sqrt x * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by
      refine Finset.sum_congr rfl ?_
      intro ρ hρ
      have hzero := (mem_nontrivialZerosFinset.mp hρ).1
      calc
        ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ =
            ‖(analyticOrderNatAt riemannZeta ρ : ℂ)‖ *
              ‖(x : ℂ) ^ ρ / ρ‖ := by
          rw [mul_div_assoc, norm_mul]
        _ = (analyticOrderNatAt riemannZeta ρ : ℝ) *
              (Real.sqrt x / ‖ρ‖) := by
          rw [norm_zero_contribution_eq_sqrt_of_RH hRH hzero hx]
          simp
        _ = Real.sqrt x *
              ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by
          ring
    _ = Real.sqrt x * globalReciprocalZeroMultiplicity T := by
      unfold globalReciprocalZeroMultiplicity
      rw [Finset.mul_sum]

/-- Under RH, the complete multiplicity-aware finite zero sum is
`O(sqrt x log² T)`, uniformly for `T ≥ 4`. -/
theorem exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_sqrt_mul_log_sq_of_RH
    (hRH : RiemannHypothesis.Statement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x T : ℝ, 0 < x → 4 ≤ T →
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
        C * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 := by
  rcases exists_globalReciprocalZeroMultiplicity_le_log_sq with
    ⟨C, hC, hreciprocal⟩
  refine ⟨C, hC, ?_⟩
  intro x T hx hT
  calc
    ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
        Real.sqrt x * globalReciprocalZeroMultiplicity T :=
      norm_finiteNontrivialZeroSumWithMultiplicity_le_sqrt_mul_globalReciprocal_of_RH
        hRH hx
    _ ≤ Real.sqrt x * (C * (1 + Real.log (T + 6)) ^ 2) :=
      mul_le_mul_of_nonneg_left (hreciprocal T hT) (Real.sqrt_nonneg x)
    _ = C * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 := by ring

/-- The number of distinct nontrivial zeros up to height `T` also satisfies
the global `O(T log T)` bound. -/
theorem exists_card_nontrivialZerosFinset_le_mul_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      ((nontrivialZerosFinset T).card : ℝ) ≤
        C * T * (1 + Real.log (T + 6)) := by
  rcases exists_globalZeroMultiplicity_le_mul_log with ⟨C, hC, hglobal⟩
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hcard_le : ((nontrivialZerosFinset T).card : ℝ) ≤
      globalZeroMultiplicity T := by
    rw [show ((nontrivialZerosFinset T).card : ℝ) =
        ∑ ρ ∈ nontrivialZerosFinset T, (1 : ℝ) by simp]
    unfold globalZeroMultiplicity
    apply Finset.sum_le_sum
    intro ρ hρ
    have hzero := (mem_nontrivialZerosFinset.mp hρ).1
    have hρ1 : ρ ≠ 1 := by
      intro hρeq
      have hre := congrArg Complex.re hρeq
      simp at hre
      linarith [hzero.2.2]
    have hpos : 0 < analyticOrderNatAt riemannZeta ρ :=
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hρ1 hzero.1
    exact_mod_cast hpos
  exact hcard_le.trans (hglobal T hT)

end ExplicitFormulaAux
end PrimeNumberTheorem
