import PrimeNumberTheorem.MWKFCubicAFEShiftedIntegral
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.GCD

open Filter MeasureTheory
open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Exact single-variable parametrization before Poisson summation

The equation `n*s-m*r=delta` is solved with `m>0`, `delta+m*r>0`, and
`s | delta+m*r`.  The positivity and divisibility hypotheses are retained:
integer division and `toNat` do not introduce spurious zero or rounded solutions.
The actual physical integrals, not a replacement model, are reindexed below.
-/

def cubicAFEProgressionNumerator (d e : ℕ) (δ : ℤ) (m : ℕ) : ℤ :=
  δ + (m : ℤ) * ((d / Nat.gcd d e : ℕ) : ℤ)

/-- The exact positive part of a linear congruence in `m`. -/
def cubicAFEProgression (d e : ℕ) (δ : ℤ) : Set ℕ :=
  {m | 0 < m ∧ 0 < cubicAFEProgressionNumerator d e δ m ∧
    ((e / Nat.gcd d e : ℕ) : ℤ) ∣ cubicAFEProgressionNumerator d e δ m}

/-- Zero-based AFE indices recovered from the positive variable `m`. -/
def cubicAFEProgressionPair (d e : ℕ) (δ : ℤ) (m : ℕ) : ℕ × ℕ :=
  (m - 1, (cubicAFEProgressionNumerator d e δ m /
    ((e / Nat.gcd d e : ℕ) : ℤ)).toNat - 1)

theorem cubicAFEProgression_mem_iff_modEq (d e : ℕ) (δ : ℤ) (m : ℕ) :
    m ∈ cubicAFEProgression d e δ ↔
      0 < m ∧ 0 < cubicAFEProgressionNumerator d e δ m ∧
        Int.ModEq ((e / Nat.gcd d e : ℕ) : ℤ)
          ((m : ℤ) * ((d / Nat.gcd d e : ℕ) : ℤ)) (-δ) := by
  have hsign : -δ - (m : ℤ) * ((d / Nat.gcd d e : ℕ) : ℤ) =
      -(cubicAFEProgressionNumerator d e δ m) := by
    unfold cubicAFEProgressionNumerator
    ring
  simp only [cubicAFEProgression, Set.mem_ofPred_eq, Int.modEq_iff_dvd,
    hsign, Int.dvd_neg]

private theorem reduced_right_pos {d e : ℕ} (he : 0 < e) : 0 < e / Nat.gcd d e := by
  have hq : 0 < Nat.gcd d e := by
    simpa only [Nat.gcd_comm] using Nat.gcd_pos_of_pos_left d he
  obtain ⟨_, heq, _⟩ := gcd_extraction hq.ne'
  apply Nat.pos_of_ne_zero
  intro hz
  rw [hz, mul_zero] at heq
  exact he.ne' heq

private theorem positive_exact_quotient {z s : ℤ}
    (hz : 0 < z) (hs : 0 < s) (hdiv : s ∣ z) : 0 < z / s := by
  have hmul := Int.ediv_mul_cancel hdiv
  by_contra h
  have hnon := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hs.le
  rw [hmul] at hnon
  omega

/-- The inverse residue is `-delta*rbar`, without requiring delta to be a
unit and without excluding modulus one.  The inverse is a Bézout coefficient. -/
theorem cubicAFEProgression_mem_iff_residue {d e : ℕ} (he : 0 < e) (δ : ℤ) (m : ℕ) :
    m ∈ cubicAFEProgression d e δ ↔
      0 < m ∧ 0 < cubicAFEProgressionNumerator d e δ m ∧
        Int.ModEq ((e / Nat.gcd d e : ℕ) : ℤ) (m : ℤ)
          (-δ * Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e)) := by
  let r := d / Nat.gcd d e
  let s := e / Nat.gcd d e
  let a := Nat.gcdA r s
  have hq : 0 < Nat.gcd d e := by
    simpa only [Nat.gcd_comm] using Nat.gcd_pos_of_pos_left d he
  have hrs : Nat.Coprime r s := (gcd_extraction hq.ne').2.2
  have hbezout : (r : ℤ) * a + (s : ℤ) * Nat.gcdB r s = 1 := by
    simpa only [hrs.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab r s).symm
  have hunit : Int.ModEq (s : ℤ) ((r : ℤ) * a) 1 := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨Nat.gcdB r s, by linarith [hbezout]⟩
  have hc : Int.ModEq (s : ℤ) ((m : ℤ) * r) (-δ) ↔
      Int.ModEq (s : ℤ) (m : ℤ) (-δ * a) := by
    constructor
    · intro h
      have hm : Int.ModEq (s : ℤ) ((m : ℤ) * r * a) (m : ℤ) := by
        simpa only [mul_assoc, mul_one] using hunit.mul_left (m : ℤ)
      exact hm.symm.trans (h.mul_right a)
    · intro h
      have hu : Int.ModEq (s : ℤ) ((-δ * a) * r) (-δ) := by
        convert hunit.mul_left (-δ) using 1 <;> ring
      exact (h.mul_right (r : ℤ)).trans hu
  rw [cubicAFEProgression_mem_iff_modEq]
  exact and_congr Iff.rfl (and_congr Iff.rfl hc)

theorem cubicAFEProgressionPair_succ {d e : ℕ} (he : 0 < e) {δ : ℤ} {m : ℕ}
    (hm : m ∈ cubicAFEProgression d e δ) :
    (cubicAFEProgressionPair d e δ m).1 + 1 = m ∧
      (cubicAFEProgressionPair d e δ m).2 + 1 =
        (cubicAFEProgressionNumerator d e δ m /
          ((e / Nat.gcd d e : ℕ) : ℤ)).toNat := by
  have hs : (0 : ℤ) < ((e / Nat.gcd d e : ℕ) : ℤ) := by
    exact_mod_cast reduced_right_pos (d := d) he
  have hn := positive_exact_quotient hm.2.1 hs hm.2.2
  exact ⟨Nat.sub_add_cancel hm.1,
    Nat.sub_add_cancel (Int.pos_iff_toNat_pos.mp hn)⟩

theorem cubicAFEProgressionPair_mem {d e : ℕ} (he : 0 < e) {δ : ℤ} {m : ℕ}
    (hm : m ∈ cubicAFEProgression d e δ) :
    cubicAFEProgressionPair d e δ m ∈ cubicAFEShiftFiber d e δ := by
  have hs : (0 : ℤ) < ((e / Nat.gcd d e : ℕ) : ℤ) := by
    exact_mod_cast reduced_right_pos (d := d) he
  have hn := positive_exact_quotient hm.2.1 hs hm.2.2
  obtain ⟨hfirst, hsecond⟩ := cubicAFEProgressionPair_succ he hm
  change cubicAFEReducedShift d e (cubicAFEProgressionPair d e δ m) = δ
  unfold cubicAFEReducedShift
  rw [hfirst, hsecond]
  simp only [Nat.cast_mul]
  rw [Int.toNat_of_nonneg hn.le, Int.ediv_mul_cancel hm.2.2]
  unfold cubicAFEProgressionNumerator
  ring

/-- Exact real quotient on the progression, ready for a physical kernel
extension.  No floor, rounding, or toNat approximation remains. -/
theorem cubicAFEProgressionPair_second_cast {d e : ℕ} (he : 0 < e) {δ : ℤ} {m : ℕ}
    (hm : m ∈ cubicAFEProgression d e δ) :
    (((cubicAFEProgressionPair d e δ m).2 + 1 : ℕ) : ℝ) =
      ((δ : ℝ) + (m : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ)) /
        ((e / Nat.gcd d e : ℕ) : ℝ) := by
  have hs0 : ((e / Nat.gcd d e : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (reduced_right_pos (d := d) he).ne'
  have h := cubicAFEReducedShift_add_denominator d e (cubicAFEProgressionPair d e δ m)
  rw [show cubicAFEReducedShift d e (cubicAFEProgressionPair d e δ m) = δ from
    cubicAFEProgressionPair_mem he hm, (cubicAFEProgressionPair_succ he hm).1] at h
  have hZ : (((cubicAFEProgressionPair d e δ m).2 + 1 : ℕ) : ℤ) *
      ((e / Nat.gcd d e : ℕ) : ℤ) = δ + (m : ℤ) * ((d / Nat.gcd d e : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul] using h.symm
  apply (eq_div_iff hs0).mpr
  simpa only [Int.cast_mul, Int.cast_add, Int.cast_natCast] using
    congrArg (fun z : ℤ ↦ (z : ℝ)) hZ

theorem cubicAFEProgression_of_shift {d e : ℕ} (he : 0 < e) {δ : ℤ} {p : ℕ × ℕ}
    (hp : p ∈ cubicAFEShiftFiber d e δ) : p.1 + 1 ∈ cubicAFEProgression d e δ := by
  have hs : (0 : ℤ) < ((e / Nat.gcd d e : ℕ) : ℤ) := by
    exact_mod_cast reduced_right_pos (d := d) he
  have hnum : cubicAFEProgressionNumerator d e δ (p.1 + 1) =
      ((p.2 + 1 : ℕ) : ℤ) * ((e / Nat.gcd d e : ℕ) : ℤ) := by
    have h := cubicAFEReducedShift_add_denominator d e p
    rw [show cubicAFEReducedShift d e p = δ from hp] at h
    simpa only [cubicAFEProgressionNumerator, Nat.cast_mul] using h
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · rw [hnum]
    positivity
  · rw [hnum]
    exact ⟨((p.2 + 1 : ℕ) : ℤ), by ring⟩

/-- A positive second residual modulus makes the second index unique. -/
theorem cubicAFEShiftFiber_first_injective {d e : ℕ} (he : 0 < e) (δ : ℤ) :
    Function.Injective (fun p : cubicAFEShiftFiber d e δ ↦ p.val.1 + 1) := by
  intro p v h
  change p.val.1 + 1 = v.val.1 + 1 at h
  have hfirst : p.val.1 = v.val.1 := by omega
  have hp := p.property
  have hv := v.property
  change cubicAFEReducedShift d e p.val = δ at hp
  change cubicAFEReducedShift d e v.val = δ at hv
  simp only [cubicAFEReducedShift, Nat.cast_mul] at hp hv
  rw [hfirst] at hp
  have hprod : ((p.val.2 + 1 : ℕ) : ℤ) * ((e / Nat.gcd d e : ℕ) : ℤ) =
      ((v.val.2 + 1 : ℕ) : ℤ) * ((e / Nat.gcd d e : ℕ) : ℤ) := by linarith
  have hs0 : ((e / Nat.gcd d e : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (reduced_right_pos (d := d) he).ne'
  have hn := mul_right_cancel₀ hs0 hprod
  have hnNat : p.val.2 + 1 = v.val.2 + 1 := by exact_mod_cast hn
  apply Subtype.ext
  exact Prod.ext hfirst (by omega)

/-- A bijection, not merely a way to construct some solutions. -/
def cubicAFEProgressionEquiv {d e : ℕ} (he : 0 < e) (δ : ℤ) :
    cubicAFEProgression d e δ ≃ cubicAFEShiftFiber d e δ where
  toFun m := ⟨cubicAFEProgressionPair d e δ m.val, cubicAFEProgressionPair_mem he m.property⟩
  invFun p := ⟨p.val.1 + 1, cubicAFEProgression_of_shift he p.property⟩
  left_inv m := by
    apply Subtype.ext
    exact (cubicAFEProgressionPair_succ he m.property).1
  right_inv p := by
    apply cubicAFEShiftFiber_first_injective he δ
    exact (cubicAFEProgressionPair_succ he (cubicAFEProgression_of_shift he p.property)).1

theorem tsum_cubicAFEShiftFiber_eq_progression {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (f : ℕ × ℕ → ℂ) :
    (∑' p : cubicAFEShiftFiber d e δ, f p.val) =
      ∑' m : cubicAFEProgression d e δ, f (cubicAFEProgressionPair d e δ m.val) :=
  ((cubicAFEProgressionEquiv he δ).tsum_eq (fun p ↦ f p.val)).symm

/-- The actual integrated progression series is summable. -/
theorem summable_integral_cubicAFE_progression
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : 0 < e) (δ : ℤ) :
    Summable (fun m : cubicAFEProgression d e δ ↦ ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ m.val)) :=
  (cubicAFEProgressionEquiv he δ).summable_iff.mpr
    (summable_integral_cubicAFE_shiftFiber W hT hX V hd he.ne' δ)

/-- A genuine single-variable congruence sum inside every shift and pair. -/
noncomputable def cubicAFEProgressionMomentFinite
    (W : CubicTestWeight) (T X V : ℝ) : ℂ :=
  ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
    ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' m : cubicAFEProgression d e δ.val, ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t (cubicAFEProgressionPair d e δ.val m.val)

theorem cubicAFEShiftedMomentFinite_eq_progression (W : CubicTestWeight) (T X V : ℝ) :
    cubicAFEShiftedMomentFinite W T X V = cubicAFEProgressionMomentFinite W T X V := by
  unfold cubicAFEShiftedMomentFinite cubicAFEProgressionMomentFinite
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro δ
  exact tsum_cubicAFEShiftFiber_eq_progression (Finset.mem_Icc.mp he).1 δ.val
    (fun p ↦ ∫ t : ℝ, cubicAFECombinedSummandFinite W T X V d e t p)

theorem cubicAFEMollifiedMomentFinite_eq_diagonal_add_progression
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    cubicAFEMollifiedMomentFinite W T X V =
      cubicAFEDiagonalMomentFinite W T X V + cubicAFEProgressionMomentFinite W T X V := by
  rw [cubicAFEMollifiedMomentFinite_eq_diagonal_add_shifted W hT hX V,
    cubicAFEShiftedMomentFinite_eq_progression W T X V]

/-- No separate limit of an infinite progression or shift sum is asserted. -/
theorem tendsto_cubicAFEDiagonal_add_progression
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
      cubicAFEProgressionMomentFinite W T X V)
      atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)) := by
  apply (tendsto_cubicAFEMollifiedMomentFinite W hT hX).congr'
  exact Eventually.of_forall (fun V ↦
    cubicAFEMollifiedMomentFinite_eq_diagonal_add_progression W hT hX V)

end PrimeNumberTheorem.MWKFCubic
