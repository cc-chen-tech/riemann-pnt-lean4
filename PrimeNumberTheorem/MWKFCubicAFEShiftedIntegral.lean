import PrimeNumberTheorem.MWKFCubicAFEDiagonalSplit

open Filter MeasureTheory
open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Signed shifted-divisor fibers of the actual integrated AFE

For `m=p.1+1`, `n=p.2+1`, `q=gcd(d,e)`, `r=d/q`, and `s=e/q`, the
signed shift is `delta=n*s-m*r`.  No Taylor approximation, shift truncation,
absolute value of Möbius coefficients, or height-limit interchange is used.
-/

/-- An integer difference, never natural subtraction. -/
def cubicAFEReducedShift (d e : ℕ) (p : ℕ × ℕ) : ℤ :=
  (((p.2 + 1) * (e / Nat.gcd d e) : ℕ) : ℤ) -
    (((p.1 + 1) * (d / Nat.gcd d e) : ℕ) : ℤ)

theorem gcd_mul_cubicAFEReducedShift (d e : ℕ) (p : ℕ × ℕ) :
    (Nat.gcd d e : ℤ) * cubicAFEReducedShift d e p =
      (((p.2 + 1) * e : ℕ) : ℤ) - (((p.1 + 1) * d : ℕ) : ℤ) := by
  by_cases hq : Nat.gcd d e = 0
  · obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp hq
    simp [cubicAFEReducedShift]
  · obtain ⟨hdq, heq, _⟩ := gcd_extraction hq
    have hdZ : (d : ℤ) = (Nat.gcd d e : ℤ) * ((d / Nat.gcd d e : ℕ) : ℤ) := by
      exact_mod_cast hdq
    have heZ : (e : ℤ) = (Nat.gcd d e : ℤ) * ((e / Nat.gcd d e : ℕ) : ℤ) := by
      exact_mod_cast heq
    simp only [cubicAFEReducedShift, Nat.cast_mul]
    rw [hdZ, heZ]
    ring

/-- Includes the degenerate zero moduli, which are absent from the mollifier. -/
theorem cubicAFEReducedShift_zero_iff (d e : ℕ) (p : ℕ × ℕ) :
    cubicAFEReducedShift d e p = 0 ↔ p ∈ cubicAFEDiagonal d e := by
  by_cases hq : Nat.gcd d e = 0
  · obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp hq
    simp [cubicAFEReducedShift, cubicAFEDiagonal]
  · have hqZ : (Nat.gcd d e : ℤ) ≠ 0 := by exact_mod_cast hq
    have hscaled := gcd_mul_cubicAFEReducedShift d e p
    change cubicAFEReducedShift d e p = 0 ↔ (p.2 + 1) * e = (p.1 + 1) * d
    constructor
    · intro h
      rw [h, mul_zero] at hscaled
      have hraw := sub_eq_zero.mp hscaled.symm
      exact_mod_cast hraw
    · intro h
      have hraw : (((p.2 + 1) * e : ℕ) : ℤ) = (((p.1 + 1) * d : ℕ) : ℤ) := by
        exact_mod_cast h
      rw [hraw, sub_self] at hscaled
      exact (mul_eq_zero.mp hscaled).resolve_left hqZ

theorem cubicAFEReducedShift_add_denominator (d e : ℕ) (p : ℕ × ℕ) :
    cubicAFEReducedShift d e p + (((p.1 + 1) * (d / Nat.gcd d e) : ℕ) : ℤ) =
      (((p.2 + 1) * (e / Nat.gcd d e) : ℕ) : ℤ) := by
  simp [cubicAFEReducedShift]

private theorem reduced_left_pos {d e : ℕ} (hd : 0 < d) : 0 < d / Nat.gcd d e := by
  have hq := Nat.gcd_pos_of_pos_left e hd
  obtain ⟨hdq, _, _⟩ := gcd_extraction hq.ne'
  apply Nat.pos_of_ne_zero
  intro hz
  rw [hz, mul_zero] at hdq
  exact hd.ne' hdq

/-- Full logarithmic phase, with the reduced gcd denominator and its sign. -/
theorem cubicAFECombinedLogPhase_eq_reducedShift
    (p : ℕ × ℕ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    cubicAFECombinedLogPhase p d e =
      Real.log (1 + (cubicAFEReducedShift d e p : ℝ) /
        (((p.1 + 1 : ℕ) : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ))) := by
  have hq := Nat.gcd_pos_of_pos_left e hd
  obtain ⟨hdq, heq, _⟩ := gcd_extraction hq.ne'
  have hr := reduced_left_pos (e := e) hd
  have hdR : (d : ℝ) = (Nat.gcd d e : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ) := by
    exact_mod_cast hdq
  have heR : (e : ℝ) = (Nat.gcd d e : ℝ) * ((e / Nat.gcd d e : ℕ) : ℝ) := by
    exact_mod_cast heq
  have hden : (((p.1 + 1 : ℕ) : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ)) ≠ 0 := by
    positivity
  have hratio :
      (((p.2 + 1 : ℕ) : ℝ) * (e : ℝ)) / (((p.1 + 1 : ℕ) : ℝ) * (d : ℝ)) =
        (((p.2 + 1 : ℕ) : ℝ) * ((e / Nat.gcd d e : ℕ) : ℝ)) /
          (((p.1 + 1 : ℕ) : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ)) := by
    apply (div_eq_div_iff (by positivity) hden).mpr
    rw [hdR, heR]
    ring
  have hshift : (cubicAFEReducedShift d e p : ℝ) =
      (((p.2 + 1 : ℕ) : ℝ) * ((e / Nat.gcd d e : ℕ) : ℝ)) -
        (((p.1 + 1 : ℕ) : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ)) := by
    simp only [cubicAFEReducedShift, Int.cast_sub, Nat.cast_mul, Int.cast_mul,
      Int.cast_natCast]
  rw [cubicAFECombinedLogPhase_eq_log_products p hd he,
    ← Real.log_div (by positivity) (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one] at hratio hshift hden ⊢
  rw [hratio, hshift]
  congr 1
  rw [sub_div, div_self hden]
  ring

/-- The exact logarithm argument is positive also for negative shifts. -/
theorem cubicAFEReducedShift_logArgument_pos
    (p : ℕ × ℕ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    0 < 1 + (cubicAFEReducedShift d e p : ℝ) /
      (((p.1 + 1 : ℕ) : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ)) := by
  have hr := reduced_left_pos (e := e) hd
  have hs : 0 < e / Nat.gcd d e := by
    simpa only [Nat.gcd_comm] using reduced_left_pos (e := d) he
  have hden : 0 < (((p.1 + 1 : ℕ) : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ)) := by
    positivity
  have hshift : (cubicAFEReducedShift d e p : ℝ) =
      (((p.2 + 1 : ℕ) : ℝ) * ((e / Nat.gcd d e : ℕ) : ℝ)) -
        (((p.1 + 1 : ℕ) : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ)) := by
    simp only [cubicAFEReducedShift, Int.cast_sub, Nat.cast_mul, Int.cast_mul,
      Int.cast_natCast]
  rw [hshift, sub_div, div_self hden.ne']
  have hnum : 0 < (((p.2 + 1 : ℕ) : ℝ) * ((e / Nat.gcd d e : ℕ) : ℝ)) := by
    positivity
  linarith [div_pos hnum hden]

/-- Complete physical summand in reduced-shift coordinates. -/
theorem cubicAFECombinedSummandFinite_eq_reducedShift
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (t : ℝ) (p : ℕ × ℕ) :
    cubicAFECombinedSummandFinite W T X V d e t p =
      (cubicMollifierCoefficient T d : ℂ) *
        (cubicMollifierCoefficient T e : ℂ) * 2 *
        (((Real.sqrt (cubicAFEPositiveIndexProduct p) : ℂ)⁻¹ *
          (Real.sqrt (d * e) : ℂ)⁻¹) *
          Complex.exp ((Complex.I * (Real.log (1 +
            (cubicAFEReducedShift d e p : ℝ) /
              (((p.1 + 1 : ℕ) : ℝ) * ((d / Nat.gcd d e : ℕ) : ℝ))) : ℂ)) * t) *
          cubicAFEProductWeightFinite t X V (cubicAFEPositiveIndexProduct p)) *
        (W (t / T) : ℂ) := by
  rw [cubicAFECombinedSummandFinite_eq_exp W T X V hd.ne' he.ne' t p,
    cubicAFECombinedLogPhase_eq_reducedShift p hd he]

/-- One signed shifted-divisor equation in the original positive indices. -/
def cubicAFEShiftFiber (d e : ℕ) (δ : ℤ) : Set (ℕ × ℕ) :=
  {p | cubicAFEReducedShift d e p = δ}

/-- Exact disjoint-union equivalence, with both signs and every gcd stratum. -/
def cubicAFEShiftEquiv (d e : ℕ) :
    ↑((cubicAFEDiagonal d e)ᶜ) ≃
      (Σ δ : {δ : ℤ // δ ≠ 0}, cubicAFEShiftFiber d e δ.val) where
  toFun p := ⟨⟨cubicAFEReducedShift d e p.val, fun hz ↦
    p.property ((cubicAFEReducedShift_zero_iff d e p.val).mp hz)⟩, ⟨p.val, rfl⟩⟩
  invFun x := ⟨x.2.val, fun hdiag ↦ x.1.property
    (x.2.property.symm.trans ((cubicAFEReducedShift_zero_iff d e x.2.val).mpr hdiag))⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv x := by
    rcases x with ⟨⟨δ, hδ⟩, ⟨p, hp⟩⟩
    change cubicAFEReducedShift d e p = δ at hp
    cases hp
    rfl

/-- Regroup a summable off-diagonal series by every signed nonzero shift.
The concrete integral specialization below proves the summability input. -/
theorem hasSum_cubicAFE_shiftFibers (d e : ℕ) (f : ℕ × ℕ → ℂ)
    (hf : Summable (fun p : ↑((cubicAFEDiagonal d e)ᶜ) ↦ f p.val)) :
    HasSum (fun δ : {δ : ℤ // δ ≠ 0} ↦
      ∑' p : cubicAFEShiftFiber d e δ.val, f p.val)
      (∑' p : ↑((cubicAFEDiagonal d e)ᶜ), f p.val) := by
  let E := cubicAFEShiftEquiv d e
  have hg : Summable (fun x : (Σ δ : {δ : ℤ // δ ≠ 0},
      cubicAFEShiftFiber d e δ.val) ↦ f x.2.val) := E.symm.summable_iff.mpr hf
  have heq : (∑' p : ↑((cubicAFEDiagonal d e)ᶜ), f p.val) =
      ∑' x : (Σ δ : {δ : ℤ // δ ≠ 0}, cubicAFEShiftFiber d e δ.val), f x.2.val :=
    (E.symm.tsum_eq (fun p ↦ f p.val)).symm
  rw [heq, hg.tsum_sigma]
  exact hg.sigma.hasSum

theorem summable_integral_cubicAFE_shiftFiber
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) (δ : ℤ) :
    Summable (fun p : cubicAFEShiftFiber d e δ ↦ ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t p.val) :=
  (hasSum_integral_cubicAFECombinedSummandFinite W hT hX V hd he).summable.subtype _

theorem hasSum_integral_cubicAFE_shiftFibers
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    HasSum (fun δ : {δ : ℤ // δ ≠ 0} ↦
      ∑' p : cubicAFEShiftFiber d e δ.val, ∫ t : ℝ,
        cubicAFECombinedSummandFinite W T X V d e t p.val)
      (∑' p : ↑((cubicAFEDiagonal d e)ᶜ), ∫ t : ℝ,
        cubicAFECombinedSummandFinite W T X V d e t p.val) :=
  hasSum_cubicAFE_shiftFibers d e
    (fun p ↦ ∫ t : ℝ, cubicAFECombinedSummandFinite W T X V d e t p)
    (summable_integral_cubicAFE_diagonal_and_offDiagonal W hT hX V hd he).2

/-- The full physical shifted-divisor expression: no large shift or sign is
discarded, and all Mellin/physical weights remain inside each integral. -/
noncomputable def cubicAFEShiftedMomentFinite
    (W : CubicTestWeight) (T X V : ℝ) : ℂ :=
  ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
    ∑' δ : {δ : ℤ // δ ≠ 0}, ∑' p : cubicAFEShiftFiber d e δ.val, ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t p.val

theorem cubicAFEOffDiagonalMomentFinite_eq_shifted
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) :
    cubicAFEOffDiagonalMomentFinite W T X V =
      cubicAFEShiftedMomentFinite W T X V := by
  unfold cubicAFEOffDiagonalMomentFinite cubicAFEShiftedMomentFinite
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hd0 : d ≠ 0 := by have h := (Finset.mem_Icc.mp hd).1; omega
  have he0 : e ≠ 0 := by have h := (Finset.mem_Icc.mp he).1; omega
  exact (hasSum_integral_cubicAFE_shiftFibers W hT hX V hd0 he0).tsum_eq.symm

theorem cubicAFEMollifiedMomentFinite_eq_diagonal_add_shifted
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) :
    cubicAFEMollifiedMomentFinite W T X V =
      cubicAFEDiagonalMomentFinite W T X V + cubicAFEShiftedMomentFinite W T X V := by
  rw [cubicAFEMollifiedMomentFinite_eq_diagonal_add_offDiagonal W hT hX V,
    cubicAFEOffDiagonalMomentFinite_eq_shifted W hT hX V]

/-- The height limit remains outside the complete reassembled expression. -/
theorem tendsto_cubicAFEDiagonal_add_shifted
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦ cubicAFEDiagonalMomentFinite W T X V +
      cubicAFEShiftedMomentFinite W T X V)
      atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)) := by
  apply (tendsto_cubicAFEMollifiedMomentFinite W hT hX).congr'
  exact Eventually.of_forall (fun V ↦
    cubicAFEMollifiedMomentFinite_eq_diagonal_add_shifted W hT hX V)

end PrimeNumberTheorem.MWKFCubic
