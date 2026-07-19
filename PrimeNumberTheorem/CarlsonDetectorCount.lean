import PrimeNumberTheorem.CarlsonZeroDetector
import PrimeNumberTheorem.ZeroDensityCount

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The closed axis-parallel rectangle used to count zeros of Carlson's
detector. -/
def carlsonDetectorRectangle
    (sigma alpha a b : ℝ) : Set ℂ :=
  Set.Icc sigma alpha ×ℂ Set.Icc a b

theorem isCompact_carlsonDetectorRectangle
    (sigma alpha a b : ℝ) :
    IsCompact (carlsonDetectorRectangle sigma alpha a b) := by
  simpa [carlsonDetectorRectangle] using
    (isCompact_Icc.reProdIm isCompact_Icc)

/-- Carlson's detector is meromorphic on the whole complex plane. -/
theorem meromorphic_carlsonZeroDetector (X : ℕ) :
    Meromorphic (carlsonZeroDetector X) := by
  intro s
  have hzeta : MeromorphicAt riemannZeta s :=
    ZeroFreeRegion.meromorphic_riemannZeta s
  have hmollifier : MeromorphicAt (mobiusMollifier X) s :=
    (analyticAt_mobiusMollifier X s).meromorphicAt
  change MeromorphicAt
    (fun z : ℂ =>
      1 - (riemannZeta z * mobiusMollifier X z - 1) ^ 2) s
  exact (MeromorphicAt.const 1 s).sub
    (((hzeta.mul hmollifier).sub (MeromorphicAt.const 1 s)).pow 2)

/-- Finite divisor support of Carlson's detector on a closed rectangle. -/
noncomputable def carlsonDetectorRectangleDivisorSupport
    (X : ℕ) (sigma alpha a b : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (carlsonZeroDetector X)
      (carlsonDetectorRectangle sigma alpha a b)).finiteSupport
    (isCompact_carlsonDetectorRectangle sigma alpha a b)).toFinset

/-- Total zero multiplicity of Carlson's detector in a closed rectangle.
Poles have negative divisor order and contribute zero through `Int.toNat`. -/
noncomputable def carlsonDetectorRectangleZeroCount
    (X : ℕ) (sigma alpha a b : ℝ) : ℕ :=
  let D := MeromorphicOn.divisor (carlsonZeroDetector X)
    (carlsonDetectorRectangle sigma alpha a b)
  ∑ z ∈ carlsonDetectorRectangleDivisorSupport X sigma alpha a b,
    (D z).toNat

/-- Finite divisor support of the pole-free Carlson detector on a closed
rectangle. -/
noncomputable def regularizedCarlsonDetectorRectangleDivisorSupport
    (X : ℕ) (sigma alpha a b : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
      (carlsonDetectorRectangle sigma alpha a b)).finiteSupport
    (isCompact_carlsonDetectorRectangle sigma alpha a b)).toFinset

/-- Total zero multiplicity of the pole-free Carlson detector in a closed
rectangle. -/
noncomputable def regularizedCarlsonDetectorRectangleZeroCount
    (X : ℕ) (sigma alpha a b : ℝ) : ℕ :=
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
    (carlsonDetectorRectangle sigma alpha a b)
  ∑ z ∈ regularizedCarlsonDetectorRectangleDivisorSupport
      X sigma alpha a b, (D z).toNat

private theorem divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt_of_mem
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b : ℝ}
    (hsigma : 0 < sigma) {z : ℂ}
    (hz : z ∈ carlsonDetectorRectangle sigma alpha a b) :
    MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
        (carlsonDetectorRectangle sigma alpha a b) z =
      (analyticOrderNatAt (regularizedCarlsonZeroDetector X) z : ℤ) := by
  have hzre : 0 < z.re := by
    have hzIcc := hz.1
    exact hsigma.trans_le hzIcc.1
  have hanalytic : AnalyticAt ℂ (regularizedCarlsonZeroDetector X) z :=
    analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X z hzre
  have horder :
      analyticOrderAt (regularizedCarlsonZeroDetector X) z ≠ ⊤ :=
    analyticOrderAt_regularizedCarlsonZeroDetector_ne_top X hX hzre
  rw [MeromorphicOn.divisor_apply
      (meromorphic_regularizedCarlsonZeroDetector X).meromorphicOn hz,
    hanalytic.meromorphicOrderAt_eq]
  have hcast := Nat.cast_analyticOrderNatAt horder
  rw [← hcast]
  simp

/-- Inside a rectangle contained in the open right half-plane, the finite
divisor support of the regularized detector is exactly its zero set. -/
theorem mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b : ℝ}
    (hsigma : 0 < sigma) {z : ℂ}
    (hz : z ∈ carlsonDetectorRectangle sigma alpha a b) :
    z ∈ regularizedCarlsonDetectorRectangleDivisorSupport X sigma alpha a b ↔
      regularizedCarlsonZeroDetector X z = 0 := by
  classical
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
    (carlsonDetectorRectangle sigma alpha a b)
  have hdivisor : D z =
      (analyticOrderNatAt (regularizedCarlsonZeroDetector X) z : ℤ) := by
    dsimp [D]
    exact divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt_of_mem
      hX hsigma hz
  have hzre : 0 < z.re := hsigma.trans_le hz.1.1
  have hanalytic : AnalyticAt ℂ (regularizedCarlsonZeroDetector X) z :=
    analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X z hzre
  have horder :
      analyticOrderAt (regularizedCarlsonZeroDetector X) z ≠ ⊤ :=
    analyticOrderAt_regularizedCarlsonZeroDetector_ne_top X hX hzre
  have hnatCast := Nat.cast_analyticOrderNatAt horder
  rw [regularizedCarlsonDetectorRectangleDivisorSupport]
  rw [(D.finiteSupport
    (isCompact_carlsonDetectorRectangle sigma alpha a b)).mem_toFinset]
  simp only [Function.mem_support]
  rw [hdivisor, Int.ofNat_ne_zero]
  constructor
  · intro hnat
    apply hanalytic.analyticOrderAt_ne_zero.mp
    intro hzero
    have hcastZero :
        (analyticOrderNatAt (regularizedCarlsonZeroDetector X) z : ℕ∞) = 0 :=
      hnatCast.trans hzero
    exact hnat (by simpa using hcastZero)
  · intro hzero hnatZero
    have horderZero :
        analyticOrderAt (regularizedCarlsonZeroDetector X) z = 0 := by
      rw [← hnatCast, hnatZero]
      rfl
    exact (hanalytic.analyticOrderAt_eq_zero.mp horderZero) hzero

/-- Every unit height interval contains a horizontal segment on which the
regularized detector is nonvanishing throughout a prescribed compact real
interval in the open right half-plane. -/
theorem exists_regularizedCarlsonZeroDetector_horizontal_ne_zero
    {X : ℕ} (hX : 1 ≤ X) {sigma alpha T : ℝ}
    (hsigma : 0 < sigma) :
    ∃ t : ℝ, T < t ∧ t < T + 1 ∧
      ∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
  classical
  let P := regularizedCarlsonDetectorRectangleDivisorSupport
    X sigma alpha T (T + 1)
  let bad : Finset ℝ := P.image Complex.im
  obtain ⟨t, htIoo, htbad⟩ :=
    (Set.Ioo_infinite (show T < T + 1 by linarith)).exists_notMem_finset bad
  refine ⟨t, htIoo.1, htIoo.2, ?_⟩
  intro x hx hzero
  let z : ℂ := (x : ℂ) + (t : ℂ) * I
  have hz : z ∈ carlsonDetectorRectangle sigma alpha T (T + 1) := by
    change z.re ∈ Set.Icc sigma alpha ∧ z.im ∈ Set.Icc T (T + 1)
    constructor
    · simpa [z] using hx
    · simpa [z] using And.intro htIoo.1.le htIoo.2.le
  have hzP : z ∈ P := by
    dsimp [P]
    exact
      (mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
        hX hsigma hz).mpr hzero
  apply htbad
  dsimp [bad]
  apply Finset.mem_image.mpr
  refine ⟨z, hzP, ?_⟩
  dsimp [z]
  simp

private theorem divisor_carlsonZeroDetector_eq_analyticOrderNatAt
    {X : ℕ} {sigma alpha a b : ℝ} {rho : ℂ}
    (hX : 1 ≤ X) (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hmem : rho ∈ carlsonDetectorRectangle sigma alpha a b) :
    MeromorphicOn.divisor (carlsonZeroDetector X)
        (carlsonDetectorRectangle sigma alpha a b) rho =
      (analyticOrderNatAt (carlsonZeroDetector X) rho : ℤ) := by
  have hrho1 : rho ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp at hre
    linarith [hrho.2.2]
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one rho hrho1
  have hmollifier : AnalyticAt ℂ (mobiusMollifier X) rho :=
    analyticAt_mobiusMollifier X rho
  have hdetector : AnalyticAt ℂ (carlsonZeroDetector X) rho := by
    unfold carlsonZeroDetector mollifiedZetaError
    exact analyticAt_const.sub
      (((hzeta.mul hmollifier).sub analyticAt_const).pow 2)
  have hzeta_pos : 0 < analyticOrderNatAt riemannZeta rho :=
    ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero hrho1 hrho.1
  have hdetector_pos :
      0 < analyticOrderNatAt (carlsonZeroDetector X) rho :=
    hzeta_pos.trans_le
      (analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector hX hrho)
  have hdetector_order_ne_top :
      analyticOrderAt (carlsonZeroDetector X) rho ≠ ⊤ := by
    intro htop
    have hzero : analyticOrderNatAt (carlsonZeroDetector X) rho = 0 := by
      simp [analyticOrderNatAt, htop]
    omega
  rw [MeromorphicOn.divisor_apply
      (meromorphic_carlsonZeroDetector X).meromorphicOn hmem,
    hdetector.meromorphicOrderAt_eq]
  have horder := Nat.cast_analyticOrderNatAt hdetector_order_ne_top
  rw [← horder]
  simp

/-- Every zeta zero counted by `zeroDensityCount sigma T` is a detector zero
inside the closed rectangle `[sigma, 1] × [0, T]`, with at least the same
multiplicity. -/
theorem zeroDensityCount_le_carlsonDetectorRectangleZeroCount
    {X : ℕ} (hX : 1 ≤ X) (sigma T : ℝ) :
    ZeroDensity.zeroDensityCount sigma T ≤
      carlsonDetectorRectangleZeroCount X sigma 1 0 T := by
  classical
  let K : Set ℂ := carlsonDetectorRectangle sigma 1 0 T
  let D := MeromorphicOn.divisor (carlsonZeroDetector X) K
  let S := ZeroDensity.zeroDensityZerosFinset sigma T
  let P := carlsonDetectorRectangleDivisorSupport X sigma 1 0 T
  have hS_subset : S ⊆ P := by
    intro rho hrhoS
    have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
    have hmem : rho ∈ K := by
      dsimp [K, carlsonDetectorRectangle]
      simp only [Complex.mem_reProdIm, Set.mem_Icc]
      exact ⟨⟨hrho.2.2.2.le, hrho.1.2.2.le⟩,
        ⟨hrho.2.1.le, hrho.2.2.1⟩⟩
    have hdivisor : D rho =
        (analyticOrderNatAt (carlsonZeroDetector X) rho : ℤ) := by
      dsimp [D, K]
      exact divisor_carlsonZeroDetector_eq_analyticOrderNatAt
        hX hrho.1 hmem
    have hpositive : 0 < analyticOrderNatAt (carlsonZeroDetector X) rho :=
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        (by
          intro hone
          have hre := congrArg Complex.re hone
          simp at hre
          linarith [hrho.1.2.2]) hrho.1.1).trans_le
        (analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector hX hrho.1)
    dsimp [P, carlsonDetectorRectangleDivisorSupport]
    apply (D.finiteSupport
      (isCompact_carlsonDetectorRectangle sigma 1 0 T)).mem_toFinset.mpr
    simp only [Function.mem_support]
    rw [hdivisor]
    exact_mod_cast hpositive.ne'
  calc
    ZeroDensity.zeroDensityCount sigma T =
        ∑ rho ∈ S, analyticOrderNatAt riemannZeta rho := rfl
    _ ≤ ∑ rho ∈ S, (D rho).toNat := by
      apply Finset.sum_le_sum
      intro rho hrhoS
      have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
      have hmem : rho ∈ K := by
        dsimp [K, carlsonDetectorRectangle]
        simp only [Complex.mem_reProdIm, Set.mem_Icc]
        exact ⟨⟨hrho.2.2.2.le, hrho.1.2.2.le⟩,
          ⟨hrho.2.1.le, hrho.2.2.1⟩⟩
      have hdivisor : D rho =
          (analyticOrderNatAt (carlsonZeroDetector X) rho : ℤ) := by
        dsimp [D, K]
        exact divisor_carlsonZeroDetector_eq_analyticOrderNatAt
          hX hrho.1 hmem
      rw [hdivisor, Int.toNat_natCast]
      exact analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector hX hrho.1
    _ ≤ ∑ z ∈ P, (D z).toNat :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_subset
        (fun _ _ _ => Nat.zero_le _)
    _ = carlsonDetectorRectangleZeroCount X sigma 1 0 T := rfl

private theorem divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt
    {X : ℕ} {sigma alpha a b : ℝ} {rho : ℂ}
    (hX : 1 ≤ X) (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hmem : rho ∈ carlsonDetectorRectangle sigma alpha a b) :
    MeromorphicOn.divisor (regularizedCarlsonZeroDetector X)
        (carlsonDetectorRectangle sigma alpha a b) rho =
      (analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho : ℤ) := by
  have hdetector : AnalyticAt ℂ (regularizedCarlsonZeroDetector X) rho :=
    analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X rho hrho.2.1
  have hzeta_pos : 0 < analyticOrderNatAt riemannZeta rho :=
    ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
      (by
        intro hone
        have hre := congrArg Complex.re hone
        simp at hre
        linarith [hrho.2.2]) hrho.1
  have hdetector_pos :
      0 < analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho :=
    hzeta_pos.trans_le
      (analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
        hX hrho)
  have hdetector_order_ne_top :
      analyticOrderAt (regularizedCarlsonZeroDetector X) rho ≠ ⊤ := by
    intro htop
    have hzero :
        analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho = 0 := by
      simp [analyticOrderNatAt, htop]
    omega
  rw [MeromorphicOn.divisor_apply
      (meromorphic_regularizedCarlsonZeroDetector X).meromorphicOn hmem,
    hdetector.meromorphicOrderAt_eq]
  have horder := Nat.cast_analyticOrderNatAt hdetector_order_ne_top
  rw [← horder]
  simp

/-- Every zeta zero counted by `zeroDensityCount sigma T` is a zero of the
pole-free Carlson detector inside `[sigma, 1] × [0, T]`, with at least the
same multiplicity. -/
theorem zeroDensityCount_le_regularizedCarlsonDetectorRectangleZeroCount
    {X : ℕ} (hX : 1 ≤ X) (sigma T : ℝ) :
    ZeroDensity.zeroDensityCount sigma T ≤
      regularizedCarlsonDetectorRectangleZeroCount X sigma 1 0 T := by
  classical
  let K : Set ℂ := carlsonDetectorRectangle sigma 1 0 T
  let D := MeromorphicOn.divisor (regularizedCarlsonZeroDetector X) K
  let S := ZeroDensity.zeroDensityZerosFinset sigma T
  let P := regularizedCarlsonDetectorRectangleDivisorSupport X sigma 1 0 T
  have hS_subset : S ⊆ P := by
    intro rho hrhoS
    have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
    have hmem : rho ∈ K := by
      dsimp [K, carlsonDetectorRectangle]
      simp only [Complex.mem_reProdIm, Set.mem_Icc]
      exact ⟨⟨hrho.2.2.2.le, hrho.1.2.2.le⟩,
        ⟨hrho.2.1.le, hrho.2.2.1⟩⟩
    have hdivisor : D rho =
        (analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho : ℤ) := by
      dsimp [D, K]
      exact divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt
        hX hrho.1 hmem
    have hpositive :
        0 < analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho :=
      (ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        (by
          intro hone
          have hre := congrArg Complex.re hone
          simp at hre
          linarith [hrho.1.2.2]) hrho.1.1).trans_le
        (analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
          hX hrho.1)
    dsimp [P, regularizedCarlsonDetectorRectangleDivisorSupport]
    apply (D.finiteSupport
      (isCompact_carlsonDetectorRectangle sigma 1 0 T)).mem_toFinset.mpr
    simp only [Function.mem_support]
    rw [hdivisor]
    exact_mod_cast hpositive.ne'
  calc
    ZeroDensity.zeroDensityCount sigma T =
        ∑ rho ∈ S, analyticOrderNatAt riemannZeta rho := rfl
    _ ≤ ∑ rho ∈ S, (D rho).toNat := by
      apply Finset.sum_le_sum
      intro rho hrhoS
      have hrho := ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoS
      have hmem : rho ∈ K := by
        dsimp [K, carlsonDetectorRectangle]
        simp only [Complex.mem_reProdIm, Set.mem_Icc]
        exact ⟨⟨hrho.2.2.2.le, hrho.1.2.2.le⟩,
          ⟨hrho.2.1.le, hrho.2.2.1⟩⟩
      have hdivisor : D rho =
          (analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho : ℤ) := by
        dsimp [D, K]
        exact divisor_regularizedCarlsonZeroDetector_eq_analyticOrderNatAt
          hX hrho.1 hmem
      rw [hdivisor, Int.toNat_natCast]
      exact
        analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
          hX hrho.1
    _ ≤ ∑ z ∈ P, (D z).toNat :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_subset
        (fun _ _ _ => Nat.zero_le _)
    _ = regularizedCarlsonDetectorRectangleZeroCount X sigma 1 0 T := rfl

end CarlsonZeroDensity
end PrimeNumberTheorem
