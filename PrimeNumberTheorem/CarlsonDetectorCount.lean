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

end CarlsonZeroDensity
end PrimeNumberTheorem
