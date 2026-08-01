import PrimeNumberTheorem.ExceptionalZeroDetectOrCount
import PrimeNumberTheorem.VKEdgeDynamicZeroPacketDrift

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExceptionalZeroDetectOrCount

open VKEdgePiOverTwo

noncomputable section

/-!
# Quantitative detect-or-count packet mass

This module packages the existing moving real-band extraction theorem into one
end-to-end certificate.  The selected packet is the actual filtered zeta-zero
packet, and the coefficient-mass lower bound keeps the Gaussian Schur constant
and the inspected bucket count explicit.

This is only an interface around an existing conditional moving-energy
extraction.  It supplies no new unconditional energy lower bound, no Sharp or
Witness input, and no zero-free half-plane.
-/

/-- Strictly positive actual coefficient mass forces the actual real-band
packet to be nonempty. -/
theorem dynamicComplementRealBandZeroPacket_nonempty_of_coefficientMass_pos
    (S : Finset ℂ) (T beta a delta : ℝ) (n : ℕ)
    (hmass :
      0 <
        dynamicComplementRealBandPacketCoefficientMass
          S T beta a delta n) :
    (dynamicComplementRealBandZeroPacket S T beta delta n).Nonempty := by
  classical
  by_contra hPempty
  have hPEq :
      dynamicComplementRealBandZeroPacket S T beta delta n = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hPempty
  have hmassZero :
      dynamicComplementRealBandPacketCoefficientMass
        S T beta a delta n = 0 := by
    simp [dynamicComplementRealBandPacketCoefficientMass, hPEq]
  linarith

/-- A pointwise upper bound for nonnegative weights converts a strict
mass-square lower bound into a cardinal-square lower bound.  No square root is
introduced. -/
theorem sum_sq_lt_card_sq_mul_sq_of_pointwise_le
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (weight : ι → ℝ) {lambda U : ℝ}
    (hweightNonneg : ∀ rho ∈ P, 0 ≤ weight rho)
    (hweightUpper : ∀ rho ∈ P, weight rho ≤ U)
    (hlambda : lambda < (∑ rho ∈ P, weight rho) ^ 2) :
    lambda < (P.card : ℝ) ^ 2 * U ^ 2 := by
  have hsumNonneg : 0 ≤ ∑ rho ∈ P, weight rho :=
    Finset.sum_nonneg fun rho hrho => hweightNonneg rho hrho
  have hsumUpper :
      (∑ rho ∈ P, weight rho) ≤ (P.card : ℝ) * U := by
    calc
      (∑ rho ∈ P, weight rho) ≤ ∑ _rho ∈ P, U :=
        Finset.sum_le_sum fun rho hrho => hweightUpper rho hrho
      _ = (P.card : ℝ) * U := by simp
  have hsquare :
      (∑ rho ∈ P, weight rho) ^ 2 ≤
        ((P.card : ℝ) * U) ^ 2 :=
    pow_le_pow_left₀ hsumNonneg hsumUpper 2
  exact lt_of_lt_of_le hlambda (by simpa [mul_pow] using hsquare)

/-- The generic cardinal-square consequence specialized to the actual
real-band packet coefficient mass. -/
theorem
    dynamicComplementRealBandPacketCoefficientMass_sq_lt_card_sq_mul_sq
    (S : Finset ℂ) (T beta a delta : ℝ) (n : ℕ)
    {lambda U : ℝ}
    (hupper :
      ∀ rho ∈ dynamicComplementRealBandZeroPacket S T beta delta n,
        ‖finiteZeroClusterCoefficientAt
          (analyticOrderNatAt riemannZeta) beta a rho‖ ≤ U)
    (hlambda :
      lambda <
        dynamicComplementRealBandPacketCoefficientMass
          S T beta a delta n ^ 2) :
    lambda <
      ((dynamicComplementRealBandZeroPacket
        S T beta delta n).card : ℝ) ^ 2 * U ^ 2 := by
  apply sum_sq_lt_card_sq_mul_sq_of_pointwise_le
    (dynamicComplementRealBandZeroPacket S T beta delta n)
    (fun rho =>
      ‖finiteZeroClusterCoefficientAt
        (analyticOrderNatAt riemannZeta) beta a rho‖)
  · intro rho hrho
    exact norm_nonneg _
  · exact hupper
  · simpa [dynamicComplementRealBandPacketCoefficientMass] using hlambda

/-- A large existing real-band forward moving energy produces one full
quantitative cluster certificate.  The output names both the selected bucket
and the actual packet, keeps the strict mass-square bound explicit, records
the packet geometry, and uses the existing detect-or-count growth lemma for
the strict set update. -/
theorem exists_quantitativeRealBandPacket_of_forwardMovingGaussianL2_gt
    {S : Finset ℂ} {T beta a eta m L delta : ℝ} {K : Finset ℕ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (heta : 0 < eta)
    (hm : 1 ≤ m)
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hK : K.Nonempty)
    (hlarge :
      2 * eta +
          2 * (1 - Real.exp (-delta * L)) ^ 2 *
            (∑ n ∈ K,
              dynamicComplementRealBandPacketCoefficientMass
                S T beta a delta n) ^ 2 <
        dynamicComplementRealBandForwardMovingGaussianSecondMoment
          S T beta a delta K m L) :
    ∃ n ∈ K, ∃ P : Finset ℂ,
      P = dynamicComplementRealBandZeroPacket S T beta delta n ∧
      eta / (MathlibAux.gaussianBucketSchurConstant * K.card) <
          dynamicComplementRealBandPacketCoefficientMass
            S T beta a delta n ^ 2 ∧
      P ⊆ nontrivialZerosFinset T ∧
      Disjoint S P ∧
      (∀ rho ∈ P,
        beta - delta ≤ rho.re ∧ rho.re ≤ beta) ∧
      (∀ rho ∈ P,
        (n : ℝ) ≤ |rho.im| ∧ |rho.im| < (n : ℝ) + 1) ∧
      P.Nonempty ∧
      S.card < (S ∪ P).card := by
  classical
  obtain ⟨n, hnK, hmass, hnonempty, hdisjoint, hsubset,
      _hcard, hrealBand⟩ :=
    exists_absorbableDynamicComplementRealBandPacket_of_forwardMovingGaussianL2_gt
      heta hm hL hdelta hK hlarge
  let P : Finset ℂ :=
    dynamicComplementRealBandZeroPacket S T beta delta n
  have hband :
      ∀ rho ∈ P,
        beta - delta ≤ rho.re ∧ rho.re ≤ beta := by
    simpa [P, dynamicComplementRealBand] using hrealBand
  have hheight :
      ∀ rho ∈ P,
        (n : ℝ) ≤ |rho.im| ∧ |rho.im| < (n : ℝ) + 1 := by
    intro rho hrho
    have hrhoRealBand :
        rho ∈ dynamicComplementRealBandZeroPacket
          S T beta delta n := by
      simpa [P] using hrho
    change
      rho ∈
        (dynamicComplementZeroPacket S T n).filter
          (dynamicComplementRealBand beta delta) at hrhoRealBand
    have hrhoPacket :
        rho ∈ dynamicComplementZeroPacket S T n :=
      (Finset.mem_filter.mp hrhoRealBand).1
    change
      rho ∈ zeroOrdinateUnitBucket n ∩
        (nontrivialZerosFinset T \ S) at hrhoPacket
    have hrhoBucket : rho ∈ zeroOrdinateUnitBucket n :=
      (Finset.mem_inter.mp hrhoPacket).1
    change
      rho ∈
        (nontrivialZerosFinset ((n : ℝ) + 9 / 4)).filter
          (fun z => (n : ℝ) ≤ |z.im| ∧ |z.im| < (n : ℝ) + 1)
        at hrhoBucket
    exact (Finset.mem_filter.mp hrhoBucket).2
  have hgrowth :=
    union_disjoint_nontrivialZeroPacket_strict_growth
      hS hsubset hdisjoint hnonempty
  exact
    ⟨n, hnK, P, rfl, hmass, hsubset, hdisjoint,
      hband, hheight, hnonempty, hgrowth.2.1⟩

end

end ExceptionalZeroDetectOrCount
end PrimeNumberTheorem
