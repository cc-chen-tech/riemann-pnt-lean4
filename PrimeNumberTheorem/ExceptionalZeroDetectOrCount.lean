import PrimeNumberTheorem

open Complex

namespace PrimeNumberTheorem
namespace ExceptionalZeroDetectOrCount

/-!
# One-window growth of a recorded zeta-zero set

This module is the combinatorial integration layer for exceptional-zero
amplification.  It does not prove that a detector or an energy estimate
produces a new zero.  Instead, it converts either of the two intended upstream
outputs into a strictly larger finite set of genuine height-truncated zeta
zeros.
-/

/-- Adjoining one genuine zero outside the recorded set preserves the
height-truncated zero invariant and increases cardinality strictly. -/
theorem insert_new_nontrivialZero_strict_growth
    {S : Finset ℂ} {T : ℝ} {rho : ℂ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hrho : rho ∈ nontrivialZerosFinset T)
    (hrhoS : rho ∉ S) :
    S ⊆ insert rho S ∧
      S.card < (insert rho S).card ∧
      insert rho S ⊆ nontrivialZerosFinset T := by
  constructor
  · exact Finset.subset_insert rho S
  constructor
  · simp [hrhoS]
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hrho
    · exact hS hz

/-- Union with a nonempty, disjoint packet of genuine zeros preserves the
height-truncated zero invariant and increases cardinality strictly. -/
theorem union_disjoint_nontrivialZeroPacket_strict_growth
    {S P : Finset ℂ} {T : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hP : P ⊆ nontrivialZerosFinset T)
    (hdisjoint : Disjoint S P)
    (hPnonempty : P.Nonempty) :
    S ⊆ S ∪ P ∧
      S.card < (S ∪ P).card ∧
      S ∪ P ⊆ nontrivialZerosFinset T := by
  constructor
  · exact Finset.subset_union_left
  constructor
  · rw [Finset.card_union_of_disjoint hdisjoint]
    have hPcard : 0 < P.card := Finset.card_pos.mpr hPnonempty
    omega
  · exact Finset.union_subset hS hP

/-- The exact witness shape produced by the complementary-energy theorem
gives one strict update of the recorded genuine-zero set. -/
theorem exists_strictly_larger_recordedZeroSet_of_new_nontrivialZero
    {S : Finset ℂ} {T : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hnew : ∃ rho ∈ nontrivialZerosFinset T, rho ∉ S) :
    ∃ S' : Finset ℂ,
      S ⊆ S' ∧
        S.card < S'.card ∧
        S' ⊆ nontrivialZerosFinset T := by
  rcases hnew with ⟨rho, hrho, hrhoS⟩
  exact
    ⟨insert rho S,
      insert_new_nontrivialZero_strict_growth hS hrho hrhoS⟩

/-- A single detector window may return either one new zero or a nonempty
packet disjoint from all recorded zeros.  Either output forces one strict
growth step while preserving the genuine-zero invariant. -/
theorem exists_strictly_larger_recordedZeroSet_of_detect_or_count
    {S : Finset ℂ} {T : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hdetectOrCount :
      (∃ rho ∈ nontrivialZerosFinset T, rho ∉ S) ∨
        ∃ P : Finset ℂ,
          P ⊆ nontrivialZerosFinset T ∧ Disjoint S P ∧ P.Nonempty) :
    ∃ S' : Finset ℂ,
      S ⊆ S' ∧
        S.card < S'.card ∧
        S' ⊆ nontrivialZerosFinset T := by
  rcases hdetectOrCount with hnew | ⟨P, hP, hdisjoint, hPnonempty⟩
  · exact exists_strictly_larger_recordedZeroSet_of_new_nontrivialZero hS hnew
  · exact
      ⟨S ∪ P,
        union_disjoint_nontrivialZeroPacket_strict_growth
          hS hP hdisjoint hPnonempty⟩

end ExceptionalZeroDetectOrCount
end PrimeNumberTheorem
