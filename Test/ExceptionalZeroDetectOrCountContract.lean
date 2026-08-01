import PrimeNumberTheorem.ExceptionalZeroDetectOrCount

open Complex

namespace PrimeNumberTheorem
namespace ExceptionalZeroDetectOrCount

#check
  (insert_new_nontrivialZero_strict_growth :
    ∀ {S : Finset ℂ} {T : ℝ} {rho : ℂ},
      S ⊆ nontrivialZerosFinset T →
      rho ∈ nontrivialZerosFinset T →
      rho ∉ S →
      S ⊆ insert rho S ∧
        S.card < (insert rho S).card ∧
        insert rho S ⊆ nontrivialZerosFinset T)

#check
  (union_disjoint_nontrivialZeroPacket_strict_growth :
    ∀ {S P : Finset ℂ} {T : ℝ},
      S ⊆ nontrivialZerosFinset T →
      P ⊆ nontrivialZerosFinset T →
      Disjoint S P →
      P.Nonempty →
      S ⊆ S ∪ P ∧
        S.card < (S ∪ P).card ∧
        S ∪ P ⊆ nontrivialZerosFinset T)

#check
  (exists_strictly_larger_recordedZeroSet_of_new_nontrivialZero :
    ∀ {S : Finset ℂ} {T : ℝ},
      S ⊆ nontrivialZerosFinset T →
      (∃ rho ∈ nontrivialZerosFinset T, rho ∉ S) →
      ∃ S' : Finset ℂ,
        S ⊆ S' ∧
          S.card < S'.card ∧
          S' ⊆ nontrivialZerosFinset T)

#check
  (exists_strictly_larger_recordedZeroSet_of_detect_or_count :
    ∀ {S : Finset ℂ} {T : ℝ},
      S ⊆ nontrivialZerosFinset T →
      ((∃ rho ∈ nontrivialZerosFinset T, rho ∉ S) ∨
        ∃ P : Finset ℂ,
          P ⊆ nontrivialZerosFinset T ∧ Disjoint S P ∧ P.Nonempty) →
      ∃ S' : Finset ℂ,
        S ⊆ S' ∧
          S.card < S'.card ∧
          S' ⊆ nontrivialZerosFinset T)

end ExceptionalZeroDetectOrCount
end PrimeNumberTheorem
