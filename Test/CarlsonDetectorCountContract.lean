import PrimeNumberTheorem.CarlsonDetectorCount

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example (sigma alpha a b : ℝ) : Set ℂ :=
  carlsonDetectorRectangle sigma alpha a b

example (sigma alpha a b : ℝ) :
    IsCompact (carlsonDetectorRectangle sigma alpha a b) :=
  isCompact_carlsonDetectorRectangle sigma alpha a b

example (X : ℕ) : Meromorphic (carlsonZeroDetector X) :=
  meromorphic_carlsonZeroDetector X

noncomputable example (X : ℕ) (sigma alpha a b : ℝ) : ℕ :=
  carlsonDetectorRectangleZeroCount X sigma alpha a b

noncomputable example (X : ℕ) (sigma alpha a b : ℝ) : Finset ℂ :=
  regularizedCarlsonDetectorRectangleDivisorSupport X sigma alpha a b

noncomputable example (X : ℕ) (sigma alpha a b : ℝ) : ℕ :=
  regularizedCarlsonDetectorRectangleZeroCount X sigma alpha a b

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha a b : ℝ}
    (hsigma : 0 < sigma) {z : ℂ}
    (hz : z ∈ carlsonDetectorRectangle sigma alpha a b) :
    z ∈ regularizedCarlsonDetectorRectangleDivisorSupport X sigma alpha a b ↔
      regularizedCarlsonZeroDetector X z = 0 :=
  mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
    hX hsigma hz

example {X : ℕ} (hX : 1 ≤ X) {sigma alpha T : ℝ}
    (hsigma : 0 < sigma) :
    ∃ t : ℝ, T < t ∧ t < T + 1 ∧
      ∀ x ∈ Set.Icc sigma alpha,
        regularizedCarlsonZeroDetector X
          ((x : ℂ) + (t : ℂ) * I) ≠ 0 :=
  exists_regularizedCarlsonZeroDetector_horizontal_ne_zero
    hX hsigma (T := T)

example {X : ℕ} (hX : 1 ≤ X) (sigma T : ℝ) :
    ZeroDensity.zeroDensityCount sigma T ≤
      carlsonDetectorRectangleZeroCount X sigma 1 0 T :=
  zeroDensityCount_le_carlsonDetectorRectangleZeroCount hX sigma T

example {X : ℕ} (hX : 1 ≤ X) (sigma T : ℝ) :
    ZeroDensity.zeroDensityCount sigma T ≤
      regularizedCarlsonDetectorRectangleZeroCount X sigma 1 0 T :=
  zeroDensityCount_le_regularizedCarlsonDetectorRectangleZeroCount hX sigma T

#print axioms isCompact_carlsonDetectorRectangle
#print axioms meromorphic_carlsonZeroDetector
#print axioms zeroDensityCount_le_carlsonDetectorRectangleZeroCount
#print axioms zeroDensityCount_le_regularizedCarlsonDetectorRectangleZeroCount
#print axioms mem_regularizedCarlsonDetectorRectangleDivisorSupport_iff_zero
#print axioms exists_regularizedCarlsonZeroDetector_horizontal_ne_zero

end CarlsonZeroDensity
end PrimeNumberTheorem
