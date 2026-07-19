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

end CarlsonZeroDensity
end PrimeNumberTheorem
