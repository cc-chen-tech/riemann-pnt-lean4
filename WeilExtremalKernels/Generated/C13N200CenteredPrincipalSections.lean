import WeilExtremalKernels.CenteredPrincipalSection
import WeilExtremalKernels.Generated.C13N200FiniteClosure

/-!
# Generated centered-section metadata for c=13, N=200

This module binds the finite closure to the 201 centered principal
sections with cutoffs 0 through 200.  It does not cover larger cutoffs.
-/

namespace WeilExtremalKernels.Generated

def c13N200NestingArtifactPayloadSHA256 : String :=
  "1aed6dd8d96548f72dd395ff501910c31dd9f2bcb213922823b5c8e4d63fa686"

def c13N200CertifiedCenteredSectionCount : Nat := 201

theorem c13N200CertifiedCenteredSectionCount_eq :
    c13N200CertifiedCenteredSectionCount = 201 := rfl

theorem c13N200CenteredCoordinatePreserved
    (M : Nat) (hM : M <= 200) (i : Fin (2 * M + 1)) :
    centeredIndexCoordinate 200 (centeredFinEmbedding hM i) =
      centeredIndexCoordinate M i :=
  centeredIndexCoordinate_centeredFinEmbedding hM i

theorem c13N200AllSmallerStrictlyPositive
    (Q : Nat -> (n : Nat) -> FiniteMatrix (2 * n + 1))
    (hnested :
      forall M (hM : M <= 200),
        Q 13 M = centeredPrincipalSection hM (Q 13 200))
    (h200 :
      forall x, x != 0 -> 0 < quadraticForm (Q 13 200) x) :
    forall M (hM : M <= 200) x, x != 0 ->
      0 < quadraticForm (Q 13 M) x :=
  all_smaller_cutoffs_pos_of_centered_nested
    Q 13 200 hnested h200

end WeilExtremalKernels.Generated
