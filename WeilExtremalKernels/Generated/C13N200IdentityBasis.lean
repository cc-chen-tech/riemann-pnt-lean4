import WeilExtremalKernels.WeilCoordinateBridge

/-!
# Generated full Fourier coordinate certificate for c=13, N=200

This file is generated from one authenticated identity-basis record.  It
binds finite coordinate metadata only; it does not state Gate A, an
infinite-dimensional Weil criterion, or RH.
-/

namespace WeilExtremalKernels.Generated

def c13N200C : Nat := 13
def c13N200N : Nat := 200
def c13N200Dimension : Nat := 401

def c13N200ArtifactPayloadSHA256 : String :=
  "b849e20b4fe3812de8fe191d9259f828dedf3b69068a5aa5c25003b8b6d95b9f"

def c13N200SourceFileSHA256 : String :=
  "efec67a8e7a0eca6c028164c12e87ae6cb94312d0b855adceb58ea439f504b04"

def c13N200SourcePayloadSHA256 : String :=
  "00a54e206ba1df5c5b9178b6fb80a3935c3c1d673d3387913d4b0f8a1c286d28"

def c13N200LDLCheckpointFileSHA256 : String :=
  "be071bd29e22a8d6c6ee947bc4585394a63f030519f920241c790a4e6fcce41b"

def c13N200LDLCheckpointPayloadSHA256 : String :=
  "e5a47ed8f49131fc8a4ec9ca4a8043fed5521770e42393f547d60e9f828ba316"

def c13N200IdentityBasisSHA256 : String :=
  "4bdabd34b0b01a2abf2875a5cdcea59e7de8ec53804694cb52ac5f82317233ed"

theorem c13N200Dimension_eq :
    2 * c13N200N + 1 = c13N200Dimension := by
  norm_num [c13N200N, c13N200Dimension]

def c13N200Basis :
    RectangularMatrix c13N200Dimension c13N200Dimension :=
  fullFourierIdentityBasis c13N200N

def c13N200LeftInverseCertificate :
    LeftInverseCertificate c13N200Basis := by
  simpa [c13N200Basis] using
    fullFourierIdentityLeftInverseCertificate c13N200N

theorem c13N200RegisteredIndex_eq
    (i : Fin c13N200Dimension) :
    (registeredFullFourierIndex c13N200N i : Real) =
      centeredIndexCoordinate c13N200N i :=
  registeredFullFourierIndex_cast_eq_centeredIndexCoordinate c13N200N i

theorem c13N200Congruence_eq
    (A : FiniteMatrix c13N200Dimension) :
    congruenceMatrix A c13N200Basis = A := by
  simpa [c13N200Basis] using
    congruenceMatrix_fullFourierIdentityBasis c13N200N A

theorem c13N200QuadraticForm_eq
    (A : FiniteMatrix c13N200Dimension)
    (x : FiniteVector c13N200Dimension) :
    quadraticForm (congruenceMatrix A c13N200Basis) x =
      quadraticForm A x := by
  rw [c13N200Congruence_eq]

end WeilExtremalKernels.Generated
