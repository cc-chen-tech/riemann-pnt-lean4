import HardyTheorem.SelbergSqrtZetaSignedRationalCollected

open Complex

namespace HardyTheorem

noncomputable example (p : ℕ × (ℕ × ℕ)) : ℚ :=
  selbergSqrtZetaSignedRationalKey p

noncomputable example (N X : ℕ) : Finset ℚ :=
  selbergSqrtZetaSignedRationalSupport N X

noncomputable example (N X : ℕ) (q : ℚ) : Finset (ℕ × (ℕ × ℕ)) :=
  selbergSqrtZetaSignedRationalFiber N X q

noncomputable example (N X : ℕ) (q : ℚ) : ℂ :=
  selbergSqrtZetaSignedRationalCoeff N X q

noncomputable example (q : ℚ) : ℝ :=
  selbergSqrtZetaSignedRationalFrequency q

noncomputable example (N X : ℕ) (t : ℝ) : ℂ :=
  selbergSqrtZetaSignedRationalCollectedPolynomial N X t

example {N X : ℕ} {p : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergSqrtZetaSignedPhaseSupport N X) :
    0 < selbergSqrtZetaSignedRationalKey p :=
  selbergSqrtZetaSignedRationalKey_pos_of_mem hp

example {N X : ℕ} {p : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergSqrtZetaSignedPhaseSupport N X) :
    selbergSqrtZetaSignedPhaseFrequency p =
      selbergSqrtZetaSignedRationalFrequency
        (selbergSqrtZetaSignedRationalKey p) :=
  selbergSqrtZetaSignedPhaseFrequency_eq_rationalFrequency_key hp

example {N X : ℕ} {p q : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergSqrtZetaSignedPhaseSupport N X)
    (hq : q ∈ selbergSqrtZetaSignedPhaseSupport N X) :
    selbergSqrtZetaSignedPhaseFrequency p =
        selbergSqrtZetaSignedPhaseFrequency q ↔
      selbergSqrtZetaSignedRationalKey p =
        selbergSqrtZetaSignedRationalKey q :=
  selbergSqrtZetaSignedPhaseFrequency_eq_iff_rationalKey_eq hp hq

example (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedTriplePolynomial N X t =
      selbergSqrtZetaSignedRationalCollectedPolynomial N X t :=
  selbergSqrtZetaSignedTriplePolynomial_eq_rationalCollectedPolynomial N X t

end HardyTheorem
