import HardyTheorem.SelbergSqrtZetaSignedBoundaryLargeN

open scoped BigOperators

namespace HardyTheorem

example {N X k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    selbergSqrtZetaSignedDenominatorFiber N X k =
      k.divisorsAntidiagonal.filter (fun p => p.2 ≤ X) :=
  selbergSqrtZetaSignedDenominatorFiber_eq_divisorsAntidiagonal_filter_snd hk hkN

example {N X a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hX : 1 ≤ X)
    (hlarge : b * X ≤ N) :
    selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b =
      Finset.Ioc (X / b) (X / a) :=
  selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport_eq_Ioc_of_b_mul_X_le_N
    ha hb hX hlarge

example {N X a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hX : 1 ≤ X)
    (hlarge : b * X ≤ N) :
    selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b =
      ∑ d ∈ Finset.Ioc (X / b) (X / a),
        (d : ℝ)⁻¹ * selbergSqrtZetaTaperedCoeff X (a * d) *
          ∑ p ∈ (b * d).divisorsAntidiagonal.filter (fun p => p.2 ≤ X),
            selbergSqrtZetaTaperedCoeff X p.2 :=
  selbergSqrtZetaSignedReducedRayBoundaryTerm_eq_stable_Ioc ha hb hX hlarge

example {N X a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hX : 1 ≤ X)
    (hN : X * X ≤ N) (hbX : b ≤ X) :
    selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b =
      ∑ d ∈ Finset.Ioc (X / b) (X / a),
        (d : ℝ)⁻¹ * selbergSqrtZetaTaperedCoeff X (a * d) *
          ∑ p ∈ (b * d).divisorsAntidiagonal.filter (fun p => p.2 ≤ X),
            selbergSqrtZetaTaperedCoeff X p.2 :=
  selbergSqrtZetaSignedReducedRayBoundaryTerm_eq_stable_Ioc_of_sq_le
    ha hb hX hN hbX

example {N X a b : ℕ} (hXN : X ≤ N) (hba : b ≤ a) :
    selbergSqrtZetaSignedReducedRayBoundaryTerm N X a b = 0 :=
  selbergSqrtZetaSignedReducedRayBoundaryTerm_eq_zero_of_denominator_le_numerator
    hXN hba

end HardyTheorem
