import MathlibAux.SlidingRegionSwap

open MeasureTheory Set

namespace MathlibAux

/-!
# Contract for the region-swap lag identity
-/

example {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (Function.uncurry Φ)) {H : ℝ}
    (hH : 0 ≤ H) :
    (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, Φ v (w - v)) =
      ∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ), Φ v τ :=
  intervalIntegral_pair_sub_eq_lagIntegral hΦ hH

#print axioms intervalIntegral_pair_sub_swap
#print axioms intervalIntegral_pair_sub_eq_lagIntegral

end MathlibAux
