import PrimeNumberTheorem.ZeroDensityLayerBudgetBidirectionalHeightStrategy

/-!
# Contract for bidirectional PNT height strategies
-/

namespace PrimeNumberTheorem

#check BidirectionalPNTHeightStrategy
#check pntPolynomialLowerLogHeight
#check isTargetAmplitudeAdmissibleHeight_pntPolynomialLowerLogHeight
#check pntSqrtLogPolynomialBidirectionalHeightStrategy
#check nonempty_bidirectionalPNTHeightStrategy
#check BidirectionalPNTHeightStrategy.upperLogHeight_ne_lowerLogHeight
#check pntSqrtLogHeight_ne_pntPolynomialLowerLogHeight

example (beta rate : ℝ) (hrate : 0 ≤ rate) :
    Nonempty (BidirectionalPNTHeightStrategy beta) :=
  nonempty_bidirectionalPNTHeightStrategy beta rate hrate

example {beta : ℝ} (strategy : BidirectionalPNTHeightStrategy beta)
    (hbeta : beta < 1) :
    strategy.upperLogHeight ≠ strategy.lowerLogHeight :=
  strategy.upperLogHeight_ne_lowerLogHeight hbeta

end PrimeNumberTheorem
