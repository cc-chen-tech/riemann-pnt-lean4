import HardyTheorem.SelbergLagDyadicGeometry

open Set

namespace HardyTheorem

#check (@selberg_lag_dyadic_mem :
  ∀ {T H τ v x : ℝ}, τ ∈ Icc (-H) H →
    v ∈ Icc (max 0 (-τ)) (min H (H - τ)) →
    x ∈ Icc (T + v) ((2 * T - H) + v) →
    x ∈ Icc T (2 * T))

#check (@selberg_lag_shifted_dyadic_mem :
  ∀ {T H τ v x : ℝ}, τ ∈ Icc (-H) H →
    v ∈ Icc (max 0 (-τ)) (min H (H - τ)) →
    x ∈ Icc (T + v) ((2 * T - H) + v) →
    x + τ ∈ Icc T (2 * T))

#check (@selberg_lag_controlInterval_subset_dyadic :
  ∀ {T H τ v : ℝ}, τ ∈ Icc (-H) H →
    v ∈ Icc (max 0 (-τ)) (min H (H - τ)) →
    Icc (min (T + v) (T + v + τ))
        (max ((2 * T - H) + v) ((2 * T - H) + v + τ)) ⊆ Icc T (2 * T))

end HardyTheorem
