import MathlibAux.AutocorrelationApproximation

open MeasureTheory Set

namespace MathlibAux

/-!
# Contract for shifted-autocorrelation approximation
-/

example {A B τ x : ℝ} (hx : x ∈ Icc A B) :
    x ∈ Icc (min A (A + τ)) (max B (B + τ)) :=
  mem_autocorrelationControlInterval hx

example {A B τ x : ℝ} (hx : x ∈ Icc A B) :
    x + τ ∈ Icc (min A (A + τ)) (max B (B + τ)) :=
  add_mem_autocorrelationControlInterval hx

example {F P : ℝ → ℝ} {A B τ eps M : ℝ}
    (hF : ContinuousOn F (Icc (min A (A + τ)) (max B (B + τ))))
    (hP : ContinuousOn P (Icc (min A (A + τ)) (max B (B + τ))))
    (hAB : A ≤ B) (heps : 0 ≤ eps) (hM : 0 ≤ M)
    (happrox : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)), |F x - P x| ≤ eps)
    (hFbound : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)), |F x| ≤ M)
    (hPbound : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)), |P x| ≤ M) :
    |(∫ x in A..B, F x * F (x + τ)) - ∫ x in A..B, P x * P (x + τ)| ≤
      (B - A) * (2 * M * eps) :=
  abs_integral_mul_shift_sub_mul_shift_le_of_continuousOn
    hF hP hAB heps hM happrox hFbound hPbound

example {F P : ℝ → ℝ} (hF : Continuous F) (hP : Continuous P)
    {A B τ eps M : ℝ} (hAB : A ≤ B) (heps : 0 ≤ eps) (hM : 0 ≤ M)
    (happrox : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)), |F x - P x| ≤ eps)
    (hFbound : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)), |F x| ≤ M)
    (hPbound : ∀ x ∈ Icc (min A (A + τ)) (max B (B + τ)), |P x| ≤ M) :
    |(∫ x in A..B, F x * F (x + τ)) - ∫ x in A..B, P x * P (x + τ)| ≤
      (B - A) * (2 * M * eps) :=
  abs_integral_mul_shift_sub_mul_shift_le
    hF hP hAB heps hM happrox hFbound hPbound

end MathlibAux
