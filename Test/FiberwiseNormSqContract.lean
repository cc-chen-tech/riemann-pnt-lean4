import MathlibAux.FiberwiseNormSq

open Complex
open scoped BigOperators

namespace MathlibAux

#check normSq_finset_sum_le_card_mul_sum_normSq
#check sum_normSq_fiber_le_sum_card_mul_normSq
#check sum_normSq_fiber_le_mul_sum_normSq

example {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∑ x ∈ s, f x) ≤
      (s.card : ℝ) * ∑ x ∈ s, Complex.normSq (f x) :=
  normSq_finset_sum_le_card_mul_sum_normSq s f

example {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → ℂ)
    (hmaps : ∀ x ∈ s, g x ∈ t) :
    (∑ k ∈ t,
        Complex.normSq (∑ x ∈ s.filter (fun x => g x = k), f x)) ≤
      ∑ k ∈ t,
        ((s.filter (fun x => g x = k)).card : ℝ) *
          ∑ x ∈ s.filter (fun x => g x = k), Complex.normSq (f x) :=
  sum_normSq_fiber_le_sum_card_mul_normSq s t g f hmaps

example {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → ℂ)
    (hmaps : ∀ x ∈ s, g x ∈ t) {C : ℝ}
    (hcard : ∀ k ∈ t, ((s.filter (fun x => g x = k)).card : ℝ) ≤ C) :
    (∑ k ∈ t,
        Complex.normSq (∑ x ∈ s.filter (fun x => g x = k), f x)) ≤
      C * ∑ x ∈ s, Complex.normSq (f x) :=
  sum_normSq_fiber_le_mul_sum_normSq s t g f hmaps hcard

#print axioms normSq_finset_sum_le_card_mul_sum_normSq
#print axioms sum_normSq_fiber_le_sum_card_mul_normSq
#print axioms sum_normSq_fiber_le_mul_sum_normSq

end MathlibAux
