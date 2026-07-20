import PrimeNumberTheorem.DirichletPolynomialMeanSquare

open Complex
open scoped ComplexConjugate Interval

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example {a b d : ℝ} (hd : d ≠ 0) :
    ‖∫ t in a..b, Complex.exp (Complex.I * (d * t))‖ ≤ 2 / |d| :=
  norm_integral_exp_I_mul_le_two_div hd

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (homega : Set.InjOn omega (S : Set ι)) :
    ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 ≤
      ∑ m ∈ S, ∑ n ∈ S,
        ‖c m‖ * ‖c n‖ *
          if m = n then b - a else 2 / |omega n - omega m| :=
  finiteExponentialSum_meanSquare_le hab homega

example (S : Finset ℕ) (c : ℕ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ n ∈ S, 0 < n) :
    ∫ t in a..b, ‖finiteDirichletPolynomial S c t‖ ^ 2 ≤
      ∑ m ∈ S, ∑ n ∈ S,
        ‖c m‖ * ‖c n‖ *
          if m = n then b - a
          else 2 / |Real.log n - Real.log m| :=
  finiteDirichletPolynomial_meanSquare_le hab hpos

noncomputable example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) : ℂ :=
  hilbertForm S c omega

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) :
    conj (hilbertForm S c omega) = -hilbertForm S c omega :=
  conj_hilbertForm_eq_neg S c omega

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) :
    (hilbertForm S c omega).re = 0 :=
  hilbertForm_re_eq_zero S c omega

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) :
    hilbertForm S c (fun n => -omega n) = -hilbertForm S c omega :=
  hilbertForm_neg_frequency S c omega

example {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (S : Finset α) (index : α → ι) (hinj : Set.InjOn index (S : Set α))
    (c : ι → ℂ) (omega : ι → ℝ) :
    hilbertForm (S.image index) c omega =
      hilbertForm S (fun n => c (index n)) (fun n => omega (index n)) :=
  hilbertForm_image_eq S index hinj c omega

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (D : ℝ)
    (hplus : 0 ≤ ((D : ℂ) + Complex.I * hilbertForm S c omega).re)
    (hminus : 0 ≤ ((D : ℂ) - Complex.I * hilbertForm S c omega).re) :
    ‖hilbertForm S c omega‖ ≤ D :=
  norm_hilbertForm_le_of_two_sided_re_nonneg hplus hminus

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) {a b : ℝ}
    (homega : Set.InjOn omega (S : Set ι)) :
    ((∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 : ℝ) : ℂ) =
      (b - a) * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) -
        Complex.I *
          (hilbertForm S (phaseTwist c omega b) omega -
            hilbertForm S (phaseTwist c omega a) omega) :=
  finiteExponentialMeanSquare_cast_eq_diagonal_add_hilbert homega

example {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    1 / |Real.log m - Real.log n| ≤ (n : ℝ) + 1 :=
  inv_abs_log_sub_log_le_nat_add_one hm hn hmn

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (weight : ι → ℝ)
    {a b C : ℝ} (hab : a ≤ b) (homega : Set.InjOn omega (S : Set ι))
    (hweight : ∀ n ∈ S, 0 ≤ weight n)
    (hHilbert : ∀ d : ι → ℂ,
      ‖hilbertForm S d omega‖ ≤
        C * ∑ n ∈ S, weight n * ‖d n‖ ^ 2) :
    ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2 +
        2 * C * ∑ n ∈ S, weight n * ‖c n‖ ^ 2 :=
  finiteExponentialSum_meanSquare_le_of_hilbert
    hab homega hweight hHilbert

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (weight : ι → ℝ)
    {a b C : ℝ} (hab : a ≤ b) (homega : Set.InjOn omega (S : Set ι))
    (hweight : ∀ n ∈ S, 0 ≤ weight n)
    (hplus : ∀ d : ι → ℂ,
      0 ≤ (((C * ∑ n ∈ S, weight n * ‖d n‖ ^ 2 : ℝ) : ℂ) +
        Complex.I * hilbertForm S d omega).re)
    (hminus : ∀ d : ι → ℂ,
      0 ≤ (((C * ∑ n ∈ S, weight n * ‖d n‖ ^ 2 : ℝ) : ℂ) -
        Complex.I * hilbertForm S d omega).re) :
    ∫ t in a..b, ‖finiteExponentialSum S c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ S, ‖c n‖ ^ 2 +
        2 * C * ∑ n ∈ S, weight n * ‖c n‖ ^ 2 :=
  finiteExponentialSum_meanSquare_le_of_two_sided_certificate
    hab homega hweight hplus hminus

#print axioms norm_integral_exp_I_mul_le_two_div
#print axioms finiteExponentialSum_meanSquare_le
#print axioms finiteDirichletPolynomial_meanSquare_le
#print axioms finiteExponentialMeanSquare_cast_eq_diagonal_add_hilbert
#print axioms conj_hilbertForm_eq_neg
#print axioms hilbertForm_re_eq_zero
#print axioms hilbertForm_neg_frequency
#print axioms hilbertForm_image_eq
#print axioms norm_hilbertForm_le_of_two_sided_re_nonneg
#print axioms inv_abs_log_sub_log_le_nat_add_one
#print axioms finiteExponentialSum_meanSquare_le_of_hilbert
#print axioms finiteExponentialSum_meanSquare_le_of_two_sided_certificate

end DirichletPolynomial
end PrimeNumberTheorem
