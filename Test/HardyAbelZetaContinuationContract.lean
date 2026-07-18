import ZeroFreeRegion.MeromorphicAux

open Complex Set

example {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) +
      s * ∫ t in Set.Ioi (1 : ℝ),
        ((((⌊t⌋₊ : ℝ) - t : ℝ) : ℂ) *
          (t : ℂ) ^ (-(s + 1))) :=
  ZeroFreeRegion.riemannZeta_eq_pole_add_floorError_integral_of_pos_re hs hs1

example {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℂ) ^ s) +
        (N : ℂ) ^ (1 - s) / (s - 1) +
        s * ∫ t in Set.Ioi (N : ℝ),
          ((((⌊t⌋₊ : ℝ) - t : ℝ) : ℂ) *
            (t : ℂ) ^ (-(s + 1))) :=
  ZeroFreeRegion.riemannZeta_eq_dirichletPolynomial_add_pole_add_floorErrorTail
    hs hs1 hN
