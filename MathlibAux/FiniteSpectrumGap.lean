import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib

open scoped BigOperators

/-!
# The finite-spectrum gap: explicit `π/2 + δ_M` constants

Paper-level proof record: `docs/research/vk-edge-pi-over-two-proof-record.md`.
Preregistration: `docs/research/vk-edge-pi-over-two-preregistration.md`.

An *admissible* exponential polynomial is

```text
F(y) = 2 Re(∑_{j<r} a_j exp(i λ_j y)),
```

with `0 < r ≤ M`, positive distinct frequencies `λ_j > 0`, and the
distinguished normalization `λ_0 = 1`, `a_0 = 1`.  The proof record shows
that for every fixed `M` there is an explicit `δ_M > 0` such that every
admissible `F` has sup norm at least `π/2 + δ_M`, using the missing odd
harmonic of `sign(cos)`.

This module formalizes the admissible class, the explicit constant chain

```text
b_M = 2 / (π (2M+1)),
η_M = sin(1 / (4 (2M+1))),
d_M = η_M / (π (2M+1)),
L_M = 1 / (2/π - d_M),
δ_M = L_M - π/2,
```

and proves the positivity and gap facts that are independent of the
harmonic-analysis argument.  The full gap theorem is registered as the
`Prop` targets `finiteSpectrumGapTarget` and `kappaFormTarget`; it is NOT
proved in this module.  No `sorry` is used.
-/

namespace FiniteSpectrumGap

/-- The admissible exponential polynomial of the preregistration, with
`r` terms, coefficients `a`, and frequencies `λ`. -/
noncomputable def admissiblePolynomial (r : ℕ) (a : ℕ → ℂ) (lam : ℕ → ℝ) (y : ℝ) : ℝ :=
  (2 * (∑ j ∈ Finset.range r, a j * Complex.exp (Complex.I * (lam j * y)))).re

/-- The admissibility conditions of the preregistration: `0 < r ≤ M`,
positive pairwise-distinct frequencies, and the distinguished
normalization `λ_0 = 1`, `a_0 = 1`. -/
def IsAdmissible (M r : ℕ) (a : ℕ → ℂ) (lam : ℕ → ℝ) : Prop :=
  0 < r ∧ r ≤ M ∧ a 0 = 1 ∧ lam 0 = 1 ∧
    (∀ j, j < r → 0 < lam j) ∧ Function.Injective (fun j : Fin r => lam j)

/-- `κ_M`: the infimum of the sup norms of admissible polynomials with at
most `M` frequencies, encoded as the infimum of the set of upper bounds. -/
noncomputable def kappaM (M : ℕ) : ℝ :=
  sInf {K : ℝ | ∃ (r : ℕ) (a : ℕ → ℂ) (lam : ℕ → ℝ),
    IsAdmissible M r a lam ∧ ∀ y : ℝ, |admissiblePolynomial r a lam y| ≤ K}

/-- `b_M = 2 / (π (2M+1))`: the Fourier-coefficient lower bound of the
missing odd harmonic. -/
noncomputable def bM (M : ℕ) : ℝ := 2 / (Real.pi * ((2 * M + 1 : ℕ) : ℝ))

/-- `η_M = sin(1 / (4 (2M+1)))`: the level splitting the circle measure. -/
noncomputable def etaM (M : ℕ) : ℝ := Real.sin (1 / (4 * ((2 * M + 1 : ℕ) : ℝ)))

/-- `d_M = sin(1 / (4 (2M+1))) / (π (2M+1))`: the explicit equality-defect
lower bound of the proof record, equation (4). -/
noncomputable def dM (M : ℕ) : ℝ :=
  Real.sin (1 / (4 * ((2 * M + 1 : ℕ) : ℝ))) / (Real.pi * ((2 * M + 1 : ℕ) : ℝ))

/-- `L_M = 1 / (2/π - d_M)`: the explicit sup-norm lower bound,
`L_M > π/2`, of the proof record, equation (5). -/
noncomputable def LM (M : ℕ) : ℝ := 1 / (2 / Real.pi - dM M)

/-- `δ_M = L_M - π/2 > 0`: the explicit strict gap above `π/2`. -/
noncomputable def deltaM (M : ℕ) : ℝ := LM M - Real.pi / 2

/-- **Finite-spectrum gap target.**  For every admissible polynomial with
at most `M` frequencies there is a point where its modulus exceeds
`π/2 + δ_M`.  Paper proof: `vk-edge-pi-over-two-proof-record.md`
(missing odd harmonic of `sign(cos)`; not yet formalized). -/
def finiteSpectrumGapTarget : Prop :=
  ∀ M : ℕ, ∀ (r : ℕ) (a : ℕ → ℂ) (lam : ℕ → ℝ),
    IsAdmissible M r a lam → ∃ y : ℝ,
      Real.pi / 2 + deltaM M ≤ |admissiblePolynomial r a lam y|

/-- **`κ_M` form of the finite-spectrum gap target.** -/
def kappaFormTarget : Prop :=
  ∀ M : ℕ, Real.pi / 2 + deltaM M ≤ kappaM M

theorem bM_pos (M : ℕ) : 0 < bM M := by
  unfold bM
  positivity

theorem etaM_arg_pos (M : ℕ) : 0 < 1 / (4 * ((2 * M + 1 : ℕ) : ℝ)) := by
  positivity

theorem etaM_arg_lt_pi (M : ℕ) : 1 / (4 * ((2 * M + 1 : ℕ) : ℝ)) < Real.pi := by
  have hden : (4 : ℝ) ≤ 4 * ((2 * M + 1 : ℕ) : ℝ) := by
    have hone : (1 : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) :=
      (Nat.one_le_cast).mpr (by omega : 1 ≤ 2 * M + 1)
    nlinarith
  have hle : 1 / (4 * ((2 * M + 1 : ℕ) : ℝ)) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by positivity) hden
  exact lt_of_le_of_lt hle (by nlinarith [Real.pi_gt_three])

theorem etaM_pos (M : ℕ) : 0 < etaM M := by
  unfold etaM
  exact Real.sin_pos_of_pos_of_lt_pi (etaM_arg_pos M) (etaM_arg_lt_pi M)

theorem dM_pos (M : ℕ) : 0 < dM M := by
  unfold dM
  exact div_pos (etaM_pos M) (by positivity)

theorem dM_le_inv_pi_mul (M : ℕ) :
    dM M ≤ 1 / (Real.pi * ((2 * M + 1 : ℕ) : ℝ)) := by
  unfold dM
  exact div_le_div_of_nonneg_right (Real.sin_le_one _) (by positivity)

theorem dM_lt_two_div_pi (M : ℕ) : dM M < 2 / Real.pi := by
  have h2 : 1 / (Real.pi * ((2 * M + 1 : ℕ) : ℝ)) ≤ 1 / Real.pi := by
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < Real.pi)
    have hone : (1 : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) :=
      (Nat.one_le_cast).mpr (by omega : 1 ≤ 2 * M + 1)
    nlinarith [Real.pi_pos]
  have h3 : 1 / Real.pi < 2 / Real.pi := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right (by norm_num : (1 : ℝ) < 2) (by positivity)
  exact lt_of_le_of_lt ((dM_le_inv_pi_mul M).trans h2) h3

theorem two_div_pi_sub_dM_pos (M : ℕ) : 0 < 2 / Real.pi - dM M :=
  sub_pos.mpr (dM_lt_two_div_pi M)

/-- `L_M > π/2`: the explicit sup-norm lower bound is strictly above the
classical baseline. -/
theorem LM_gt_pi_div_two (M : ℕ) : Real.pi / 2 < LM M := by
  unfold LM
  have hpos : 0 < 2 / Real.pi - dM M := two_div_pi_sub_dM_pos M
  have hlt : 2 / Real.pi - dM M < 2 / Real.pi := by
    nlinarith [dM_pos M]
  have h : 1 / (2 / Real.pi) < 1 / (2 / Real.pi - dM M) :=
    one_div_lt_one_div_of_lt hpos hlt
  have hone : 1 / (2 / Real.pi) = Real.pi / 2 := by rw [one_div_div]
  simpa [hone] using h

/-- `δ_M > 0`: the explicit strict gap. -/
theorem deltaM_pos (M : ℕ) : 0 < deltaM M := by
  unfold deltaM
  exact sub_pos.mpr (LM_gt_pi_div_two M)

theorem deltaM_eq (M : ℕ) :
    deltaM M =
      1 / (2 / Real.pi -
          Real.sin (1 / (4 * ((2 * M + 1 : ℕ) : ℝ))) /
            (Real.pi * ((2 * M + 1 : ℕ) : ℝ))) -
        Real.pi / 2 := rfl

end FiniteSpectrumGap
