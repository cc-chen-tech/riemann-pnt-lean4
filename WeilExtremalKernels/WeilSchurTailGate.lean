import WeilExtremalKernels.WeilFiniteToInfiniteGate

/-!
# Core-tail Schur budgets for extending finite Weil sections

To extend a certified cutoff, split a vector into old coordinates `x` and
new tail coordinates `y`.  The enlarged quadratic form has the shape

`core x + 2 * coupling x y + tail y`.

The exact analytic task is to show that lower bounds for the core and tail
absorb the absolute coupling.  This module formalizes that statement with
explicit spent and unspent coercivity budgets.
-/

namespace WeilExtremalKernels

/-- Quadratic form of a core-tail block decomposition. -/
def blockQuadraticForm
    {X Y : Type*}
    (core : X -> Real)
    (tail : Y -> Real)
    (coupling : X -> Y -> Real)
    (x : X) (y : Y) : Real :=
  core x + 2 * coupling x y + tail y

/-- Exact Schur absorption criterion.

The core and tail lower bounds are allowed to spend all their coercivity on
the coupling. -/
theorem blockQuadraticForm_nonneg_of_schur_budget
    {X Y : Type*}
    (core : X -> Real)
    (tail : Y -> Real)
    (coupling : X -> Y -> Real)
    (coreNormSq : X -> Real)
    (tailNormSq : Y -> Real)
    (coreBudget tailBudget : Real)
    (hcore :
      forall x, coreBudget * coreNormSq x <= core x)
    (htail :
      forall y, tailBudget * tailNormSq y <= tail y)
    (hcoupling :
      forall x y,
        2 * |coupling x y| <=
          coreBudget * coreNormSq x +
            tailBudget * tailNormSq y) :
    forall x y,
      0 <= blockQuadraticForm core tail coupling x y := by
  intro x y
  have hcouplingLower :
      -2 * |coupling x y| <= 2 * coupling x y := by
    have := neg_abs_le (coupling x y)
    linarith
  have hc := hcore x
  have ht := htail y
  have hb := hcoupling x y
  unfold blockQuadraticForm
  linarith

/-- Quantitative Schur criterion retaining explicit coercivity after the
coupling has been absorbed. -/
theorem blockQuadraticForm_ge_reserve_of_schur_budget
    {X Y : Type*}
    (core : X -> Real)
    (tail : Y -> Real)
    (coupling : X -> Y -> Real)
    (coreNormSq : X -> Real)
    (tailNormSq : Y -> Real)
    (coreSpend tailSpend coreReserve tailReserve : Real)
    (hcore :
      forall x,
        (coreSpend + coreReserve) * coreNormSq x <= core x)
    (htail :
      forall y,
        (tailSpend + tailReserve) * tailNormSq y <= tail y)
    (hcoupling :
      forall x y,
        2 * |coupling x y| <=
          coreSpend * coreNormSq x +
            tailSpend * tailNormSq y) :
    forall x y,
      coreReserve * coreNormSq x +
          tailReserve * tailNormSq y <=
        blockQuadraticForm core tail coupling x y := by
  intro x y
  have hcouplingLower :
      -2 * |coupling x y| <= 2 * coupling x y := by
    have := neg_abs_le (coupling x y)
    linarith
  have hc := hcore x
  have ht := htail y
  have hb := hcoupling x y
  unfold blockQuadraticForm
  nlinarith

/-- Nonnegative reserves give positive semidefiniteness of the enlarged
block. -/
theorem blockQuadraticForm_nonneg_of_schur_reserve
    {X Y : Type*}
    (core : X -> Real)
    (tail : Y -> Real)
    (coupling : X -> Y -> Real)
    (coreNormSq : X -> Real)
    (tailNormSq : Y -> Real)
    (coreSpend tailSpend coreReserve tailReserve : Real)
    (hcoreNorm : forall x, 0 <= coreNormSq x)
    (htailNorm : forall y, 0 <= tailNormSq y)
    (hcoreReserve : 0 <= coreReserve)
    (htailReserve : 0 <= tailReserve)
    (hcore :
      forall x,
        (coreSpend + coreReserve) * coreNormSq x <= core x)
    (htail :
      forall y,
        (tailSpend + tailReserve) * tailNormSq y <= tail y)
    (hcoupling :
      forall x y,
        2 * |coupling x y| <=
          coreSpend * coreNormSq x +
            tailSpend * tailNormSq y) :
    forall x y,
      0 <= blockQuadraticForm core tail coupling x y := by
  intro x y
  have hlower :=
    blockQuadraticForm_ge_reserve_of_schur_budget
      core tail coupling coreNormSq tailNormSq
      coreSpend tailSpend coreReserve tailReserve
      hcore htail hcoupling x y
  have hreserve :
      0 <= coreReserve * coreNormSq x +
        tailReserve * tailNormSq y :=
    add_nonneg
      (mul_nonneg hcoreReserve (hcoreNorm x))
      (mul_nonneg htailReserve (htailNorm y))
  exact hreserve.trans hlower

/-- Positive reserves give strict positivity when both component norms are
definite and the block vector is nonzero. -/
theorem blockQuadraticForm_pos_of_schur_reserve
    {X Y : Type*} [Zero X] [Zero Y]
    (core : X -> Real)
    (tail : Y -> Real)
    (coupling : X -> Y -> Real)
    (coreNormSq : X -> Real)
    (tailNormSq : Y -> Real)
    (coreSpend tailSpend coreReserve tailReserve : Real)
    (hcoreNormNonneg : forall x, 0 <= coreNormSq x)
    (htailNormNonneg : forall y, 0 <= tailNormSq y)
    (hcoreNorm : forall x, x != 0 -> 0 < coreNormSq x)
    (htailNorm : forall y, y != 0 -> 0 < tailNormSq y)
    (hcoreReserve : 0 < coreReserve)
    (htailReserve : 0 < tailReserve)
    (hcore :
      forall x,
        (coreSpend + coreReserve) * coreNormSq x <= core x)
    (htail :
      forall y,
        (tailSpend + tailReserve) * tailNormSq y <= tail y)
    (hcoupling :
      forall x y,
        2 * |coupling x y| <=
          coreSpend * coreNormSq x +
            tailSpend * tailNormSq y) :
    forall x y, x != 0 \/ y != 0 ->
      0 < blockQuadraticForm core tail coupling x y := by
  intro x y hxy
  have hlower :=
    blockQuadraticForm_ge_reserve_of_schur_budget
      core tail coupling coreNormSq tailNormSq
      coreSpend tailSpend coreReserve tailReserve
      hcore htail hcoupling x y
  have hreserve :
      0 < coreReserve * coreNormSq x +
        tailReserve * tailNormSq y := by
    rcases hxy with hx | hy
    · have hpositive :=
        mul_pos hcoreReserve (hcoreNorm x hx)
      have htailNonneg :
          0 <= tailReserve * tailNormSq y := by
        exact mul_nonneg htailReserve.le (htailNormNonneg y)
      linarith
    · have hpositive :=
        mul_pos htailReserve (htailNorm y hy)
      have hcoreNonneg :
          0 <= coreReserve * coreNormSq x := by
        exact mul_nonneg hcoreReserve.le (hcoreNormNonneg x)
      linarith
  exact hreserve.trans_le hlower

/-- A one-step extension theorem in the form needed for a certified core:
the certified coercivity is split into coupling spend and retained reserve. -/
theorem certified_core_extends_through_schur_tail
    {X Y : Type*}
    (core : X -> Real)
    (tail : Y -> Real)
    (coupling : X -> Y -> Real)
    (coreNormSq : X -> Real)
    (tailNormSq : Y -> Real)
    (coreCoercivity tailCoercivity coreSpend tailSpend : Real)
    (hcore :
      forall x, coreCoercivity * coreNormSq x <= core x)
    (htail :
      forall y, tailCoercivity * tailNormSq y <= tail y)
    (hcoupling :
      forall x y,
        2 * |coupling x y| <=
          coreSpend * coreNormSq x +
            tailSpend * tailNormSq y) :
    forall x y,
      (coreCoercivity - coreSpend) * coreNormSq x +
          (tailCoercivity - tailSpend) * tailNormSq y <=
        blockQuadraticForm core tail coupling x y := by
  apply blockQuadraticForm_ge_reserve_of_schur_budget
    core tail coupling coreNormSq tailNormSq
    coreSpend tailSpend
    (coreCoercivity - coreSpend)
    (tailCoercivity - tailSpend)
  · intro x
    convert hcore x using 1 <;> ring
  · intro y
    convert htail y using 1 <;> ring
  · exact hcoupling

end WeilExtremalKernels
