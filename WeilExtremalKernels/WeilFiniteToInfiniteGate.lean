import WeilExtremalKernels.InfiniteFiniteSectionTransfer
import WeilExtremalKernels.IntegerKernelCutoff

/-!
# Exact finite-to-infinite gates for centered Weil cutoffs

This module states the two mathematically valid ways a family of finite
centered matrices can imply positivity of an infinite quadratic form.

The first route requires positivity, or a uniform coercivity constant, for
every centered cutoff.  The second route compares one finite approximation
with the target form through a rigorous truncation error.  In the strict
case it is exactly the condition

`epsilon > delta`.

A certificate at one cutoff does not manufacture either missing hypothesis.
-/

namespace WeilExtremalKernels

/-- If every centered cutoff is positive semidefinite and every finitely
supported coordinate vector is represented exactly in one such cutoff, then
continuity and density transfer nonnegativity to the infinite space. -/
theorem infinite_nonneg_of_all_centered_cutoffs
    {X : Type*} [TopologicalSpace X]
    (K : Int -> Int -> Real)
    (q : X -> Real)
    (embed : (Int ->₀ Real) -> X)
    (hcutoffs :
      forall (N : Nat) (x : FiniteVector (2 * N + 1)),
        0 <= quadraticForm (integerKernelCutoffMatrix K N) x)
    (hcoordinate :
      forall z : Int ->₀ Real,
        exists (N : Nat) (x : FiniteVector (2 * N + 1)),
          q (embed z) =
            quadraticForm (integerKernelCutoffMatrix K N) x)
    (hdense : Dense (Set.range embed))
    (hcontinuous : Continuous q) :
    forall y : X, 0 <= q y := by
  apply nonneg_of_dense_continuous q (Set.range embed)
    hdense hcontinuous
  intro y hy
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨N, x, hx⟩ := hcoordinate z
  rw [hx]
  exact hcutoffs N x

/-- A uniform lower bound for all centered cutoffs transfers to the infinite
space, provided the coordinate realization also preserves the chosen norm
squared. -/
theorem infinite_coercive_of_uniform_centered_cutoffs
    {X : Type*} [TopologicalSpace X]
    (K : Int -> Int -> Real)
    (q normSq : X -> Real)
    (embed : (Int ->₀ Real) -> X)
    (epsilon : Real)
    (hcutoffs :
      forall (N : Nat) (x : FiniteVector (2 * N + 1)),
        epsilon * squaredNorm x <=
          quadraticForm (integerKernelCutoffMatrix K N) x)
    (hcoordinate :
      forall z : Int ->₀ Real,
        exists (N : Nat) (x : FiniteVector (2 * N + 1)),
          q (embed z) =
              quadraticForm (integerKernelCutoffMatrix K N) x /\
            normSq (embed z) = squaredNorm x)
    (hdense : Dense (Set.range embed))
    (hqContinuous : Continuous q)
    (hnormContinuous : Continuous normSq) :
    forall y : X, epsilon * normSq y <= q y := by
  have hresidualContinuous :
      Continuous (fun y => q y - epsilon * normSq y) :=
    hqContinuous.sub (continuous_const.mul hnormContinuous)
  have hresidualNonneg :
      forall y : X, 0 <= q y - epsilon * normSq y := by
    apply nonneg_of_dense_continuous
      (fun y => q y - epsilon * normSq y)
      (Set.range embed) hdense hresidualContinuous
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    obtain ⟨N, x, hq, hnorm⟩ := hcoordinate z
    rw [hq, hnorm]
    exact sub_nonneg.mpr (hcutoffs N x)
  intro y
  linarith [hresidualNonneg y]

/-- Abstract normalized truncation certificate.

`approximation` has coercivity `epsilon`, while the target differs from it
by at most `delta` in the same norm.  If `delta <= epsilon`, the target is
nonnegative.
-/
theorem nonneg_of_coercive_approximation_and_error
    {X : Type*}
    (target approximation normSq : X -> Real)
    (epsilon delta : Real)
    (hnorm : forall y, 0 <= normSq y)
    (hcoercive :
      forall y, epsilon * normSq y <= approximation y)
    (herror :
      forall y,
        |target y - approximation y| <= delta * normSq y)
    (hmargin : delta <= epsilon) :
    forall y, 0 <= target y := by
  intro y
  have hlower :
      approximation y - delta * normSq y <= target y := by
    have habsLower :=
      neg_abs_le (target y - approximation y)
    have herr := herror y
    linarith
  have hremaining :
      0 <= (epsilon - delta) * normSq y :=
    mul_nonneg (sub_nonneg.mpr hmargin) (hnorm y)
  have hfinite := hcoercive y
  nlinarith

/-- Strict form of the normalized truncation gate.

If `delta < epsilon` and the norm is positive away from zero, the target
quadratic form is strictly positive away from zero.
-/
theorem pos_of_coercive_approximation_and_strict_error
    {X : Type*} [Zero X]
    (target approximation normSq : X -> Real)
    (epsilon delta : Real)
    (hnorm : forall y, y != 0 -> 0 < normSq y)
    (hcoercive :
      forall y, epsilon * normSq y <= approximation y)
    (herror :
      forall y,
        |target y - approximation y| <= delta * normSq y)
    (hmargin : delta < epsilon) :
    forall y, y != 0 -> 0 < target y := by
  intro y hy
  have hlower :
      approximation y - delta * normSq y <= target y := by
    have habsLower :=
      neg_abs_le (target y - approximation y)
    have herr := herror y
    linarith
  have hremaining :
      0 < (epsilon - delta) * normSq y :=
    mul_pos (sub_pos.mpr hmargin) (hnorm y hy)
  have hfinite := hcoercive y
  nlinarith

/-- A sequence version of the same gate.  Any index whose certified
coercivity exceeds its rigorous truncation error proves target
nonnegativity. -/
theorem nonneg_of_exists_finite_section_margin
    {X : Type*}
    (target normSq : X -> Real)
    (approximation : Nat -> X -> Real)
    (epsilon delta : Nat -> Real)
    (hnorm : forall y, 0 <= normSq y)
    (hcoercive :
      forall N y,
        epsilon N * normSq y <= approximation N y)
    (herror :
      forall N y,
        |target y - approximation N y| <= delta N * normSq y)
    (hgate : exists N, delta N <= epsilon N) :
    forall y, 0 <= target y := by
  obtain ⟨N, hN⟩ := hgate
  exact nonneg_of_coercive_approximation_and_error
    target (approximation N) normSq
    (epsilon N) (delta N) hnorm
    (hcoercive N) (herror N) hN

end WeilExtremalKernels
