import PrimeNumberTheorem.ZeroDensityLayerBudgetAntiCancellation

/-!
# From finite-cluster recurrence to Omega bounds

The anti-cancellation module produces a large main-cluster value arbitrarily
far out.  To turn that statement into an Omega theorem for the full explicit
formula, one must show that the complementary zeros and truncation remainder
are eventually smaller than that main value.

This file isolates and proves that transfer.  It has no dependency on the
canonical complementary-bound implementation: Carlson layer estimates may
discharge `IsEventuallyHalfSmall` later through the public interface.
-/

namespace PrimeNumberTheorem

/-- `f` has norm at least `amplitude` at points beyond every starting scale. -/
def HasFarNormWitness (f : ℝ → ℝ) (amplitude : ℝ) : Prop :=
  ∀ X, ∃ x, X ≤ x ∧ amplitude ≤ |f x|

/-- `f` has a positive value of size `amplitude` beyond every starting scale. -/
def HasFarPositiveWitness (f : ℝ → ℝ) (amplitude : ℝ) : Prop :=
  ∀ X, ∃ x, X ≤ x ∧ amplitude ≤ f x

/-- `f` has a negative value of size `amplitude` beyond every starting scale. -/
def HasFarNegativeWitness (f : ℝ → ℝ) (amplitude : ℝ) : Prop :=
  ∀ X, ∃ x, X ≤ x ∧ f x ≤ -amplitude

/-- Both signs recur with the same certified amplitude. -/
structure HasFarSignedWitnesses (f : ℝ → ℝ) (amplitude : ℝ) : Prop where
  positive : HasFarPositiveWitness f amplitude
  negative : HasFarNegativeWitness f amplitude

/--
The remainder is eventually at most half the main-cluster amplitude.  This is
the exact asymptotic interface required from dynamic Carlson layer budgets.
-/
def IsEventuallyHalfSmall (remainder : ℝ → ℝ) (amplitude : ℝ) : Prop :=
  ∀ᶠ x in Filter.atTop, |remainder x| ≤ amplitude / 2

/--
Absolute Omega transfer.  A recurrent main term of amplitude `A`, together
with an eventually `A / 2`-small remainder, forces recurrent values of the full
error of amplitude `A / 2`.
-/
theorem hasFarNormWitness_add_of_eventuallyHalfSmall
    {error main remainder : ℝ → ℝ} {amplitude : ℝ}
    (hmain : HasFarNormWitness main amplitude)
    (hsmall : IsEventuallyHalfSmall remainder amplitude)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarNormWitness error (amplitude / 2) := by
  intro X
  rcases Filter.eventually_atTop.1 hsmall with ⟨R, hR⟩
  rcases hmain (max X R) with ⟨x, hx, hmainx⟩
  refine ⟨x, (le_max_left X R).trans hx, ?_⟩
  have hxR : R ≤ x := (le_max_right X R).trans hx
  have hsmallx := hR x hxR
  have hrewrite : main x = error x - remainder x := by
    rw [hdecomp x]
    ring
  have htriangle : |main x| ≤ |error x| + |remainder x| := by
    rw [hrewrite]
    simpa only [Real.norm_eq_abs] using
      (norm_sub_le (error x) (remainder x))
  linarith

/--
Positive Omega transfer.  A recurrent positive main value survives an
eventually half-amplitude perturbation.
-/
theorem hasFarPositiveWitness_add_of_eventuallyHalfSmall
    {error main remainder : ℝ → ℝ} {amplitude : ℝ}
    (hmain : HasFarPositiveWitness main amplitude)
    (hsmall : IsEventuallyHalfSmall remainder amplitude)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarPositiveWitness error (amplitude / 2) := by
  intro X
  rcases Filter.eventually_atTop.1 hsmall with ⟨R, hR⟩
  rcases hmain (max X R) with ⟨x, hx, hmainx⟩
  refine ⟨x, (le_max_left X R).trans hx, ?_⟩
  have hxR : R ≤ x := (le_max_right X R).trans hx
  have hsmallx := hR x hxR
  have hremainderLower : -(amplitude / 2) ≤ remainder x :=
    (abs_le.mp hsmallx).1
  rw [hdecomp x]
  linarith

/--
Negative Omega transfer.  A recurrent negative main value survives an
eventually half-amplitude perturbation.
-/
theorem hasFarNegativeWitness_add_of_eventuallyHalfSmall
    {error main remainder : ℝ → ℝ} {amplitude : ℝ}
    (hmain : HasFarNegativeWitness main amplitude)
    (hsmall : IsEventuallyHalfSmall remainder amplitude)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarNegativeWitness error (amplitude / 2) := by
  intro X
  rcases Filter.eventually_atTop.1 hsmall with ⟨R, hR⟩
  rcases hmain (max X R) with ⟨x, hx, hmainx⟩
  refine ⟨x, (le_max_left X R).trans hx, ?_⟩
  have hxR : R ≤ x := (le_max_right X R).trans hx
  have hsmallx := hR x hxR
  have hremainderUpper : remainder x ≤ amplitude / 2 :=
    (abs_le.mp hsmallx).2
  rw [hdecomp x]
  linarith

/--
Two-sided Omega-plus/minus transfer.  The same eventual remainder estimate is
shared by the positive and negative witnesses.
-/
theorem hasFarSignedWitnesses_add_of_eventuallyHalfSmall
    {error main remainder : ℝ → ℝ} {amplitude : ℝ}
    (hmain : HasFarSignedWitnesses main amplitude)
    (hsmall : IsEventuallyHalfSmall remainder amplitude)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarSignedWitnesses error (amplitude / 2) where
  positive :=
    hasFarPositiveWitness_add_of_eventuallyHalfSmall
      hmain.positive hsmall hdecomp
  negative :=
    hasFarNegativeWitness_add_of_eventuallyHalfSmall
      hmain.negative hsmall hdecomp

end PrimeNumberTheorem
