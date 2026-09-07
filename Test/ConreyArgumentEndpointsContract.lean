import HardyTheorem.ConreyArgumentEndpoints

open Complex Set Filter Topology
open HardyTheorem

-- Endpoints may be eta zeros. The limit belongs to the supplied component
-- logarithm, not to an unrelated locally selected branch.
example {g g0 g1 L a b : ℝ} {ell : ℝ → ℂ} (hg : g ≠ 0) (hab : a < b)
    (hell : ContinuousOn ell (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) =
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) :
    ∃ A B : ℝ,
      Tendsto (fun t => (ell t).im) (nhdsWithin a (Ioi a)) (nhds A) ∧
      Tendsto (fun t => (ell t).im) (nhdsWithin b (Iio b)) (nhds B) := by
  exact exists_conreyDegreeOneEta_component_argument_limits hg hab hell hexp

-- A zero-free open eta component needs no separate endpoint nonvanishing
-- or finite-order assumptions; both finite phase endpoints are produced.
example {g g0 g1 L a b : ℝ} (hg : g ≠ 0) (hab : a < b)
    (hne : ∀ t ∈ Ioo a b,
      conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t) ≠ 0) :
    ∃ ell : ℝ → ℂ, ∃ A B : ℝ,
      ContinuousOn ell (Ioo a b) ∧
      (∀ t ∈ Ioo a b, Complex.exp (ell t) =
        conreyDegreeOneEta g g0 g1 L (conreyCriticalPoint t)) ∧
      Tendsto (fun t => (ell t).im) (nhdsWithin a (Ioi a)) (nhds A) ∧
      Tendsto (fun t => (ell t).im) (nhdsWithin b (Iio b)) (nhds B) := by
  exact exists_conreyDegreeOneEta_continuousLog_with_argument_limits hg hab hne

#print axioms exists_conreyDegreeOneEta_component_argument_limits
#print axioms exists_conreyDegreeOneEta_continuousLog_with_argument_limits
