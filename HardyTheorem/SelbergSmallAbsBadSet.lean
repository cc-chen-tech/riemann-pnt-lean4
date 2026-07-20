import HardyTheorem.SelbergShortAbsLower

open MeasureTheory Set

namespace HardyTheorem

/-!
# The small-absolute-mass Selberg bad set

The first zeta approximation reduces a small mollified absolute integral to
an unusually large value of one explicit finite Dirichlet polynomial.  This
file records the resulting Chebyshev estimate.  The remaining analytic input
is a mean-square bound for that finite polynomial over the start parameter.
-/

/-- A lower bound for the mollified absolute mass, together with an `L2`
bound for its finite-polynomial error, controls the starts where the absolute
mass is small. -/
theorem volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_of_shortDirichletL2
    {X N : ℕ} {A B H eta R M : ℝ}
    (hthreshold : 0 < H - eta - R)
    (hlower : ∀ t ∈ Icc A B,
      H - ‖selbergMollifiedShortDirichletPolynomial H N X t‖ - R ≤
        selbergMoebiusAbsShortIntegral X H t)
    (hQint : Integrable
      (fun t => Complex.normSq
        (selbergMollifiedShortDirichletPolynomial H N X t))
      (volume.restrict (Icc A B)))
    (hQbound :
      (∫ t, Complex.normSq
          (selbergMollifiedShortDirichletPolynomial H N X t)
        ∂volume.restrict (Icc A B)) ≤ M) :
    volume.real
        (selbergSmallAbsoluteMassStarts X H eta ∩ Icc A B) ≤
      M / (H - eta - R) ^ 2 := by
  let Q : ℝ → ℂ := fun t =>
    selbergMollifiedShortDirichletPolynomial H N X t
  let epsilon : ℝ := (H - eta - R) ^ 2
  let largeQ : Set ℝ := {t | epsilon ≤ Complex.normSq (Q t)}
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  have hsubset :
      selbergSmallAbsoluteMassStarts X H eta ∩ Icc A B ⊆
        largeQ ∩ Icc A B := by
    intro t ht
    have hsmall : selbergMoebiusAbsShortIntegral X H t ≤ eta := by
      simpa only [selbergSmallAbsoluteMassStarts, Set.mem_setOf_eq] using ht.1
    have hnorm : H - eta - R ≤ ‖Q t‖ := by
      have := hlower t ht.2
      dsimp only [Q]
      linarith
    constructor
    · change epsilon ≤ Complex.normSq (Q t)
      rw [Complex.normSq_eq_norm_sq]
      dsimp only [epsilon]
      simpa only [pow_two] using
        (mul_self_le_mul_self hthreshold.le hnorm)
    · exact ht.2
  have hmarkov :
      epsilon * volume.real (largeQ ∩ Icc A B) ≤ M := by
    have h := mul_meas_ge_le_integral_of_nonneg
      (μ := volume.restrict (Icc A B))
      (Filter.Eventually.of_forall fun t => Complex.normSq_nonneg (Q t))
      (by simpa only [Q] using hQint) epsilon
    rw [measureReal_restrict_apply' measurableSet_Icc] at h
    exact h.trans (by simpa only [Q] using hQbound)
  have hfinite : volume (largeQ ∩ Icc A B) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hmono :
      volume.real
          (selbergSmallAbsoluteMassStarts X H eta ∩ Icc A B) ≤
        volume.real (largeQ ∩ Icc A B) :=
    measureReal_mono hsubset hfinite
  apply hmono.trans
  exact (le_div_iff₀ hepsilon).2 (by simpa [mul_comm] using hmarkov)

end HardyTheorem
