import MathlibAux.LogDerivArgumentPrinciple

/-!
# Removing the logarithmic poles on a rectangle's left edge

Subtract every zero principal part and normalize the removable singularities;
then put back only the strictly interior principal parts. This constructs one
function analytic along the entire boundary, with the actual logarithmic
derivative's real trace on the left edge and the interior residue integral.
No integral of the singular complex logarithmic derivative along the left
edge is asserted or split. Left-edge corner zeros are excluded explicitly.
-/

open Complex Set
open scoped BigOperators Interval

namespace MathlibAux

/-- Construct a left-regularized logarithmic derivative, not just a hypothetical
continuous trace. All five conclusions refer to the same function. -/
theorem exists_left_regularized_logDeriv
    {f : ℂ → ℂ} {x0 x1 U T : ℝ}
    (hx : x0 < x1) (hUT : U < T)
    (off left : Finset ℂ) (m : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[U, T]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[U, T]]),
      f z = 0 ↔ z ∈ off ∪ left)
    (hoff : ∀ p ∈ off, x0 < p.re ∧ p.re < x1 ∧ U < p.im ∧ p.im < T)
    (hleft : ∀ p ∈ left, p.re = x0 ∧ U < p.im ∧ p.im < T)
    (horder : ∀ p ∈ off ∪ left, analyticOrderAt f p = m p) :
    ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G (([[x0, x1]] ×ℂ [[U, T]]) \ (off : Set ℂ)) ∧
      (∀ z ∈ ([[x0, x1]] ×ℂ [[U, T]]), f z ≠ 0 →
        G z = logDeriv f z - ∑ p ∈ left, (z - p)⁻¹ * (m p : ℂ)) ∧
      ContinuousOn (fun t : ℝ => (G ((x0 : ℂ) + I * t)).re) (Icc U T) ∧
      (∀ t ∈ Icc U T, f ((x0 : ℂ) + I * t) ≠ 0 →
        (G ((x0 : ℂ) + I * t)).re =
          (logDeriv f ((x0 : ℂ) + I * t)).re) ∧
      boundaryRectIntegral G x0 x1 U T =
        (2 * Real.pi * I) * ∑ p ∈ off, (m p : ℂ) := by
  classical
  let K : Set ℂ := [[x0, x1]] ×ℂ [[U, T]]
  let zeros := off ∪ left
  let raw : ℂ → ℂ := fun z =>
    logDeriv f z - ∑ p ∈ zeros, (m p : ℂ) * (z - p)⁻¹
  let H := toMeromorphicNFOn raw K
  let G : ℂ → ℂ := fun z => H z + ∑ p ∈ off, (z - p)⁻¹ * (m p : ℂ)
  have hH : AnalyticOnNhd ℂ H K :=
    ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts
      hf zeros m hzero horder
  have hrawMeromorphic : MeromorphicOn raw K :=
    ZeroFreeRegion.meromorphicOn_logDeriv_sub_finset_principalParts
      hf.meromorphicOn zeros m
  have hdisjoint : Disjoint off left := by
    apply Finset.disjoint_left.mpr
    intro p hp hl
    have hpgt := (hoff p hp).1
    rw [(hleft p hl).1] at hpgt
    exact (lt_irrefl x0) hpgt
  have hG : AnalyticOnNhd ℂ G (K \ (off : Set ℂ)) := by
    intro z hz
    have hsum : AnalyticAt ℂ
        (fun w : ℂ => ∑ p ∈ off, (w - p)⁻¹ * (m p : ℂ)) z := by
      apply Finset.analyticAt_fun_sum
      intro p hp
      have hzp : z ≠ p := by
        intro heq
        subst p
        exact hz.2 hp
      exact ((analyticAt_id.sub analyticAt_const).inv
        (sub_ne_zero.mpr hzp)).mul analyticAt_const
    exact (hH z hz.1).add hsum
  have hlink : ∀ z ∈ K, f z ≠ 0 →
      G z = logDeriv f z - ∑ p ∈ left, (z - p)⁻¹ * (m p : ℂ) := by
    intro z hz hfz
    have hzNotZero : z ∉ zeros := fun hp => hfz ((hzero z hz).mpr hp)
    have hlog : AnalyticAt ℂ (logDeriv f) z :=
      (hf z hz).deriv.div (hf z hz) hfz
    have hsum : AnalyticAt ℂ
        (fun w : ℂ => ∑ p ∈ zeros, (m p : ℂ) * (w - p)⁻¹) z := by
      apply Finset.analyticAt_fun_sum
      intro p hp
      have hzp : z ≠ p := by
        intro heq
        subst p
        exact hzNotZero hp
      exact analyticAt_const.mul
        ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzp))
    have hrawAnalytic : AnalyticAt ℂ raw z := hlog.sub hsum
    have hHeq : H z = raw z := by
      rw [show H z = toMeromorphicNFOn raw K z by rfl,
        toMeromorphicNFOn_eq_toMeromorphicNFAt hrawMeromorphic hz,
        congrFun (toMeromorphicNFAt_eq_self.mpr hrawAnalytic.meromorphicNFAt) z]
    have hcomm : (∑ p ∈ zeros, (m p : ℂ) * (z - p)⁻¹) =
        ∑ p ∈ zeros, (z - p)⁻¹ * (m p : ℂ) := by
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    dsimp only [G]
    rw [hHeq]
    dsimp only [raw]
    rw [hcomm, show zeros = off ∪ left by rfl, Finset.sum_union hdisjoint]
    ring
  have hleftMem : ∀ t ∈ Icc U T,
      ((x0 : ℂ) + I * t) ∈ K \ (off : Set ℂ) := by
    intro t ht
    constructor
    · simp only [K, mem_reProdIm, uIcc_of_le hx.le, uIcc_of_le hUT.le]
      simpa using And.intro (And.intro (le_refl x0) hx.le) ht
    · intro hp
      have hgt := (hoff _ hp).1
      simp at hgt
  have hparam : Continuous (fun t : ℝ => (x0 : ℂ) + I * t) :=
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have htraceCont : ContinuousOn (fun t : ℝ => (G ((x0 : ℂ) + I * t)).re)
      (Icc U T) :=
    Complex.continuous_re.comp_continuousOn
      (hG.continuousOn.comp hparam.continuousOn hleftMem)
  refine ⟨G, hG, hlink, htraceCont, ?_, ?_⟩
  · intro t ht hfne
    rw [hlink _ (hleftMem t ht).1 hfne, Complex.sub_re]
    have hprincipalRe :
        (∑ p ∈ left, (((x0 : ℂ) + I * t) - p)⁻¹ * (m p : ℂ)).re = 0 := by
      rw [Complex.re_sum]
      apply Finset.sum_eq_zero
      intro p hp
      simp [Complex.mul_re, Complex.inv_re, (hleft p hp).1]
    rw [hprincipalRe, sub_zero]
  · exact boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
      off (fun p => (m p : ℂ)) hH.differentiableOn hoff

end MathlibAux
