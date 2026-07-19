import ZeroFreeRegion.VinogradovKorobov.VinogradovFiniteConditioning

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Integers in `{1, ..., X}` lying in the residue class `ξ` modulo `Q`. -/
def vinogradovResidueClassFinset
    (Q X : ℕ) [NeZero Q] (ξ : ZMod Q) : Finset (Fin X) :=
  Finset.univ.filter fun m : Fin X ↦ ((m.val + 1 : ℕ) : ZMod Q) = ξ

@[simp] theorem mem_vinogradovResidueClassFinset
    (Q X : ℕ) [NeZero Q] (ξ : ZMod Q) (m : Fin X) :
    m ∈ vinogradovResidueClassFinset Q X ξ ↔
      ((m.val + 1 : ℕ) : ZMod Q) = ξ := by
  simp [vinogradovResidueClassFinset]

/-- A finite exponential sum restricted to one residue class.  The summand
is kept abstract so that the same conditioning API applies to ordinary,
weighted, and shifted Weyl sums. -/
def vinogradovResidueClassSum
    {E : Type*} [AddCommMonoid E]
    (Q X : ℕ) [NeZero Q] (ξ : ZMod Q) (f : Fin X → E) : E :=
  ∑ m ∈ vinogradovResidueClassFinset Q X ξ, f m

/-- Inside a fixed class modulo `p^a`, filtering by a compatible class
modulo `p^b` gives exactly that finer residue class. -/
theorem vinogradovResidueClassFinset_filter_refinement
    (p a b X : ℕ) (hab : a ≤ b)
    [NeZero (p ^ a)] [NeZero (p ^ b)]
    (ξ : ZMod (p ^ a)) (z : ZMod (p ^ b))
    (hz : ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ) :
    (vinogradovResidueClassFinset (p ^ a) X ξ).filter
        (fun m : Fin X ↦ ((m.val + 1 : ℕ) : ZMod (p ^ b)) = z) =
      vinogradovResidueClassFinset (p ^ b) X z := by
  ext m
  simp only [Finset.mem_filter, mem_vinogradovResidueClassFinset]
  constructor
  · exact fun h ↦ h.2
  · intro hfine
    refine ⟨?_, hfine⟩
    have hcast := congrArg
      (ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a))) hfine
    rw [ZMod.castHom_apply,
      ZMod.cast_natCast (pow_dvd_pow p hab)] at hcast
    exact hcast.trans hz

/-- Pointwise residue conditioning for finite Weyl sums.  A class modulo
`p^a` splits into exactly `p^(b-a)` classes modulo `p^b`, and finite Holder
controls the `(n+1)`-st power with the sharp cardinality loss. -/
theorem norm_vinogradovResidueClassSum_pow_le_refinement
    {E : Type*} [SeminormedAddCommGroup E]
    (p a b X : ℕ) (hp : 0 < p) (hab : a ≤ b)
    [NeZero (p ^ a)] [NeZero (p ^ b)]
    (ξ : ZMod (p ^ a)) (f : Fin X → E) (n : ℕ) :
    ‖vinogradovResidueClassSum (p ^ a) X ξ f‖ ^ (n + 1) ≤
      ((p ^ (b - a) : ℕ) : ℝ) ^ n *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          ‖vinogradovResidueClassSum (p ^ b) X z f‖ ^ (n + 1) := by
  let S := vinogradovResidueClassFinset (p ^ a) X ξ
  have hcoarse : ∀ m ∈ S,
      ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a))
          (((m.val + 1 : ℕ) : ZMod (p ^ b))) = ξ := by
    intro m hm
    have hm' : ((m.val + 1 : ℕ) : ZMod (p ^ a)) = ξ := by
      simpa [S] using hm
    rw [ZMod.castHom_apply,
      ZMod.cast_natCast (pow_dvd_pow p hab)]
    exact hm'
  have hrefine := norm_finset_sum_pow_le_primePower_fiber_refinement
    p a b hp hab ξ S (fun m : Fin X ↦ ((m.val + 1 : ℕ) : ZMod (p ^ b)))
      f hcoarse n
  change
    ‖∑ m ∈ S, f m‖ ^ (n + 1) ≤
      ((p ^ (b - a) : ℕ) : ℝ) ^ n *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          ‖∑ m ∈ vinogradovResidueClassFinset (p ^ b) X z, f m‖ ^ (n + 1)
  rw [show S = vinogradovResidueClassFinset (p ^ a) X ξ from rfl]
  refine hrefine.trans_eq ?_
  apply congrArg (fun u : ℝ ↦ ((p ^ (b - a) : ℕ) : ℝ) ^ n * u)
  apply Finset.sum_congr rfl
  intro z hz
  congr 2
  rw [vinogradovResidueClassFinset_filter_refinement p a b X hab ξ z
    (Finset.mem_filter.mp hz).2]

/-- Finite conditioned mean-value transition.  Summing the pointwise
conditioning inequality over an arbitrary finite coefficient space commutes
the coefficient sum with the finer residue classes. -/
theorem sum_norm_vinogradovResidueClassSum_pow_le_refinement
    {C E : Type*} [Fintype C] [SeminormedAddCommGroup E]
    (p a b X : ℕ) (hp : 0 < p) (hab : a ≤ b)
    [NeZero (p ^ a)] [NeZero (p ^ b)]
    (ξ : ZMod (p ^ a)) (phase : C → Fin X → E) (n : ℕ) :
    (∑ c : C, ‖vinogradovResidueClassSum (p ^ a) X ξ (phase c)‖ ^ (n + 1)) ≤
      ((p ^ (b - a) : ℕ) : ℝ) ^ n *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          ∑ c : C,
            ‖vinogradovResidueClassSum (p ^ b) X z (phase c)‖ ^ (n + 1) := by
  calc
    (∑ c : C,
        ‖vinogradovResidueClassSum (p ^ a) X ξ (phase c)‖ ^ (n + 1)) ≤
        ∑ c : C, ((p ^ (b - a) : ℕ) : ℝ) ^ n *
          ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
            ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
            ‖vinogradovResidueClassSum (p ^ b) X z (phase c)‖ ^ (n + 1) := by
      apply Finset.sum_le_sum
      intro c hc
      exact norm_vinogradovResidueClassSum_pow_le_refinement
        p a b X hp hab ξ (phase c) n
    _ = ((p ^ (b - a) : ℕ) : ℝ) ^ n *
        ∑ c : C,
          ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
            ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
            ‖vinogradovResidueClassSum (p ^ b) X z (phase c)‖ ^ (n + 1) := by
      rw [Finset.mul_sum]
    _ = ((p ^ (b - a) : ℕ) : ℝ) ^ n *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          ∑ c : C,
            ‖vinogradovResidueClassSum (p ^ b) X z (phase c)‖ ^ (n + 1) := by
      congr 1
      rw [Finset.sum_comm]

end

end ZeroFreeRegion.VinogradovKorobov
