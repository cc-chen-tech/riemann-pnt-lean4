import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Finite Holder conditioning in the form used for exponential sums.  The
`(n + 1)`-st power of a finite sum is controlled by the corresponding moment,
at the cost of the `n`-th power of the number of summands. -/
theorem norm_finset_sum_pow_le_card_mul_sum_norm_pow
    {ι E : Type*} [SeminormedAddCommGroup E]
    (S : Finset ι) (f : ι → E) (n : ℕ) :
    ‖∑ i ∈ S, f i‖ ^ (n + 1) ≤
      (S.card : ℝ) ^ n * ∑ i ∈ S, ‖f i‖ ^ (n + 1) := by
  calc
    ‖∑ i ∈ S, f i‖ ^ (n + 1) ≤
        (∑ i ∈ S, ‖f i‖) ^ (n + 1) := by
      gcongr
      exact norm_sum_le S f
    _ ≤ (S.card : ℝ) ^ n * ∑ i ∈ S, ‖f i‖ ^ (n + 1) :=
      pow_sum_le_card_mul_sum_pow (fun _ _ ↦ norm_nonneg _) n

/-- Refining a finite sum into the fibers of a finite partition and applying
Holder costs only the number of target cells.  This is the abstract finite
form of the conditioning step in efficient congruencing. -/
theorem norm_finset_sum_pow_le_fiber_refinement
    {ι κ E : Type*} [DecidableEq κ] [SeminormedAddCommGroup E]
    (S : Finset ι) (T : Finset κ) (residue : ι → κ) (f : ι → E)
    (hresidue : ∀ i ∈ S, residue i ∈ T) (n : ℕ) :
    ‖∑ i ∈ S, f i‖ ^ (n + 1) ≤
      (T.card : ℝ) ^ n *
        ∑ z ∈ T, ‖∑ i ∈ S with residue i = z, f i‖ ^ (n + 1) := by
  rw [← Finset.sum_fiberwise_of_maps_to hresidue]
  exact norm_finset_sum_pow_le_card_mul_sum_norm_pow T
    (fun z ↦ ∑ i ∈ S with residue i = z, f i) n

/-- Residue-class specialization of finite conditioning.  Splitting a sum
into its classes modulo `Q` costs exactly `Q^n` in the `(n + 1)`-st moment. -/
theorem norm_finset_sum_pow_le_zmod_refinement
    {ι E : Type*} [SeminormedAddCommGroup E]
    (Q : ℕ) [NeZero Q] (S : Finset ι) (residue : ι → ZMod Q)
    (f : ι → E) (n : ℕ) :
    ‖∑ i ∈ S, f i‖ ^ (n + 1) ≤
      (Q : ℝ) ^ n *
        ∑ z : ZMod Q, ‖∑ i ∈ S with residue i = z, f i‖ ^ (n + 1) := by
  simpa [ZMod.card] using
    (norm_finset_sum_pow_le_fiber_refinement S (Finset.univ : Finset (ZMod Q))
      residue f (fun _ _ ↦ Finset.mem_univ _) n)

/-- Every residue class modulo `p^a` has exactly `p^(b-a)` lifts modulo
`p^b`.  This packages the precise cardinality needed when an efficient
congruencing mean value is conditioned from level `a` to level `b`. -/
theorem card_zmod_primePower_castHom_fiber
    (p a b : ℕ) (hp : 0 < p) (hab : a ≤ b)
    [NeZero (p ^ a)] [NeZero (p ^ b)] (ξ : ZMod (p ^ a)) :
    (Finset.univ.filter fun z : ZMod (p ^ b) ↦
      ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ).card =
        p ^ (b - a) := by
  let cast : ZMod (p ^ b) →+ ZMod (p ^ a) :=
    (ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a))).toAddMonoidHom
  have hsurjective : Function.Surjective cast :=
    ZMod.castHom_surjective (pow_dvd_pow p hab)
  have hfiber (y : ZMod (p ^ a)) :
      (Finset.univ.filter fun z : ZMod (p ^ b) ↦ cast z = y).card =
        (Finset.univ.filter fun z : ZMod (p ^ b) ↦ cast z = ξ).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range cast (hsurjective y) (hsurjective ξ)
  have htotal :
      p ^ b = p ^ a *
        (Finset.univ.filter fun z : ZMod (p ^ b) ↦ cast z = ξ).card := by
    calc
      p ^ b = (Finset.univ : Finset (ZMod (p ^ b))).card := by simp [ZMod.card]
      _ = ∑ y : ZMod (p ^ a),
          (Finset.univ.filter fun z : ZMod (p ^ b) ↦ cast z = y).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)
      _ = ∑ _y : ZMod (p ^ a),
          (Finset.univ.filter fun z : ZMod (p ^ b) ↦ cast z = ξ).card := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hfiber y
      _ = p ^ a *
          (Finset.univ.filter fun z : ZMod (p ^ b) ↦ cast z = ξ).card := by
        simp [ZMod.card]
  have hpower : p ^ b = p ^ a * p ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_of_le hab]
  apply Nat.eq_of_mul_eq_mul_left (pow_pos hp a)
  exact htotal.symm.trans hpower

/-- Prime-power residue conditioning.  If all terms begin in one class
modulo `p^a`, splitting them into their classes modulo `p^b` costs exactly
`p^((b-a)n)` in the `(n+1)`-st moment. -/
theorem norm_finset_sum_pow_le_primePower_fiber_refinement
    {ι E : Type*} [SeminormedAddCommGroup E]
    (p a b : ℕ) (hp : 0 < p) (hab : a ≤ b)
    [NeZero (p ^ a)] [NeZero (p ^ b)] (ξ : ZMod (p ^ a))
    (S : Finset ι) (residue : ι → ZMod (p ^ b)) (f : ι → E)
    (hcoarse : ∀ i ∈ S,
      ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) (residue i) = ξ)
    (n : ℕ) :
    ‖∑ i ∈ S, f i‖ ^ (n + 1) ≤
      ((p ^ (b - a) : ℕ) : ℝ) ^ n *
        ∑ z ∈ (Finset.univ.filter fun z : ZMod (p ^ b) ↦
          ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ),
          ‖∑ i ∈ S with residue i = z, f i‖ ^ (n + 1) := by
  have hrefine := norm_finset_sum_pow_le_fiber_refinement S
    (Finset.univ.filter fun z : ZMod (p ^ b) ↦
      ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = ξ)
    residue f (fun i hi ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcoarse i hi⟩) n
  simpa only [card_zmod_primePower_castHom_fiber p a b hp hab ξ] using hrefine

end

end ZeroFreeRegion.VinogradovKorobov
