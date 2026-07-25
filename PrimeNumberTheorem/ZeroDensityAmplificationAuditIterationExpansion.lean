import PrimeNumberTheorem.ZeroDensityAmplificationAuditIterationDepth

namespace PrimeNumberTheorem

open scoped BigOperators

/-- Iterated layer of windows/vertices from explicit roots and adjacency data. -/
def iterativeWindowLayer
    {ι : Type*} [DecidableEq ι]
    (roots : ℝ → Finset ι)
    (children : ℕ → ℝ → ι → Finset ι) : ℕ → ℝ → Finset ι
  | 0, T => roots T
  | n + 1, T =>
      (iterativeWindowLayer roots children n T).biUnion (fun i => children n T i)

/--
A minimal expansion certificate for level-wise growth bookkeeping.
-/
structure IterativeWindowLayerCertificate
    {ι : Type*} [DecidableEq ι] where
  depth : ℕ
  roots : ℝ → Finset ι
  children : ℕ → ℝ → ι → Finset ι
  q : ℝ → ℕ
  hroots_nonempty : ∀ᶠ T in Filter.atTop, 1 ≤ (roots T).card
  hbranch_degree :
    ∀ n, n < depth →
      ∀ᶠ T in Filter.atTop, ∀ i ∈ iterativeWindowLayer roots children n T,
        q T ≤ (children n T i).card
  hchildren_disjoint :
    ∀ n, n < depth →
      ∀ᶠ T in Filter.atTop,
        ((iterativeWindowLayer roots children n T : Set ι).PairwiseDisjoint
          (fun i => children n T i))

/--
If each active node has at least `q(T)` children and each level is pairwise disjoint
across children, then the `n`-th layer has at least `q(T)^n` distinct nodes.
-/
theorem iterativeWindowLayer_qpow_lowerBound
    {ι : Type*} [DecidableEq ι]
    (C : IterativeWindowLayerCertificate (ι := ι))
    (n : ℕ) (hn : n ≤ C.depth) :
    ∀ᶠ T in Filter.atTop,
      C.q T ^ n ≤ (iterativeWindowLayer C.roots C.children n T).card := by
  induction n with
  | zero =>
      filter_upwards [C.hroots_nonempty] with T hroot
      simpa using hroot
  | succ n ih =>
      have hn' : n < C.depth := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have hq : ∀ᶠ T in Filter.atTop,
          C.q T ^ n ≤ (iterativeWindowLayer C.roots C.children n T).card :=
            ih (Nat.le_of_lt hn')
      have hbranch :
          ∀ᶠ T in Filter.atTop, ∀ i ∈ iterativeWindowLayer C.roots C.children n T,
            C.q T ≤ (C.children n T i).card := C.hbranch_degree n hn'
      have hdisjoint :
          ∀ᶠ T in Filter.atTop,
            ((iterativeWindowLayer C.roots C.children n T : Set ι).PairwiseDisjoint
              (fun i => C.children n T i)) := C.hchildren_disjoint n hn'
      filter_upwards [hq, hbranch, hdisjoint] with T hq hbranch hdisjoint
      let layer : Finset ι := iterativeWindowLayer C.roots C.children n T
      have hchildren_sum :
          C.q T * layer.card ≤
            Finset.sum (s := layer) (fun i => (C.children n T i).card) := by
        have hsum_raw :
            Finset.sum (s := layer) (fun i : ι => (C.q T : ℕ)) ≤
              Finset.sum (s := layer) (fun i => (C.children n T i).card) := by
          exact Finset.sum_le_sum (fun i hi => hbranch i hi)
        have hsum_const :
            layer.card * C.q T = Finset.sum (s := layer) (fun _ : ι => (C.q T : ℕ)) := by
          simpa using
            (Finset.sum_const_nat (s := layer) (m := C.q T)
              (f := fun _ : ι => (C.q T : ℕ))
              (by intro x hx; rfl)).symm
        calc
          C.q T * layer.card = Finset.sum (s := layer) (fun _ : ι => (C.q T : ℕ)) := by
            calc
              C.q T * layer.card = layer.card * C.q T := by simp [Nat.mul_comm]
              _ = Finset.sum (s := layer) (fun _ : ι => (C.q T : ℕ)) := hsum_const
          _ ≤ Finset.sum (s := layer) (fun i => (C.children n T i).card) := hsum_raw
      have hbiUnion :
          Finset.sum (s := layer) (fun i => (C.children n T i).card) =
            (iterativeWindowLayer C.roots C.children (n + 1) T).card := by
        simpa [iterativeWindowLayer, layer] using
          (Finset.card_biUnion (s := layer)
            (t := fun i => C.children n T i) hdisjoint).symm
      have hmul : C.q T * layer.card ≤
          (iterativeWindowLayer C.roots C.children (n + 1) T).card := by
        simpa [hbiUnion] using hchildren_sum
      have hpow : C.q T ^ (n + 1) ≤ C.q T * layer.card := by
        calc
          C.q T ^ (n + 1) = C.q T ^ n * C.q T := by simp [pow_succ]
          _ ≤ layer.card * C.q T := Nat.mul_le_mul_right (C.q T) hq
          _ = C.q T * layer.card := by simp [Nat.mul_comm]
      exact hpow.trans hmul

/-- Shared-neighbor counterexample seed: two roots, two common children at every step. -/
def overlappingRoots : ℝ → Finset (Fin 2) := fun _ => Finset.univ

def overlappingChildren (_n : ℕ) (_T : ℝ) (_i : Fin 2) : Finset (Fin 2) :=
  Finset.univ

/-- In the shared-neighbor model, all layers are exactly the two-point universe. -/
theorem overlappingLayer_eq_univ
    (n : ℕ) (T : ℝ) :
    iterativeWindowLayer overlappingRoots overlappingChildren n T = Finset.univ := by
  induction n with
  | zero => simp [iterativeWindowLayer, overlappingRoots]
  | succ n ih =>
      ext i
      simp [iterativeWindowLayer, overlappingChildren, ih]

/-- Local minimum degree alone does not force exponential separation when collisions occur. -/
theorem sharedNeighborModel_not_exponential
    : ¬ ∀ᶠ T in Filter.atTop,
        (2 : ℕ) ^ 2 ≤ (iterativeWindowLayer overlappingRoots overlappingChildren 2 T).card := by
  rw [Filter.not_eventually]
  exact Filter.Frequently.of_forall (fun T =>
    by
      have hcard : (iterativeWindowLayer overlappingRoots overlappingChildren 2 T).card = 2 := by
        simpa [overlappingLayer_eq_univ] using
          (Finset.card_univ : (Finset.univ : Finset (Fin 2)).card = 2)
      simpa [hcard] using (show ¬ ((2 : ℕ) ^ 2 ≤ (2 : ℕ)) by decide))

/--
Auditable overlap-weakening pattern: a disjoint sub-certificate with the same
`q` gives the same `q^n` lower bound when its layer is eventually included in
`C`'s layer at the same depth.
-/
theorem iterativeWindowLayer_qpow_lowerBound_with_subcertificate
    {ι : Type*} [DecidableEq ι]
    (C : IterativeWindowLayerCertificate (ι := ι))
    (C' : IterativeWindowLayerCertificate (ι := ι))
    (n : ℕ) (hn' : n ≤ C'.depth)
    (hqeq : C'.q = C.q)
    (hsubset :
      ∀ᶠ T in Filter.atTop,
        iterativeWindowLayer C'.roots C'.children n T ⊆
          iterativeWindowLayer C.roots C.children n T) :
    ∀ᶠ T in Filter.atTop,
      C.q T ^ n ≤ (iterativeWindowLayer C.roots C.children n T).card := by
  have hqpow' : ∀ᶠ T in Filter.atTop,
      C'.q T ^ n ≤ (iterativeWindowLayer C'.roots C'.children n T).card :=
    iterativeWindowLayer_qpow_lowerBound (C := C') n hn'
  filter_upwards [hqpow', hsubset] with T hq' hsub
  exact (by simpa [hqeq] using hq'.trans (Finset.card_le_card hsub))

/--
Bridge a certified `q^n` lower bound from a layer certificate into the existing
Carlson-depth contradiction theorem.
-/
theorem iterativeWindowLayer_to_carlson_contradiction
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    {realPart ordinate : ρ → ℝ} {sigma H : ℝ}
    (C : IterativeLocalBranchCertificate (ι := ι) (ρ := ρ)
      (realPart := realPart) (ordinate := ordinate) sigma H)
    (n : ℕ)
    (hdepth : n < C.depth)
    (L : IterativeWindowLayerCertificate (ι := ι))
    (hn : n ≤ L.depth)
    (hbranch_le :
      ∀ᶠ T in Filter.atTop,
        (iterativeWindowLayer L.roots L.children n T).card ≤ C.branchCount n T)
    (hσ : 1 / 2 < sigma) (hσ1 : sigma < 1)
    (hlower :
      ∀ᶠ T in Filter.atTop,
        disjointWindowFamilyLowerCount (C.windows n) (C.cluster n)
            (C.windowStart n) realPart ordinate sigma H T ≤
            (ZeroDensity.zeroDensityCount sigma (T + H) : ℝ))
    (hgap :
      Filter.Tendsto
        (fun T =>
          (C.localContribution : ℝ) * (L.q T ^ n) -
            ((Classical.choice (exists_carlsonEventualMajorant hσ hσ1)).C *
              ‖(T + H) ^ (4 * sigma * (1 - sigma)) *
                (Real.log (T + H)) ^ 4‖))
        Filter.atTop Filter.atTop) :
    False := by
  have hbranch : ∀ᶠ T in Filter.atTop, (L.q T ^ n) ≤ C.branchCount n T := by
    have hqpow : ∀ᶠ T in Filter.atTop,
        L.q T ^ n ≤ (iterativeWindowLayer L.roots L.children n T).card :=
      iterativeWindowLayer_qpow_lowerBound (C := L) n hn
    filter_upwards [hqpow, hbranch_le] with T hqpow hLE
    exact hqpow.trans hLE
  exact iterativeBranch_qpow_carlson_contradiction
    (realPart := realPart) (ordinate := ordinate)
    (C := C) n hdepth hσ hσ1 L.q hbranch hlower hgap

end PrimeNumberTheorem
