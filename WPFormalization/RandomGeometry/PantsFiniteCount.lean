import Mathlib
noncomputable section
namespace WP.RandomGeometry

/-- Disjoint two-element cusp sets give the true deterministic pants bound.
Only the elementary label combinatorics occurs in this statement. -/
lemma disjoint_pair_card_bound {α : Type*} (s : Finset α) {n : ℕ}
    (labels : α → Finset (Fin n)) (hcard : ∀ γ ∈ s, (labels γ).card = 2)
    (hdisjoint : (s : Set α).PairwiseDisjoint labels) : 2 * s.card ≤ n := by
  classical
  have hc : (s.biUnion labels).card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (s.biUnion labels))
  rw [Finset.card_biUnion hdisjoint, Finset.sum_congr rfl hcard,
    Finset.sum_const_nat (fun _ _ => rfl)] at hc
  simpa only [mul_comm] using hc

/-- Independent ordered slots are retained in the finite fiber decomposition. -/
lemma ordered_label_fiber_card {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (label : α → β) :
    Fintype.card α = ∑ b : β, Fintype.card {a : α // label a = b} := by
  classical
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv label).symm).trans
    Fintype.card_sigma

end WP.RandomGeometry
