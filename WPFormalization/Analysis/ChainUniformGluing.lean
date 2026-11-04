import WPFormalization.Statements.Basic

/-! The finite-genus compactness argument used in the full diagonal chain.
The two estimates below are proof inputs to this elementary gluing lemma;
neither one is licensed as a classical theorem about WP volumes. -/
noncomputable section
namespace WP.Analysis

/-- A bound uniform for large genera and a bound for each fixed genus combine
to a bound uniform over every stable pair of large total complexity. -/
lemma chain_uniform_of_large_genus_and_fixed_genus (E : ℕ → ℕ → ℝ)
    (hlarge : ∀ ε : ℝ, 0 < ε → ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ,
      WP.Stable g n → |E g n| ≤ ε * (2*g+n))
    (hfixed : ∀ g : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      WP.Stable g n → |E g n| ≤ ε * (2*g+n)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g n : ℕ, WP.Stable g n →
      N ≤ 2*g+n → |E g n| ≤ ε * (2*g+n) := by
  intro ε hε
  obtain ⟨G,hG⟩ := hlarge ε hε
  choose N hN using fun g : Fin G => hfixed g.val ε hε
  refine ⟨2*G + Finset.univ.sup N, ?_⟩
  intro g n hst hsize
  by_cases hg : G ≤ g
  · exact hG g hg n hst
  · let i : Fin G := ⟨g,by omega⟩
    have hi : N i ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ i)
    exact hN i n (by omega) hst

end WP.Analysis
