import WPFormalization.HigherOrder.SeparatingSourceSupport
/-! Exact decomposition of the original finite separating source.
One low orientation and the central double-loss tail recover the original half-sum.
All infinite terms equal their original finite deficit prefixes. -/

noncomputable section
namespace WP.HigherOrder
open Set
lemma recursiveSeparating_full_source_prefix (P:PsiTheory) (g t L:ℕ)
    (d:List ℕ) (hL:2 ≤ L) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) (S:ℝ)
    (hs:Stable g (d.length+1)) (hS:((d.length+1:ℕ):ℝ)+2*L ≤ S)
    (hsmall:S^2/(complexity g (d.length+1):ℝ)<1) :
    (∑l∈Finset.range (deficit g (t::d)+1),weight Y l*
      ((1/2:ℝ)*(∑u∈Finset.range (t+l-1),∑j∈Finset.range (g+1),
        ∑I∈(Finset.range d.length).powerset,secondSeparatingTerm P g (t+l) d u j I Y)))=
      recursiveSeparatingWeightedLow P g t L d Y+
        ∑'l:ℕ,weight Y l*(recursiveSeparatingTail P g (t+l) L d Y/2):=by
  have hgL:=small_weight_parent_genus_large g (d.length+1) L S (by omega) (by omega) hs hS hsmall
  have hsep:2*L ≤ 2*g+d.length:=by omega
  rw[recursiveSeparatingWeightedLow_finite_prefix P g t L d (by omega) Y hY S hs hS hsmall,
    (recursiveSeparatingTail_weighted_prefix_hasSum P g t L d hL Y hY).tsum_eq,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw[recursiveSeparating_orientation_decomposition P g (t+l) L d hsep Y]
  ring
end WP.HigherOrder
