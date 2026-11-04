import WPFormalization.HigherOrder.SeparatingCompleteRemainderStep
import WPFormalization.HigherOrder.SeparatingSourceDecomposition
/-! The actual original finite-deficit separating source has the full
uniform strict-loss remainder row. This is the original half-sum over all
genus splits, labeled subsets, and node degrees, paired with the actual
canonical C.16 truncation. The exact finite source decomposition eliminates
the temporary weighted low/central representation from its public type. -/
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries
lemma recursiveSeparating_finite_source_uniform_remainder_step (P:PsiTheory) :
    ∃C B δ₀:ℝ,∃M₀:ℕ,0<C ∧ 0<B ∧ 0<δ₀ ∧ δ₀ ≤ 1 ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g t L:ℕ,∀d:List ℕ,Stable g (d.length+1)→2 ≤ L→
    profileOrderWeight (M:ℝ) L (t::d)^2/(complexity g (d.length+1):ℝ)<δ₀→
    ∀Y∈Icc (0:ℝ) y₀,∀EC EG EP:ℕ→ℝ,
    (∀m,0 ≤ EC m)→(∀m,0 ≤ EG m)→(∀m,0 ≤ EP m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |cuspCorrection P g' p' Y-truncationValue (formalCusp P Y p') m (1/(complexity g' p':ℝ))| ≤
        EC m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    (∀g' p' m:ℕ,1 ≤ p'→Stable g' p'→1 ≤ m→m<L→
      |genusCorrection P g' p' Y-truncationValue (formalGenus P Y p') m (1/(complexity g' p':ℝ))| ≤
        EG m*scalarOrderWeight (M:ℝ) m p'^(2*m)/(complexity g' p':ℝ)^m)→
    (∀g':ℕ,∀d':List ℕ,1 ≤ d'.length→Stable g' d'.length→∀m:ℕ,1 ≤ m→m<L→
      |profile P g' d' Y-truncationValue (formalProfile P Y d') m (1/(complexity g' d'.length:ℝ))| ≤
        EP m*profileOrderWeight (M:ℝ) m d'^(2*m)/(complexity g' d'.length:ℝ)^m)→
    |(∑l∈Finset.range (deficit g (t::d)+1),weight Y l*
        ((1/2:ℝ)*(∑u∈Finset.range (t+l-1),∑j∈Finset.range (g+1),
          ∑I∈(Finset.range d.length).powerset,secondSeparatingTerm P g (t+l) d u j I Y)))-
      truncationValue (separatingSeries P Y (formalHierarchyJet P Y) (L-1) t d) L (1/(complexity g (d.length+1):ℝ))| ≤
      C*profileOrderWeight (M:ℝ) L (t::d)^(2*L-1)/(complexity g (d.length+1):ℝ)^L*
        ((∑k∈Finset.range L,if 2 ≤ k then B^k*(EC (L-k)+EG (L-k)+EP (L-k)) else 0)+B^L) := by
  obtain ⟨C,B,δ₀,M₀,hC,hB,hδ₀,hδ1,hM₀,hstep⟩:=recursiveSeparating_uniform_remainder_step P
  refine ⟨C,B,δ₀,M₀,hC,hB,hδ₀,hδ1,hM₀,?_⟩
  intro M hM g t L d hs hL hsmall Y hY EC EG EP hEC hEG hEP hcusp hgenus hprofile
  let S:=profileOrderWeight (M:ℝ) L (t::d)
  have hM2:(2:ℝ) ≤ M:=by exact_mod_cast hM₀.trans hM
  have hS:((d.length+1:ℕ):ℝ)+2*L ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hM2 (Nat.cast_nonneg L : (0:ℝ) ≤ L)
    dsimp[S,profileOrderWeight]
    simp only[List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith[Nat.cast_nonneg (α:=ℝ) (t::d).sum]
  rw[recursiveSeparating_full_source_prefix P g t L d hL Y hY S hs hS (hsmall.trans_le hδ1)]
  exact hstep M hM g t L d hs hL hsmall Y hY EC EG EP hEC hEG hEP hcusp hgenus hprofile

end WP.HigherOrder
