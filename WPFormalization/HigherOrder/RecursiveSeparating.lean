import WPFormalization.HigherOrder.ProfileLowCore
import WPFormalization.HigherOrder.RecursiveMerger
/-! Exact separating atoms pair the actual component ratio with its prescribed formal ratio.
Finite node sums commute with their real finite truncations without error hypotheses. -/

noncomputable section
namespace WP.HigherOrder
open Set

def separatingAtomValue (P:PsiTheory) (g t:ℕ) (d:List ℕ) (Y:ℝ)
    (j:ℕ) (I:Finset ℕ) (l:ℕ) :ℝ :=
  (W P (g-j) (d.length+1-I.card) Y/W P g (d.length+1) Y)*
    ∑u∈Finset.range (t+l-1),smallW P Y j (u::selectedNat d I)*
      profile P (g-j) ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)) Y

def separatingAtomSeries (P:PsiTheory) (Y:ℝ) (t:ℕ) (d:List ℕ)
    (j:ℕ) (I:Finset ℕ) (l:ℕ) :Series :=
  ratioSeries Y (formalHierarchyJet P Y) (d.length+1) j I.card*
    ∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P Y j (u::selectedNat d I))*
      complexityShift ((2*j+I.card:ℕ):ℝ)
        (formalProfile P Y ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))

lemma separating_atom_remainder_identity (P:PsiTheory) (g t j l L:ℕ)
    (d:List ℕ) (I:Finset ℕ) (Y z:ℝ) :
    separatingAtomValue P g t d Y j I l-truncationValue (separatingAtomSeries P Y t d j I l) L z=
      ∑u∈Finset.range (t+l-1),smallW P Y j (u::selectedNat d I)*
        ((W P (g-j) (d.length+1-I.card) Y/W P g (d.length+1) Y)*
          profile P (g-j) ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)) Y-
          truncationValue (ratioSeries Y (formalHierarchyJet P Y) (d.length+1) j I.card*
            complexityShift ((2*j+I.card:ℕ):ℝ)
              (formalProfile P Y ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))) L z) :=by
  have hs:separatingAtomSeries P Y t d j I l=
      ∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P Y j (u::selectedNat d I))*
        (ratioSeries Y (formalHierarchyJet P Y) (d.length+1) j I.card*
          complexityShift ((2*j+I.card:ℕ):ℝ)
            (formalProfile P Y ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))):=by
    unfold separatingAtomSeries
    rw[Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw[hs,truncationValue_finset_sum]
  simp only[separatingAtomValue,Finset.mul_sum,truncationValue_C_mul,mul_sub,Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  ring
end WP.HigherOrder
