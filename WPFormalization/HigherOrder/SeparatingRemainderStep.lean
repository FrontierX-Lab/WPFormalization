import WPFormalization.HigherOrder.ActualRatioProfileStep
import WPFormalization.HigherOrder.StrictLossConvolution
import WPFormalization.HigherOrder.FiniteLossMajorant
import WPFormalization.HigherOrder.SeparatingCardinalityRemainder
import WPFormalization.HigherOrder.RecursiveSeparating
import WPFormalization.Analysis.NormalizedMomentScale
/-! The actual separating low-loss remainder is controlled by strictly
previous cusp, genus and profile errors. Actual C.14 factorization, bounded
small-component Gamma growth, labeled subset cardinalities, node count,
uniform C.23 moments, and the strict loss convolution are all instantiated.
The edge scale S_L^(2L-1) and minimum separating loss 2 are retained.
This supporting step is paired with the exact weighted original recursion
in RecursiveSeparating/SeparatingRemainderIdentity; it asserts no full C.3
inhabitant by itself. -/
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries

def separatingCardinalityRemainder (P:PsiTheory)(g t L:ℕ)(d:List ℕ)(Y:ℝ)(j s:ℕ):ℝ :=
  ∑'l:ℕ,weight Y l*(∑I∈Finset.powersetCard s (Finset.range d.length),
    (separatingAtomValue P g t d Y j I l-truncationValue (separatingAtomSeries P Y t d j I l) L (1/(complexity g (d.length+1):ℝ))))

lemma separating_fixed_loss_uniform_remainder_step (P:PsiTheory) :
    ∃C D B:ℝ,∃M₀:ℕ,0<C ∧ 0<D ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g t L:ℕ,∀d:List ℕ,Stable g (d.length+1)→1 ≤ L→
    profileOrderWeight (M:ℝ) L (t::d)^2/(complexity g (d.length+1):ℝ)<1→
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
    ∀j s:ℕ,s ≤ d.length→Stable j (s+1)→2 ≤ 2*j+s→2*j+s<L→
    |separatingCardinalityRemainder P g t L d Y j s| ≤
      C*D^(2*j+s)*profileOrderWeight (M:ℝ) L (t::d)^(2*L-1)/(complexity g (d.length+1):ℝ)^L*
        ((∑i∈Finset.range (L-(2*j+s)),B^i*(EC (L-(2*j+s)-i)+EG (L-(2*j+s)-i)+EP (L-(2*j+s)-i)))+
          B^(L-(2*j+s))) := by
  obtain ⟨D,B,Mp,hD,hB,hMp,hcompound⟩:=actual_large_component_profile_previous_step P
  obtain ⟨T₀,hT₀,hcard⟩:=separating_cardinality_remainder_bound P
  obtain ⟨Cm,Mm,hCm,hMm,hmoment⟩:=Analysis.canonical_growing_order_scale_bounds
  let M₀:=max Mp ⌈Mm⌉₊
  have hM₀:2 ≤ M₀:=hMp.trans (le_max_left _ _)
  have hT₀pos:0<T₀:=by linarith
  refine ⟨Cm,T₀*D,B,M₀,hCm,by positivity,hB,hM₀,?_⟩
  intro M hM g t L d hstable hL hsmall Y hY EC EG EP hEC hEG hEP hcusp hgenus hprofile j s hs hjs hr2 hr
  let p:=d.length+1
  let S:=profileOrderWeight (M:ℝ) L (t::d)
  let h:ℝ:=complexity g p
  let r:=2*j+s
  let q:=L-r
  let E:=((∑i∈Finset.range q,B^i*(EC (q-i)+EG (q-i)+EP (q-i)))+B^q)
  let R:Finset ℕ→ℕ→ℕ→ℝ:=fun I l u=>
    (W P (g-j) (p-s) Y/W P g p Y)*profile P (g-j) ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)) Y-
      truncationValue (ratioSeries Y (formalHierarchyJet P Y) p j s*
        complexityShift (r:ℝ) (formalProfile P Y ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))) L (1/h)
  have hMpM:Mp ≤ M:=(le_max_left _ _).trans hM
  have hMmM:Mm ≤ (M:ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast (le_max_right Mp ⌈Mm⌉₊).trans hM)
  have hM2:(2:ℝ) ≤ M:=by exact_mod_cast hM₀.trans hM
  have hM0:0 ≤ (M:ℝ):=by linarith
  have hMmul:=mul_le_mul_of_nonneg_right hM2 (Nat.cast_nonneg L : (0:ℝ) ≤ L)
  have hSbound:(p:ℝ)+2*L ≤ S:=by
    dsimp[S,p,profileOrderWeight]
    simp only[List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith[Nat.cast_nonneg (α:=ℝ) (t::d).sum]
  have hp:1 ≤ p:=by dsimp[p];omega
  have hS:1 ≤ S:=by
    have hpr:(1:ℝ) ≤ p:=by exact_mod_cast hp
    have :=Nat.cast_nonneg (α:=ℝ) L
    linarith
  have hS0:0 ≤ S:=by linarith
  have hh:0<h:=by
    dsimp[h,p]
    have hn:0<complexity g (d.length+1):=by unfold complexity Stable at *;omega
    exact_mod_cast hn
  have hlabel:((d.length+r:ℕ):ℝ) ≤ S:=by
    have hn:d.length+r ≤ p+2*L:=by dsimp[p,r];omega
    exact (show ((d.length+r:ℕ):ℝ) ≤ (p:ℝ)+2*L by exact_mod_cast hn).trans hSbound
  have ht:(t:ℝ) ≤ S:=by
    have hn:t ≤ (t::d).sum:=by simp only[List.sum_cons];omega
    have hb:=profileOrderWeight_base_le (M:ℝ) hM0 L (t::d)
    have hnr:(t:ℝ) ≤ ((t::d).sum:ℝ):=by exact_mod_cast hn
    linarith[Nat.cast_nonneg (α:=ℝ) (t::d).length]
  have hE:0 ≤ E:=by
    dsimp[E]
    apply add_nonneg
    · exact Finset.sum_nonneg (fun i hi=>mul_nonneg (by positivity) (add_nonneg (add_nonneg (hEC _) (hEG _)) (hEP _)))
    · positivity
  have hv:=small_weight_split_child_valid g p j s L S hp hL hstable hSbound hsmall hr.le (by dsimp[p];omega)
  have hscalar:scalarOrderWeight (M:ℝ) L p ≤ S:=by
    dsimp[scalarOrderWeight,S,p,profileOrderWeight]
    simp only[List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith[Nat.cast_nonneg (α:=ℝ) (t::d).sum]
  have hpoint(I:Finset ℕ)(hI:I∈Finset.powersetCard s (Finset.range d.length))(l u:ℕ)(hu:u∈Finset.range (t+l-1)):
      |R I l u| ≤ D^r*(S+l+1)^(2*q)/h^L*E:=by
    have hsub:=(Finset.mem_powersetCard.mp hI).1
    have hcardI:=(Finset.mem_powersetCard.mp hI).2
    have hc:(Finset.range d.length)\I⊆Finset.range d.length:=Finset.sdiff_subset
    have hlen:((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)).length=p-s:=by
      rw[List.length_cons,selectedNat_cardinality_length d _ hc,Finset.card_sdiff_of_subset hsub,Finset.card_range,hcardI]
      dsimp[p]
      omega
    have hweight:profileOrderWeight (M:ℝ) q ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)) ≤ S+l+1:=by
      have hb:=separating_order_weight (M:ℝ) hM0 q L t l u d ((Finset.range d.length)\I) (by dsimp[q,r];omega) (Finset.mem_range.mp hu)
      dsimp[S] at *
      linarith
    exact hcompound M hMpM g p j s L hv.1 (by dsimp[p];omega) hv.2 (by omega) hr _ hlen S (S+l+1)
      hscalar (by have :=Nat.cast_nonneg (α:=ℝ) l;linarith) hsmall.le hweight Y hY EC EG EP hEC hEG hEP hcusp hgenus hprofile
  have hm:=hmoment (M:ℝ) hMmM L (t::d).sum (t::d).length (2*q+1) (by simp) (by dsimp[q,r];omega) Y hY
  have hws:Summable (fun l:ℕ=>(S+l+1)^(2*q+1)*|weight Y l|):=hm.1
  have hwb:(∑'l:ℕ,(S+l+1)^(2*q+1)*|weight Y l|) ≤ Cm*S^(2*q+1):=hm.2.2.1
  have hb:= (hcard L j s t d hjs hr2 hr S h D E Cm hS hh hD.le hE hCm.le hlabel ht Y hY R hpoint hws hwb).2
  have heq:(∑'l:ℕ,weight Y l*(∑I∈Finset.powersetCard s (Finset.range d.length),
      ∑u∈Finset.range (t+l-1),smallW P Y j (u::selectedNat d I)*R I l u))=
      separatingCardinalityRemainder P g t L d Y j s:=by
    apply tsum_congr
    intro l
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    rw[separating_atom_remainder_identity]
    have hcardI:=(Finset.mem_powersetCard.mp hI).2
    simp only[hcardI]
    rfl
  rw[heq] at hb
  exact hb

lemma finite_loss_rectangular_sum_bound (a L n:ℕ)(hL:1 ≤ L)(F:ℕ→ℝ)(hF:∀r,0 ≤ F r) :
    (∑j∈Finset.range L,∑s∈Finset.range n,
      if a ≤ 2*j+s ∧ 2*j+s<L then F (2*j+s) else 0) ≤
    ∑r∈Finset.range L,if a ≤ r then (2:ℝ)^r*F r else 0 := by
  have hcrop(j:ℕ):
      (∑s∈Finset.range n,if a ≤ 2*j+s ∧ 2*j+s<L then F (2*j+s) else 0) ≤
      ∑s∈Finset.range L,if a ≤ 2*j+s ∧ 2*j+s<L then F (2*j+s) else 0 := by
    by_cases hn:n ≤ L
    · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      intro s hs hnot
      split_ifs
      · exact hF _
      · exact le_rfl
    · apply le_of_eq
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega:L ≤ n))
      intro s hs hnot
      have hsL:L ≤ s:=by simpa only[Finset.mem_range,not_lt] using hnot
      rw[ite_eq_right (by omega:¬(a ≤ 2*j+s ∧ 2*j+s<L))]
  apply (Finset.sum_le_sum (fun j hj=>hcrop j)).trans
  have he:L-1+1=L:=by omega
  have hf:=loss_pair_count_bound a (L-1) F hF
  simpa only[he,show ∀j s:ℕ,(a ≤ 2*j+s ∧ 2*j+s ≤ L-1)↔(a ≤ 2*j+s ∧ 2*j+s<L) from fun j s=>by omega] using hf

def separatingLowRemainder (P:PsiTheory)(g t L:ℕ)(d:List ℕ)(Y:ℝ):ℝ :=
  ∑j∈Finset.range L,∑s∈Finset.range (d.length+1),
    if Stable j (s+1) ∧ 2 ≤ 2*j+s ∧ 2*j+s<L then
      separatingCardinalityRemainder P g t L d Y j s else 0

lemma separating_low_uniform_remainder_step (P:PsiTheory) :
    ∃C B:ℝ,∃M₀:ℕ,0<C ∧ 0<B ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    ∀g t L:ℕ,∀d:List ℕ,Stable g (d.length+1)→1 ≤ L→
    profileOrderWeight (M:ℝ) L (t::d)^2/(complexity g (d.length+1):ℝ)<1→
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
    |separatingLowRemainder P g t L d Y| ≤
      C*profileOrderWeight (M:ℝ) L (t::d)^(2*L-1)/(complexity g (d.length+1):ℝ)^L*
        ((∑k∈Finset.range L,if 2 ≤ k then B^k*(EC (L-k)+EG (L-k)+EP (L-k)) else 0)+B^L) := by
  obtain ⟨C,D,B,M₀,hC,hD,hB,hM₀,hstep⟩:=separating_fixed_loss_uniform_remainder_step P
  let B':=2*max (2*D) B
  have hB':0<B':=by
    dsimp[B']
    have hb:0 < max (2*D) B:=lt_of_lt_of_le hB (le_max_right _ _)
    positivity
  refine ⟨C,B',M₀,hC,hB',hM₀,?_⟩
  intro M hM g t L d hstable hL hsmall Y hY EC EG EP hEC hEG hEP hcusp hgenus hprofile
  let S:=profileOrderWeight (M:ℝ) L (t::d)
  let h:ℝ:=complexity g (d.length+1)
  let E:ℕ→ℝ:=fun q=>EC q+EG q+EP q
  let F:ℕ→ℝ:=fun r=>D^r*((∑i∈Finset.range (L-r),B^i*E (L-r-i))+B^(L-r))
  let K:=C*S^(2*L-1)/h^L
  have hM0:0 ≤ (M:ℝ):=Nat.cast_nonneg _
  have hS0:0 ≤ S:=by dsimp[S,profileOrderWeight];positivity
  have hh:0<h:=by
    dsimp[h]
    have hn:0<complexity g (d.length+1):=by unfold complexity Stable at *;omega
    exact_mod_cast hn
  have hK:0 ≤ K:=by dsimp[K];positivity
  have hE:∀q,0 ≤ E q:=by intro q;exact add_nonneg (add_nonneg (hEC q) (hEG q)) (hEP q)
  have hF:∀r,0 ≤ F r:=by
    intro r
    dsimp[F]
    exact mul_nonneg (pow_nonneg hD.le _) (add_nonneg
      (Finset.sum_nonneg (fun i hi=>mul_nonneg (pow_nonneg hB.le _) (hE _))) (pow_nonneg hB.le _))
  have hb:|separatingLowRemainder P g t L d Y| ≤
      K*(∑j∈Finset.range L,∑s∈Finset.range (d.length+1),
        if 2 ≤ 2*j+s ∧ 2*j+s<L then F (2*j+s) else 0):=by
    dsimp[separatingLowRemainder]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw[Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw[Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hs':s ≤ d.length:=by have :=Finset.mem_range.mp hs;omega
    by_cases ht:Stable j (s+1) ∧ 2 ≤ 2*j+s ∧ 2*j+s<L
    · rw[ite_eq_left ht,ite_eq_left ht.2]
      have hb:=hstep M hM g t L d hstable hL hsmall Y hY EC EG EP hEC hEG hEP hcusp hgenus hprofile j s hs' ht.1 ht.2.1 ht.2.2
      convert hb using 1 <;>dsimp[K,F,E,S,h]<;>ring
    · rw[ite_eq_right ht,abs_zero]
      apply mul_nonneg hK
      split_ifs
      · exact hF _
      · exact le_rfl
  apply hb.trans
  have hrect:=finite_loss_rectangular_sum_bound 2 L (d.length+1) hL F hF
  have hrect':K*(∑j∈Finset.range L,∑s∈Finset.range (d.length+1),if 2 ≤ 2*j+s ∧ 2*j+s<L then F (2*j+s) else 0) ≤
      K*(∑r∈Finset.range L,if 2 ≤ r then (2*D)^r*((∑i∈Finset.range (L-r),B^i*E (L-r-i))+B^(L-r)) else 0):=by
    have ht:=mul_le_mul_of_nonneg_left hrect hK
    convert ht using 1
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    split_ifs
    · dsimp[F]
      rw[mul_pow]
      ring
    · rfl
  apply hrect'.trans
  have hconv:=finite_strict_loss_geometric_convolution (2*D) B (by positivity) hB.le 2 L E hE
  have ht:=mul_le_mul_of_nonneg_left hconv hK
  exact ht

end WP.HigherOrder
