import WPFormalization.Intersection.CriticalHomogeneity
import WPFormalization.Analysis.KKernelPositivity
import WPFormalization.Analysis.ThetaNonnegative
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
/-! Positive finite kernel polynomials for the actual shifted amplitudes.
The true positive recursion supplies nonnegative NNReal coefficients,
complexity homogeneity and weighted deficit homogeneity. Signed, unstable
and excess states are retained as zero. Weighted rescaling identifies both
the regularized a^h amplitude and the unrescaled K-inverse variables; no
positivity or convolution factorization is assumed. -/
noncomputable section
namespace WP.PositiveConvolution
abbrev KernelPolynomial := MvPolynomial ℕ NNReal
abbrev totalWeight : ℕ→ℕ:=fun _=>1
abbrev kernelWeight : ℕ→ℤ:=fun l=>(l:ℤ)
def BiHomogeneous (F:KernelPolynomial) (h:ℕ) (m:ℤ):Prop :=
  F.IsWeightedHomogeneous totalWeight h ∧ F.IsWeightedHomogeneous kernelWeight m
abbrev evalKernel (v:ℕ→ℝ) : KernelPolynomial→+*ℝ := MvPolynomial.eval₂Hom NNReal.toRealHom v
lemma BiHomogeneous.zero (h:ℕ) (m:ℤ):BiHomogeneous 0 h m:=by
  exact ⟨MvPolynomial.isWeightedHomogeneous_zero NNReal totalWeight h,MvPolynomial.isWeightedHomogeneous_zero NNReal kernelWeight m⟩
lemma BiHomogeneous.X (l:ℕ):BiHomogeneous (MvPolynomial.X l) 1 (l:ℤ):=by
  exact ⟨MvPolynomial.isWeightedHomogeneous_X _ _ _,MvPolynomial.isWeightedHomogeneous_X _ _ _⟩
lemma BiHomogeneous.C_mul {F:KernelPolynomial} {h:ℕ} {m:ℤ}
    (hF:BiHomogeneous F h m) (c:NNReal):BiHomogeneous (MvPolynomial.C c*F) h m:=
  ⟨hF.1.C_mul c,hF.2.C_mul c⟩
lemma BiHomogeneous.add {F G:KernelPolynomial} {h:ℕ} {m:ℤ}
    (hF:BiHomogeneous F h m) (hG:BiHomogeneous G h m):BiHomogeneous (F+G) h m:=
  ⟨hF.1.add hG.1,hF.2.add hG.2⟩
lemma BiHomogeneous.mul {F G:KernelPolynomial} {h k:ℕ} {m n:ℤ}
    (hF:BiHomogeneous F h m) (hG:BiHomogeneous G k n):BiHomogeneous (F*G) (h+k) (m+n):=
  ⟨hF.1.mul hG.1,hF.2.mul hG.2⟩
lemma BiHomogeneous.sum {ι:Type*} (s:Finset ι) (F:ι→KernelPolynomial) (h:ℕ) (m:ℤ)
    (hF:∀i∈s,BiHomogeneous (F i) h m):BiHomogeneous (∑i∈s,F i) h m:=by
  exact ⟨MvPolynomial.IsWeightedHomogeneous.sum s F h (fun i hi=>(hF i hi).1),
    MvPolynomial.IsWeightedHomogeneous.sum s F m (fun i hi=>(hF i hi).2)⟩
lemma BiHomogeneous.top (c:NNReal) (h:ℕ):BiHomogeneous (MvPolynomial.C c*MvPolynomial.X 0^h) h 0:=by
  have hX:=BiHomogeneous.X 0
  have hp:BiHomogeneous (MvPolynomial.X 0^h) h 0:=by
    constructor
    · simpa [nsmul_eq_mul,totalWeight] using hX.1.pow h
    · simpa [kernelWeight] using hX.2.pow h
  exact hp.C_mul c
lemma evalKernel_nonneg (F:KernelPolynomial) (v:ℕ→ℝ) (hv:∀l,0 ≤ v l):
    0 ≤ evalKernel v F:=by
  change 0 ≤ MvPolynomial.eval₂ NNReal.toRealHom v F
  rw[MvPolynomial.eval₂_eq]
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (NNReal.coe_nonneg _) (Finset.prod_nonneg (fun i hi=>pow_nonneg (hv i) _))
lemma mapped_coefficient_nonneg (F:KernelPolynomial) (d:ℕ→₀ℕ):
    0 ≤ (MvPolynomial.map NNReal.toRealHom F).coeff d:=by
  rw[MvPolynomial.coeff_map]
  exact NNReal.coe_nonneg _
def signedDeficit (g:ℕ) (d:List ℤ):ℤ:=3*(g:ℤ)-3+d.length-d.sum

def SignedRepresentation (P:PsiTheory) (g:ℕ) (d:List ℤ) (F:KernelPolynomial):Prop:=
  BiHomogeneous F (complexity g d.length) (signedDeficit g d) ∧
    ∀Y∈Set.Icc (0:ℝ) y₀,evalKernel (theta Y) F=piSigned P g d Y
end WP.PositiveConvolution

namespace WP.PositiveConvolution
open Set

def childrenPolynomial (F:ℕ→List ℤ→KernelPolynomial) (g p:ℕ) (d:List ℤ):KernelPolynomial:=
  (∑j∈Finset.range d.length,MvPolynomial.C (2*(d[j]!.toNat:NNReal)+1)*
    F g (((p:ℤ)+d[j]!-1)::d.eraseIdx j))+
  (if g=0 then 0 else MvPolynomial.C (1/2:NNReal)*∑u∈Finset.range (p-1),
    F (g-1) ((u:ℤ)::((p:ℤ)-2-u)::d))+
  MvPolynomial.C (1/2:NNReal)*∑u∈Finset.range (p-1),∑g₁∈Finset.range (g+1),
    ∑I∈(Finset.range d.length).powerset,
      if Stable g₁ (selected d I).length.succ ∧
        Stable (g-g₁) (selected d ((Finset.range d.length)\I)).length.succ then
        F g₁ ((u:ℤ)::selected d I)*F (g-g₁) (((p:ℤ)-2-u)::selected d ((Finset.range d.length)\I))
      else 0

lemma childrenPolynomial_bihomogeneous (P:PsiTheory) (F:ℕ→List ℤ→KernelPolynomial)
    (g p h:ℕ) (d:List ℤ) (hh:2 ≤ h) (he:complexity g (d.length+1)=h)
    (hF:∀g':ℕ,∀c:List ℤ,1 ≤ c.length→complexity g' c.length<h→SignedRepresentation P g' c (F g' c)) :
    BiHomogeneous (childrenPolynomial F g p d) (h-1) (signedDeficit g ((p:ℤ)::d)):=by
  unfold childrenPolynomial
  apply BiHomogeneous.add
  · apply BiHomogeneous.add
    · apply BiHomogeneous.sum
      intro j hj
      have hj':j<d.length:=Finset.mem_range.mp hj
      let c:=((p:ℤ)+d[j]!-1)::d.eraseIdx j
      have hc:complexity g c.length=h-1:=by
        dsimp[c]
        simp only[List.length_cons,List.length_eraseIdx_of_lt hj']
        unfold complexity at *
        omega
      have hw:signedDeficit g c=signedDeficit g ((p:ℤ)::d):=by
        have hs:d[j]!+(d.eraseIdx j).sum=d.sum:=by
          simpa [hj'] using (List.getElem_cons_eraseIdx_perm hj').sum_eq
        have hl:((d.eraseIdx j).length:ℤ)+1=(d.length:ℤ):=by
          have hn:(d.eraseIdx j).length+1=d.length:=by rw[List.length_eraseIdx_of_lt hj'];omega
          exact_mod_cast hn
        dsimp[c,signedDeficit]
        try simp only[List.length_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
        omega
      have hb:=(hF g c (by simp[c]) (by omega)).1
      rw[hc,hw] at hb
      exact hb.C_mul _
    · split_ifs with hg
      · exact BiHomogeneous.zero _ _
      · apply BiHomogeneous.C_mul
        apply BiHomogeneous.sum
        intro u hu
        let c:List ℤ:=(u:ℤ)::((p:ℤ)-2-u)::d
        have hc:complexity (g-1) c.length=h-1:=by
          dsimp[c]
          try simp only[List.length_cons]
          unfold complexity at *
          omega
        have hw:signedDeficit (g-1) c=signedDeficit g ((p:ℤ)::d):=by
          dsimp[c,signedDeficit]
          try simp only[List.length_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
          omega
        have hb:=(hF (g-1) c (by simp[c]) (by omega)).1
        rw[hc,hw] at hb
        exact hb
  · apply BiHomogeneous.C_mul
    apply BiHomogeneous.sum
    intro u hu
    apply BiHomogeneous.sum
    intro g₁ hg₁
    apply BiHomogeneous.sum
    intro I hI
    split_ifs with hstable
    · let c₁:List ℤ:=(u:ℤ)::selected d I
      let c₂:List ℤ:=((p:ℤ)-2-u)::selected d ((Finset.range d.length)\I)
      have hs₁:Stable g₁ c₁.length:=hstable.1
      have hs₂:Stable (g-g₁) c₂.length:=hstable.2
      have hgg:g₁ ≤ g:=by have ht:=Finset.mem_range.mp hg₁;omega
      have hpart:=selected_partition_length d I
      have hc₁:complexity g₁ c₁.length<h:=by
        dsimp[c₁,c₂] at hs₁ hs₂ ⊢
        simp only[Stable,List.length_cons] at hs₁ hs₂ ⊢
        unfold complexity at *
        omega
      have hc₂:complexity (g-g₁) c₂.length<h:=by
        dsimp[c₁,c₂] at hs₁ hs₂ ⊢
        simp only[Stable,List.length_cons] at hs₁ hs₂ ⊢
        unfold complexity at *
        omega
      have hcs:complexity g₁ c₁.length+complexity (g-g₁) c₂.length=h-1:=by
        dsimp[c₁,c₂] at hs₁ hs₂ ⊢
        simp only[Stable,List.length_cons] at hs₁ hs₂ ⊢
        unfold complexity at *
        omega
      have hws:signedDeficit g₁ c₁+signedDeficit (g-g₁) c₂=signedDeficit g ((p:ℤ)::d):=by
        have hsum:=selected_partition_sum d I
        have hlen:((selected d I).length:ℤ)+((selected d ((Finset.range d.length)\I)).length:ℤ)=(d.length:ℤ):=by exact_mod_cast hpart
        dsimp[c₁,c₂,signedDeficit]
        try simp only[List.length_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
        omega
      have hb₁:=(hF g₁ c₁ (by simp[c₁]) hc₁).1
      have hb₂:=(hF (g-g₁) c₂ (by simp[c₂]) hc₂).1
      have hb:=hb₁.mul hb₂
      rw[hcs,hws] at hb
      exact hb
    · exact BiHomogeneous.zero _ _
end WP.PositiveConvolution

namespace WP.PositiveConvolution
open Set
@[simp] lemma evalKernel_C (v:ℕ→ℝ) (c:NNReal):evalKernel v (MvPolynomial.C c)=(c:ℝ):=by
  simp[evalKernel]
@[simp] lemma evalKernel_X (v:ℕ→ℝ) (l:ℕ):evalKernel v (MvPolynomial.X l)=v l:=by
  simp[evalKernel]
lemma childrenPolynomial_eval (P:PsiTheory) (F:ℕ→List ℤ→KernelPolynomial)
    (g p h:ℕ) (d:List ℤ) (hh:2 ≤ h) (he:complexity g (d.length+1)=h)
    (hd:∀k∈d,0 ≤ k)
    (hF:∀g':ℕ,∀c:List ℤ,1 ≤ c.length→complexity g' c.length<h→SignedRepresentation P g' c (F g' c))
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀):
    evalKernel (theta Y) (childrenPolynomial F g p d)=normalizedChildren P g p d Y:=by
  simp only[childrenPolynomial,map_add,map_sum,map_mul,evalKernel_C]
  unfold normalizedChildren
  apply congrArg₂ (fun a b:ℝ=>a+b)
  · apply congrArg₂ (fun a b:ℝ=>a+b)
    · apply Finset.sum_congr rfl
      intro j hj
      have hj':j<d.length:=Finset.mem_range.mp hj
      let c:=((p:ℤ)+d[j]!-1)::d.eraseIdx j
      have hc:complexity g c.length=h-1:=by
        dsimp[c]
        simp only[List.length_eraseIdx_of_lt hj']
        unfold complexity at *
        omega
      have hb:=(hF g c (by simp[c]) (by omega)).2 Y hY
      have hdc:0 ≤ d[j]!:=by
        apply hd _
        simpa [hj'] using List.getElem_mem (l:=d) hj'
      have hcast:(d[j]!.toNat:ℤ)=d[j]!:=Int.toNat_of_nonneg hdc
      have hcastR:(d[j]!.toNat:ℝ)=(d[j]!:ℝ):=by exact_mod_cast hcast
      rw[hb]
      change (↑(2*(d[j]!.toNat:NNReal)+1):ℝ)*piSigned P g c Y=_
      simp only[NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast,hcastR]
      rfl
    · split_ifs with hg
      · simp only[map_zero]
      · rw[map_mul,evalKernel_C,map_sum]
        have hhalf:((1/2:NNReal):ℝ)=(1/2:ℝ):=by norm_num
        rw[hhalf]
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        let c:List ℤ:=(u:ℤ)::((p:ℤ)-2-u)::d
        have hc:complexity (g-1) c.length=h-1:=by
          dsimp[c]
          unfold complexity at *
          omega
        exact (hF (g-1) c (by simp[c]) (by omega)).2 Y hY
  · have hhalf:((1/2:NNReal):ℝ)=(1/2:ℝ):=by norm_num
    rw[hhalf]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro g₁ hg₁
    apply Finset.sum_congr rfl
    intro I hI
    let c₁:List ℤ:=(u:ℤ)::selected d I
    let c₂:List ℤ:=((p:ℤ)-2-u)::selected d ((Finset.range d.length)\I)
    change evalKernel (theta Y) (if Stable g₁ c₁.length ∧ Stable (g-g₁) c₂.length then F g₁ c₁*F (g-g₁) c₂ else 0)=
      piSigned P g₁ c₁ Y*piSigned P (g-g₁) c₂ Y
    by_cases hs₁:Stable g₁ c₁.length
    · by_cases hs₂:Stable (g-g₁) c₂.length
      · rw[if_pos ⟨hs₁,hs₂⟩,map_mul]
        have hgg:g₁ ≤ g:=by have ht:=Finset.mem_range.mp hg₁;omega
        have hpart:=selected_partition_length d I
        have hc₁:complexity g₁ c₁.length<h:=by
          dsimp[c₁,c₂] at hs₁ hs₂ ⊢
          simp only[Stable] at hs₁ hs₂
          unfold complexity at *
          omega
        have hc₂:complexity (g-g₁) c₂.length<h:=by
          dsimp[c₁,c₂] at hs₁ hs₂ ⊢
          simp only[Stable] at hs₁ hs₂
          unfold complexity at *
          omega
        rw[(hF g₁ c₁ (by simp[c₁]) hc₁).2 Y hY,(hF (g-g₁) c₂ (by simp[c₂]) hc₂).2 Y hY]
      · rw[if_neg (by tauto),map_zero,piSigned_unstable P _ _ Y hs₂,mul_zero]
    · rw[if_neg (by tauto),map_zero,piSigned_unstable P _ _ Y hs₁,zero_mul]
end WP.PositiveConvolution

namespace WP.PositiveConvolution
open Set

def recursionPolynomial (F:ℕ→List ℤ→KernelPolynomial) (g p:ℕ) (d:List ℕ):KernelPolynomial:=
  ∑l∈Finset.range (deficit g (p::d)+1),MvPolynomial.X l*childrenPolynomial F g (p+l) (d.map Int.ofNat)
lemma recursionPolynomial_bihomogeneous (P:PsiTheory) (F:ℕ→List ℤ→KernelPolynomial)
    (g p h:ℕ) (d:List ℕ) (hh:2 ≤ h) (he:complexity g (d.length+1)=h)
    (hF:∀g':ℕ,∀c:List ℤ,1 ≤ c.length→complexity g' c.length<h→SignedRepresentation P g' c (F g' c)) :
    BiHomogeneous (recursionPolynomial F g p d) h (signedDeficit g ((p:ℤ)::d.map Int.ofNat)):=by
  unfold recursionPolynomial
  apply BiHomogeneous.sum
  intro l hl
  have hb:=childrenPolynomial_bihomogeneous P F g (p+l) h (d.map Int.ofNat) hh (by simpa only[List.length_map] using he) hF
  have ha:=BiHomogeneous.X l
  have hprod:=ha.mul hb
  have hdeg:1+(h-1)=h:=by omega
  have hw:(l:ℤ)+signedDeficit g (((p+l:ℕ):ℤ)::d.map Int.ofNat)=signedDeficit g ((p:ℤ)::d.map Int.ofNat):=by
    dsimp[signedDeficit]
    push_cast
    ring
  simpa only[hdeg,hw] using hprod
lemma recursionPolynomial_eval (P:PsiTheory) (F:ℕ→List ℤ→KernelPolynomial)
    (g p h:ℕ) (d:List ℕ) (hh:2 ≤ h) (he:complexity g (d.length+1)=h)
    (hd:(p::d).sum ≤ dimension g (d.length+1))
    (hF:∀g':ℕ,∀c:List ℤ,1 ≤ c.length→complexity g' c.length<h→SignedRepresentation P g' c (F g' c))
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀):
    evalKernel (theta Y) (recursionPolynomial F g p d)=normalized P g (p::d) Y:=by
  rw[normalized_positive_convolution P g p d Y (by omega) hd hY]
  simp only[recursionPolynomial,map_sum,map_mul,evalKernel_X]
  apply Finset.sum_congr rfl
  intro l hl
  rw[childrenPolynomial_eval P F g (p+l) h (d.map Int.ofNat) hh (by simpa only[List.length_map] using he)
    (by intro k hk;obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hk;exact Int.natCast_nonneg _) hF Y hY]
end WP.PositiveConvolution

namespace WP.PositiveConvolution
open Set
lemma exists_signed_kernel_polynomial_aux (P:PsiTheory) (h:ℕ):
    ∀g:ℕ,∀c:List ℤ,1 ≤ c.length→complexity g c.length=h→
      ∃F:KernelPolynomial,SignedRepresentation P g c F:=by
  classical
  induction h using Nat.strong_induction_on with
  | h h ih=>
    intro g c hn he
    by_cases hpos:∀k∈c,0 ≤ k
    · by_cases hs:Stable g c.length
      · let d:=c.map Int.toNat
        have hlen:d.length=c.length:=List.length_map _
        have hmap:d.map Int.ofNat=c:=map_ofNat_toNat c hpos
        have hsD:Stable g d.length:=by rwa[hlen]
        have hdef:signedDeficit g c=(dimension g d.length:ℤ)-(d.sum:ℤ):=by
          rw[←hmap]
          dsimp[signedDeficit]
          simp only[List.length_map,sum_map_int]
          rw[dimension_cast_of_stable g d.length hsD]
        by_cases hd:d.sum ≤ dimension g d.length
        · by_cases htop:d.sum=dimension g d.length
          · let C₀:NNReal:=⟨normalized P g d y₀,normalized_critical_nonneg P g d⟩
            refine ⟨MvPolynomial.C C₀*MvPolynomial.X 0^h,?_,?_⟩
            · change BiHomogeneous _ (complexity g c.length) (signedDeficit g c)
              rw[he,hdef,htop,sub_self]
              exact BiHomogeneous.top C₀ h
            · intro Y hY
              change evalKernel (theta Y) (MvPolynomial.C C₀*MvPolynomial.X 0^h)=piSigned P g c Y
              rw[map_mul,evalKernel_C,map_pow,evalKernel_X,Analysis.theta_zero_closed Y hY,one_pow,mul_one]
              have hv:piSigned P g c Y=normalized P g d Y:=by simp only[piSigned,ite_eq_left hpos];rfl
              rw[hv]
              change normalized P g d y₀=normalized P g d Y
              rw[normalized_top P g d Y hY htop,normalized_top P g d y₀ ⟨y₀_pos.le,le_rfl⟩ htop]
          · by_cases hsmall:h ≤ 1
            · have hg:g=1:=by
                unfold complexity at he
                unfold Stable at hs
                unfold dimension at hd htop
                omega
              subst g
              have hld:d.length=1:=by unfold complexity at he;unfold Stable at hs;omega
              obtain ⟨q,hdEq⟩:=List.length_eq_one_iff.mp hld
              have hq:q=0:=by
                rw[hdEq] at hd htop
                norm_num[dimension] at hd htop
                omega
              have hc0:c=[0]:=by rw[←hmap,hdEq,hq];rfl
              rw[hc0]
              refine ⟨MvPolynomial.C (1/8:NNReal)*MvPolynomial.X 1,?_,?_⟩
              · change BiHomogeneous _ (complexity 1 [0].length) (signedDeficit 1 [0])
                norm_num[complexity,signedDeficit]
                exact (BiHomogeneous.X 1).C_mul (1/8:NNReal)
              · intro Y hY
                rw[map_mul,evalKernel_C,evalKernel_X]
                have hv:piSigned P 1 [0] Y=normalized P 1 [0] Y:=by simp[piSigned]
                rw[hv,(initial_amplitudes P Y hY).2.2]
                norm_num
                ring
            · have hh:2 ≤ h:=by omega
              have hfamily (g':ℕ) (c':List ℤ):
                  ∃F:KernelPolynomial,∀hn':1 ≤ c'.length,∀hc':complexity g' c'.length<h,
                    SignedRepresentation P g' c' F:=by
                by_cases hv:1 ≤ c'.length ∧ complexity g' c'.length<h
                · obtain ⟨F,hF⟩:=ih (complexity g' c'.length) hv.2 g' c' hv.1 rfl
                  exact ⟨F,fun _ _=>hF⟩
                · exact ⟨0,fun hn' hc'=>(hv ⟨hn',hc'⟩).elim⟩
              choose F hF using hfamily
              cases hdEq:d with
              | nil=>simp only[hdEq,List.length_nil] at hlen;omega
              | cons p tail=>
                have hparent:(p::tail).map Int.ofNat=c:=by rw[←hdEq];exact hmap
                have hhc:complexity g (tail.length+1)=h:=by
                  have hl:tail.length+1=c.length:=by simpa only[hdEq,List.length_cons] using hlen
                  rwa[hl]
                have hdc:(p::tail).sum ≤ dimension g (tail.length+1):=by simpa only[hdEq,List.length_cons] using hd
                refine ⟨recursionPolynomial F g p tail,?_,?_⟩
                · have hb:=recursionPolynomial_bihomogeneous P F g p h tail hh hhc hF
                  have hlist:((p:ℤ)::tail.map Int.ofNat)=c:=by simpa only[List.map_cons,Int.ofNat_eq_natCast] using hparent
                  rw[hlist,←he] at hb
                  exact hb
                · intro Y hY
                  rw[recursionPolynomial_eval P F g p h tail hh hhc hdc hF Y hY]
                  rw[←hparent]
                  simp only[piSigned]
                  have hall:∀k∈(p::tail).map Int.ofNat,0 ≤ k:=by
                    intro k hk
                    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hk
                    exact Int.natCast_nonneg _
                  rw[ite_eq_left hall]
                  simp only[List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id']
        · refine ⟨0,BiHomogeneous.zero _ _,?_⟩
          intro Y hY
          rw[map_zero]
          change 0=piSigned P g c Y
          rw[piSigned,ite_eq_left hpos]
          exact (normalized_excess P g d Y (by omega)).symm
      · exact ⟨0,BiHomogeneous.zero _ _,fun Y hY=>by rw[map_zero,piSigned_unstable P g c Y hs]⟩
    · refine ⟨0,BiHomogeneous.zero _ _,?_⟩
      intro Y hY
      simp only[map_zero,piSigned,ite_eq_right hpos]
lemma exists_signed_kernel_polynomial (P:PsiTheory) (g:ℕ) (d:List ℤ) (hn:1 ≤ d.length):
    ∃F:KernelPolynomial,SignedRepresentation P g d F:=
  exists_signed_kernel_polynomial_aux P _ g d hn rfl
end WP.PositiveConvolution

namespace WP.PositiveConvolution
lemma weighted_eval_scale (F:KernelPolynomial) (m:ℕ)
    (hm:F.IsWeightedHomogeneous kernelWeight (m:ℤ)) (r:ℝ) (v:ℕ→ℝ):
    evalKernel (fun l=>r^l*v l) F=r^m*evalKernel v F:=by
  classical
  change MvPolynomial.eval₂ NNReal.toRealHom _ F=r^m*MvPolynomial.eval₂ NNReal.toRealHom _ F
  rw[MvPolynomial.eval₂_eq,MvPolynomial.eval₂_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hw:=hm (MvPolynomial.mem_support_iff.mp hd)
  have hwZ:(∑l∈d.support,(d l:ℤ)*(l:ℤ))=(m:ℤ):=by
    simpa only[Finsupp.weight_apply,Finsupp.sum,kernelWeight,nsmul_eq_mul] using hw
  have hwN:(∑l∈d.support,l*d l)=m:=by
    have hh:(∑l∈d.support,(l:ℤ)*(d l:ℤ))=(m:ℤ):=by simpa only[mul_comm] using hwZ
    exact_mod_cast hh
  have hprod:(∏l∈d.support,(r^l*v l)^(d l))=r^m*(∏l∈d.support,(v l)^(d l)):=by
    simp only[mul_pow,←pow_mul]
    rw[Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hwN]
  rw[hprod]
  ring
lemma signedDeficit_map_nat (g:ℕ) (d:List ℕ) (hs:Stable g d.length)
    (hd:d.sum ≤ dimension g d.length):
    signedDeficit g (d.map Int.ofNat)=(deficit g d:ℤ):=by
  dsimp[signedDeficit,deficit]
  rw[Nat.cast_sub hd,dimension_cast_of_stable g d.length hs]
  simp only[List.length_map,sum_map_int]
lemma exists_regularized_amplitude_polynomial (P:PsiTheory) (g:ℕ) (d:List ℕ)
    (hn:1 ≤ d.length) (hs:Stable g d.length) (hd:d.sum ≤ dimension g d.length):
    ∃F:KernelPolynomial,BiHomogeneous F (complexity g d.length) (deficit g d:ℤ) ∧
      ∀Y∈Set.Ico (0:ℝ) y₀,
        a Y^(complexity g d.length)*shifted P g d Y=
          evalKernel (fun l=>(Analysis.kInverseCoeff l Y).re) F:=by
  obtain ⟨F,hF,hEval⟩:=exists_signed_kernel_polynomial P g (d.map Int.ofNat) (by simpa only[List.length_map] using hn)
  have hgrade:BiHomogeneous F (complexity g d.length) (deficit g d:ℤ):=by
    simpa only[List.length_map,signedDeficit_map_nat g d hs hd] using hF
  refine ⟨F,hgrade,?_⟩
  intro Y hY
  have hnval:=hEval Y ⟨hY.1,hY.2.le⟩
  have hp:∀k∈d.map Int.ofNat,0 ≤ k:=by
    intro k hk
    obtain ⟨n,hn,rfl⟩:=List.mem_map.mp hk
    exact Int.natCast_nonneg _
  simp only[piSigned,ite_eq_left hp,List.map_map,Function.comp_def,Int.ofNat_eq_natCast,
    Int.toNat_natCast,List.map_id'] at hnval
  have htheta:(theta Y)=(fun l=>(r Y)^l*(Analysis.kInverseCoeff l Y).re):=by
    funext l
    exact theta_rescaled_kInverse Y hY l
  rw[htheta,weighted_eval_scale F (deficit g d) hgrade.2] at hnval
  rw[normalized,ite_eq_right (ne_of_lt hY.2)] at hnval
  have hr:(r Y)^(deficit g d)≠0:=pow_ne_zero _ (r_pos Y hY).ne'
  apply (mul_left_cancel₀ hr)
  convert hnval.symm using 1 <;>ring
end WP.PositiveConvolution

namespace WP.PositiveConvolution
lemma homogeneous_eval_scale (F:KernelPolynomial) (h:ℕ)
    (hh:F.IsWeightedHomogeneous totalWeight h) (a:ℝ) (v:ℕ→ℝ):
    evalKernel (fun l=>a*v l) F=a^h*evalKernel v F:=by
  classical
  change MvPolynomial.eval₂ NNReal.toRealHom _ F=a^h*MvPolynomial.eval₂ NNReal.toRealHom _ F
  rw[MvPolynomial.eval₂_eq,MvPolynomial.eval₂_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hw:=hh (MvPolynomial.mem_support_iff.mp hd)
  have hwN:(∑l∈d.support,d l)=h:=by
    simpa [Finsupp.weight_apply,Finsupp.sum,totalWeight,nsmul_eq_mul] using hw
  have hprod:(∏l∈d.support,(a*v l)^(d l))=a^h*(∏l∈d.support,(v l)^(d l)):=by
    simp only[mul_pow]
    rw[Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hwN]
  rw[hprod]
  ring
lemma exists_unrescaled_amplitude_polynomial (P:PsiTheory) (g:ℕ) (d:List ℕ)
    (hn:1 ≤ d.length) (hs:Stable g d.length) (hd:d.sum ≤ dimension g d.length):
    ∃F:KernelPolynomial,BiHomogeneous F (complexity g d.length) (deficit g d:ℤ) ∧
      ∀Y∈Set.Ico (0:ℝ) y₀,
        shifted P g d Y=evalKernel (fun l=>realCoeff (fun z=>(K Y z)⁻¹) l) F:=by
  obtain ⟨F,hF,hEval⟩:=exists_regularized_amplitude_polynomial P g d hn hs hd
  refine ⟨F,hF,?_⟩
  intro Y hY
  have hker:(fun l=>(Analysis.kInverseCoeff l Y).re)=
      (fun l=>a Y*realCoeff (fun z=>(K Y z)⁻¹) l):=by
    funext l
    unfold Analysis.kInverseCoeff
    rw[derivX_ofReal]
    simp[Complex.mul_re,realCoeff]
  have hb:=hEval Y hY
  rw[hker,homogeneous_eval_scale F (complexity g d.length) hF.1] at hb
  exact (mul_left_cancel₀ (pow_ne_zero _ (a_pos Y hY).ne')) hb
end WP.PositiveConvolution
