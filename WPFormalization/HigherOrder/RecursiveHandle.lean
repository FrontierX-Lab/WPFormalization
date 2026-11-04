import WPFormalization.HigherOrder.RecursiveMerger
/-! The actual full nonseparating source and its canonical formal pairing.
Weighted coefficients and actual values are genuinely summable. Every
tail, including the empty marking tail, is included; dimension vanishing
identifies the infinite source with the original finite deficit prefix. -/
noncomputable section
open Set
namespace WP.HigherOrder
lemma contractionProfile_length_exact (t l u:ℕ) (d:List ℕ) :
    (contractionProfile t d l u).length=d.length+2:=by simp[contractionProfile]
lemma contractionProfile_sum_weak (t l u:ℕ) (d:List ℕ) (hu:u<t+l-1) :
    (contractionProfile t d l u).sum ≤ (t::d).sum+l:=by
  simp only[contractionProfile,List.sum_cons]
  omega

lemma handle_shifted_profile_coeff_summable (P:PsiTheory) (t n:ℕ) (d:List ℕ)
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    Summable (fun l:ℕ=>weight Y l*PowerSeries.coeff n
      (∑u∈Finset.range (t+l-1),complexityShift 1 (formalProfile P Y (contractionProfile t d l u)))):=by
  classical
  obtain ⟨C,B,Mb,hC,hB,hMb,hcoeff⟩:=canonical_coefficients_on_common_scale P
  obtain ⟨Cm,Mm,hCm,hMm,hops⟩:=canonical_coefficientSum_order_bounds
  let M:ℕ:=max Mb ⌈Mm⌉₊
  have hMbM:Mb ≤ M:=le_max_left _ _
  have hMmM:Mm ≤ (M:ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast (le_max_right Mb ⌈Mm⌉₊))
  have hMtwo:(2:ℝ) ≤ M:=by exact_mod_cast (hMb.trans hMbM)
  let S:=profileOrderWeight (M:ℝ) (n+1) (t::d)
  let e:ℕ→ℝ:=fun i=>C*B^i
  have he:∀i:ℕ,0 ≤ e i:=fun i=>by dsimp[e];positivity
  let K:=PowerSeries.coeff n ((PowerSeries.exp ℝ)*PowerSeries.mk e)
  have hK:0 ≤ K:=coeff_mul_nonneg exp_coeff_nonneg (fun i=>by simpa only[PowerSeries.coeff_mk] using he i) n
  have hT0 (l:ℕ):0 ≤ S+l+1:=by dsimp[S,profileOrderWeight];positivity
  have hpoint (l:ℕ):|PowerSeries.coeff n (∑u∈Finset.range (t+l-1),
      complexityShift 1 (formalProfile P Y (contractionProfile t d l u)))| ≤ K*(S+l+1)^(2*n+1):=by
    have hscalar:scalarOrderWeight (M:ℝ) (n+1) (d.length+2) ≤ S+l+1:=by
      dsimp[S,scalarOrderWeight,profileOrderWeight]
      simp only[List.length_cons,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      linarith[Nat.cast_nonneg (α:=ℝ) (t::d).sum,Nat.cast_nonneg (α:=ℝ) l]
    have hprofile (u:ℕ) (hu:u<t+l-1):profileOrderWeight (M:ℝ) (n+1) (contractionProfile t d l u) ≤ S+l+1:=by
      have hsum:((contractionProfile t d l u).sum:ℝ) ≤ ((t::d).sum:ℝ)+l:=by exact_mod_cast contractionProfile_sum_weak t l u d hu
      dsimp[S,profileOrderWeight]
      rw[contractionProfile_length_exact]
      simp only[List.sum_cons,Nat.cast_add] at hsum
      simp only[List.length_cons,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      linarith
    have hSl:((n+1:ℕ):ℝ) ≤ S+l+1:=by
      have hm:=mul_le_mul_of_nonneg_right hMtwo (Nat.cast_nonneg (n+1) : (0:ℝ) ≤ (n+1:ℕ))
      dsimp[S,profileOrderWeight]
      norm_num only[Nat.cast_add,Nat.cast_one] at hm ⊢
      nlinarith[Nat.cast_nonneg (α:=ℝ) (t::d).sum,Nat.cast_nonneg (α:=ℝ) (t::d).length,Nat.cast_nonneg (α:=ℝ) l]
    have hchild (u:ℕ) (hu:u∈Finset.range (t+l-1)):
        |PowerSeries.coeff n (complexityShift 1 (formalProfile P Y (contractionProfile t d l u)))| ≤ K*(S+l+1)^(2*n):=by
      have hb:=complexityShift_coeff_exponential_majorant 1 (S+l+1)
        (formalProfile P Y (contractionProfile t d l u)) e n (n+1) (by omega) (by norm_num) hSl he (by
          intro i hi
          exact (hcoeff M hMbM (d.length+2) (by omega) (contractionProfile t d l u)
            (by rw[contractionProfile_length_exact];omega) (n+1) (S+l+1) hscalar
            (hprofile u (Finset.mem_range.mp hu)) i (by omega) Y hY).2.2)
      simpa only[K,mul_comm] using hb
    have hcount:((t+l-1:ℕ):ℝ) ≤ S+l+1:=by
      have hn:(t+l-1:ℕ) ≤ t+l:=Nat.sub_le _ _
      have hnR:((t+l-1:ℕ):ℝ) ≤ (t:ℝ)+l:=by exact_mod_cast hn
      have hm0:0 ≤ (M:ℝ)*((n:ℝ)+1):=by positivity
      dsimp[S,profileOrderWeight]
      simp only[List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith[Nat.cast_nonneg (α:=ℝ) d.sum,Nat.cast_nonneg (α:=ℝ) d.length]
    rw[map_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑u∈Finset.range (t+l-1),K*(S+l+1)^(2*n):=Finset.sum_le_sum hchild
      _=((t+l-1:ℕ):ℝ)*(K*(S+l+1)^(2*n)):=by simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      _ ≤ (S+l+1)*(K*(S+l+1)^(2*n)):=mul_le_mul_of_nonneg_right hcount (mul_nonneg hK (pow_nonneg (hT0 l) _))
      _=_:=by rw[pow_succ];ring
  exact (hops (M:ℝ) hMmM (n+1) (t::d).sum (t::d).length (2*n+1) n (by simp) (by omega)
    K hK (fun l=>∑u∈Finset.range (t+l-1),complexityShift 1 (formalProfile P Y (contractionProfile t d l u)))
    Y hY hpoint).1

def handleAtomSeries (P:PsiTheory) (Y:ℝ) (t:ℕ) (d:List ℕ) (l u:ℕ):Series :=
  (PowerSeries.C (2*A Y)*complexityShift 1
    (PowerSeries.X*(formalCusp P Y (d.length+2)*formalProfile P Y (contractionProfile t d l u))))*
    formalGenus P Y (d.length+1)
def handleAtomValue (P:PsiTheory) (g t:ℕ) (d:List ℕ) (Y:ℝ) (l u:ℕ):ℝ :=
  2*(W P (g-1) (d.length+2) Y/W P g (d.length+1) Y)*profile P (g-1) (contractionProfile t d l u) Y
def handleLayerSeries (P:PsiTheory) (Y:ℝ) (t:ℕ) (d:List ℕ) (l:ℕ):Series :=
  ∑u∈Finset.range (t+l-1),handleAtomSeries P Y t d l u
def handleLayerValue (P:PsiTheory) (g t:ℕ) (d:List ℕ) (Y:ℝ) (l:ℕ):ℝ :=
  ∑u∈Finset.range (t+l-1),handleAtomValue P g t d Y l u
def recursiveHandle (P:PsiTheory) (g t:ℕ) (d:List ℕ) (Y:ℝ):ℝ :=
  ∑'l:ℕ,weight Y l*handleLayerValue P g t d Y l

lemma handleLayerSeries_eq_product (P:PsiTheory) (Y:ℝ) (t:ℕ) (d:List ℕ) (l:ℕ) :
    handleLayerSeries P Y t d l=
      (PowerSeries.C (2*A Y)*shiftVariable 1*complexityShift 1 (formalCusp P Y (d.length+2))*formalGenus P Y (d.length+1))*
        (∑u∈Finset.range (t+l-1),complexityShift 1 (formalProfile P Y (contractionProfile t d l u))):=by
  rw[Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  unfold handleAtomSeries
  rw[shifted_loss_one_formal_identity]
  ring

lemma nonseparatingSeries_eq_layer_sum (P:PsiTheory) (t:ℕ) (d:List ℕ) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    nonseparatingSeries Y (formalHierarchyJet P Y) t d=
      coefficientSum (fun l=>PowerSeries.C (weight Y l)*handleLayerSeries P Y t d l):=by
  let a:=PowerSeries.C (2*A Y)*shiftVariable 1*complexityShift 1 (formalCusp P Y (d.length+2))*formalGenus P Y (d.length+1)
  let F:ℕ→Series:=fun l=>PowerSeries.C (weight Y l)*∑u∈Finset.range (t+l-1),
    complexityShift 1 (formalProfile P Y (contractionProfile t d l u))
  have hF:∀n:ℕ,Summable (fun l:ℕ=>PowerSeries.coeff n (F l)):=by
    intro n
    simpa only[F,PowerSeries.coeff_C_mul] using handle_shifted_profile_coeff_summable P t n d Y hY
  change a*coefficientSum F=_
  rw[←coefficientSum_mul_left a F hF]
  apply congrArg coefficientSum
  funext l
  rw[handleLayerSeries_eq_product]
  dsimp[F,a]
  ring

lemma handle_layer_coefficient_summable (P:PsiTheory) (t n:ℕ) (d:List ℕ) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    Summable (fun l:ℕ=>weight Y l*PowerSeries.coeff n (handleLayerSeries P Y t d l)):=by
  let a:=PowerSeries.C (2*A Y)*shiftVariable 1*complexityShift 1 (formalCusp P Y (d.length+2))*formalGenus P Y (d.length+1)
  let F:ℕ→Series:=fun l=>PowerSeries.C (weight Y l)*∑u∈Finset.range (t+l-1),
    complexityShift 1 (formalProfile P Y (contractionProfile t d l u))
  have hF:∀i:ℕ,Summable (fun l:ℕ=>PowerSeries.coeff i (F l)):=by
    intro i
    simpa only[F,PowerSeries.coeff_C_mul] using handle_shifted_profile_coeff_summable P t i d Y hY
  have hs:=(coefficientSum_mul_left_hasSum a F hF n).summable
  convert hs using 1
  funext l
  rw[handleLayerSeries_eq_product]
  have heq:a*F l=PowerSeries.C (weight Y l)*(a*(∑u∈Finset.range (t+l-1),
      complexityShift 1 (formalProfile P Y (contractionProfile t d l u)))):=by dsimp[F];ring
  rw[heq,PowerSeries.coeff_C_mul]

lemma handle_layer_value_summable (P:PsiTheory) (g t:ℕ) (d:List ℕ) (hg:2 ≤ g)
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    Summable (fun l:ℕ=>weight Y l*handleLayerValue P g t d Y l):=by
  obtain ⟨C,B,hC,hB,hW⟩:=Analysis.weight_factorial_moments
  let r:=2*(W P (g-1) (d.length+2) Y/W P g (d.length+1) Y)
  have hs:Summable (fun l:ℕ=>(l+1:ℝ)*|weight Y l|):=by simpa only[pow_one] using (hW 1 Y hY).1
  have hws:Summable (fun l:ℕ=>|weight Y l|):=by simpa only[pow_zero,one_mul] using (hW 0 Y hY).1
  have hmajor:Summable (fun l:ℕ=>|r| *((t:ℝ)+(l+1))*|weight Y l|):=by
    have hh:Summable (fun l:ℕ=>(t:ℝ)*|weight Y l|+(l+1:ℝ)*|weight Y l|):=(hws.mul_left _).add hs
    convert hh.mul_left |r| using 1
    funext l
    ring
  have hpoint (l:ℕ):|handleLayerValue P g t d Y l| ≤ |r| *((t:ℝ)+(l+1)):=by
    unfold handleLayerValue handleAtomValue
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑u∈Finset.range (t+l-1),|r|:=by
        apply Finset.sum_le_sum
        intro u hu
        rw[abs_mul]
        have hb:=(profile_monotone P (g-1) (contractionProfile t d l u) (by simp only[contractionProfile_length_exact];unfold Stable;omega) 0 (by simp only[contractionProfile_length_exact];omega) Y hY).2
        have hp:|profile P (g-1) (contractionProfile t d l u) Y| ≤ 1:=by simpa only[abs_of_nonneg hb.1] using hb.2
        simpa only[mul_one,r] using mul_le_mul_of_nonneg_left hp (abs_nonneg r)
      _ ≤ |r| *((t:ℝ)+(l+1)):=by
        simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        have hnat:t+l-1 ≤ t+(l+1):=by omega
        have hcast:((t+l-1:ℕ):ℝ) ≤ (t:ℝ)+(l+1):=by exact_mod_cast hnat
        nlinarith[abs_nonneg r]
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun l=>norm_nonneg _) _ hmajor
  intro l
  change |weight Y l*handleLayerValue P g t d Y l| ≤ |r| *((t:ℝ)+(l+1))*|weight Y l|
  rw[abs_mul]
  convert mul_le_mul_of_nonneg_left (hpoint l) (abs_nonneg (weight Y l)) using 1 <;>ring

lemma handle_layer_remainder_hasSum (P:PsiTheory) (g t L:ℕ) (d:List ℕ)
    (hg:2 ≤ g) (Y z:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    HasSum (fun l:ℕ=>weight Y l*(handleLayerValue P g t d Y l-truncationValue (handleLayerSeries P Y t d l) L z))
      (recursiveHandle P g t d Y-truncationValue (nonseparatingSeries Y (formalHierarchyJet P Y) t d) L z):=by
  rw[nonseparatingSeries_eq_layer_sum P t d Y hY]
  exact weighted_operator_remainder_hasSum (weight Y) (handleLayerValue P g t d Y)
    (handleLayerSeries P Y t d) L z _ (handle_layer_value_summable P g t d hg Y hY).hasSum
    (fun n hn=>handle_layer_coefficient_summable P t n d Y hY)

lemma handleAtomValue_zero_beyond_deficit (P:PsiTheory) (g t l u:ℕ) (d:List ℕ)
    (hg:2 ≤ g) (hu:u<t+l-1) (Y:ℝ) (hl:deficit g (t::d)<l) :
    handleAtomValue P g t d Y l u=0:=by
  have hsum:(contractionProfile t d l u).sum+2=(t::d).sum+l:=by
    simp only[contractionProfile,List.sum_cons]
    omega
  have hdim:dimension (g-1) (d.length+2)+2=dimension g (d.length+1):=by unfold dimension;omega
  have hlarge:dimension g (d.length+1)<(t::d).sum+l:=by
    unfold deficit at hl
    simp only[List.length_cons] at hl
    omega
  have hexcess:dimension (g-1) (contractionProfile t d l u).length<(contractionProfile t d l u).sum:=by
    rw[contractionProfile_length_exact]
    omega
  unfold handleAtomValue
  rw[profile_excess_zero P (g-1) _ Y hexcess,mul_zero]

lemma recursiveHandle_finite_prefix (P:PsiTheory) (g t:ℕ) (d:List ℕ) (hg:2 ≤ g) (Y:ℝ) :
    recursiveHandle P g t d Y=
      ∑l∈Finset.range (deficit g (t::d)+1),weight Y l*
        (2*(W P (g-1) (d.length+2) Y/W P g (d.length+1) Y))*
        (∑u∈Finset.range (t+l-1),profile P (g-1) (contractionProfile t d l u) Y):=by
  unfold recursiveHandle
  have hs:(∑'l:ℕ,weight Y l*handleLayerValue P g t d Y l)=
      ∑l∈Finset.range (deficit g (t::d)+1),weight Y l*handleLayerValue P g t d Y l:=by
    apply (hasSum_sum_of_ne_finset_zero _).tsum_eq
    intro l hl
    have hlt:deficit g (t::d)<l:=by
      have hh:¬l<deficit g (t::d)+1:=by simpa only[Finset.mem_range] using hl
      omega
    have hz:handleLayerValue P g t d Y l=0:=by
      apply Finset.sum_eq_zero
      intro u hu
      exact handleAtomValue_zero_beyond_deficit P g t l u d hg (Finset.mem_range.mp hu) Y hlt
    rw[hz,mul_zero]
  rw[hs]
  apply Finset.sum_congr rfl
  intro l hl
  simp only[handleLayerValue,handleAtomValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring
end WP.HigherOrder
