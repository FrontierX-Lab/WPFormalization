import WPFormalization.HigherOrder.LinearRemainderAtoms
import WPFormalization.HigherOrder.CanonicalCoefficientScales
import WPFormalization.HigherOrder.WeightedCoefficientSum
import WPFormalization.HigherOrder.LinearRemainderAlgebra
import WPFormalization.HigherOrder.CoefficientSumAlgebra
/-! The actual full merger source of C.15 and its canonical formal pairing.
Every weighted shifted-profile coefficient is genuinely summable. The
formal merger rule is regrouped into actual guarded atoms, whose finite
truncations have true weighted remainder HasSums. Dimension vanishing
identifies the infinite actual sum with the original deficit prefix. -/
noncomputable section
open Set
namespace WP.HigherOrder
lemma mergerProfile_length_exact (t l j:ℕ) (d:List ℕ) (hj:j<d.length) :
    (mergerProfile t d l j).length=d.length:=by
  simp only[mergerProfile,List.length_cons,List.length_eraseIdx_of_lt hj]
  omega
lemma mergerProfile_sum_weak (t l j:ℕ) (d:List ℕ) (hj:j<d.length) :
    (mergerProfile t d l j).sum ≤ (t::d).sum+l:=by
  obtain ⟨hs,hl⟩:=sum_eraseIdx_component d j hj
  simp only[mergerProfile,List.sum_cons]
  omega

lemma merger_shifted_profile_coeff_summable (P:PsiTheory) (t j n:ℕ) (d:List ℕ)
    (hj:j<d.length) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    Summable (fun l:ℕ=>if 1 ≤ t+d[j]!+l then weight Y l*
      PowerSeries.coeff n (complexityShift 1 (formalProfile P Y (mergerProfile t d l j))) else 0):=by
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
  have hpoint (l:ℕ):|PowerSeries.coeff n (complexityShift 1 (formalProfile P Y (mergerProfile t d l j)))| ≤
      K*(S+l+1)^(2*n):=by
    have hscalar:scalarOrderWeight (M:ℝ) (n+1) d.length ≤ S+l+1:=by
      dsimp[S,scalarOrderWeight,profileOrderWeight]
      simp only[List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith[Nat.cast_nonneg (α:=ℝ) (t::d).sum,Nat.cast_nonneg (α:=ℝ) l]
    have hprofile:profileOrderWeight (M:ℝ) (n+1) (mergerProfile t d l j) ≤ S+l+1:=by
      have hsum:((mergerProfile t d l j).sum:ℝ) ≤ ((t::d).sum:ℝ)+l:=by exact_mod_cast mergerProfile_sum_weak t l j d hj
      dsimp[S,profileOrderWeight]
      rw[mergerProfile_length_exact t l j d hj]
      simp only[List.sum_cons,Nat.cast_add] at hsum
      simp only[List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith
    have hSl:((n+1:ℕ):ℝ) ≤ S+l+1:=by
      have hm:=mul_le_mul_of_nonneg_right hMtwo (Nat.cast_nonneg (n+1) : (0:ℝ) ≤ (n+1:ℕ))
      dsimp[S,profileOrderWeight]
      norm_num only[Nat.cast_add,Nat.cast_one] at hm ⊢
      nlinarith[Nat.cast_nonneg (α:=ℝ) (t::d).sum,Nat.cast_nonneg (α:=ℝ) (t::d).length,Nat.cast_nonneg (α:=ℝ) l]
    have hb:=complexityShift_coeff_exponential_majorant 1 (S+l+1)
      (formalProfile P Y (mergerProfile t d l j)) e n (n+1) (by omega) (by norm_num) hSl he (by
        intro i hi
        exact (hcoeff M hMbM d.length (by omega) (mergerProfile t d l j)
          (by rw[mergerProfile_length_exact t l j d hj];omega) (n+1) (S+l+1) hscalar hprofile i (by omega) Y hY).2.2)
    simpa only[K,mul_comm] using hb
  have hs:Summable (fun l:ℕ=>weight Y l*PowerSeries.coeff n
      (complexityShift 1 (formalProfile P Y (mergerProfile t d l j)))):=by
    have hb:=hops (M:ℝ) hMmM (n+1) (t::d).sum (t::d).length (2*n) n (by simp) (by omega)
      K hK (fun l=>complexityShift 1 (formalProfile P Y (mergerProfile t d l j))) Y hY hpoint
    exact hb.1
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun l=>norm_nonneg _) _ hs.norm
  intro l
  split_ifs
  · exact le_rfl
  · simp only[norm_zero]
    exact norm_nonneg _

lemma mergerSeries_eq_atom_sum (P:PsiTheory) (t:ℕ) (d:List ℕ)
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    mergerSeries Y (formalHierarchyJet P Y) t d=
      ∑j∈Finset.range d.length,PowerSeries.C (2*(d[j]!:ℝ)+1)*coefficientSum (fun l=>
        if 1 ≤ t+d[j]!+l then PowerSeries.C (weight Y l)*
          (PowerSeries.C (A Y)*complexityShift 1 (PowerSeries.X*
            (formalCusp P Y d.length*formalProfile P Y (mergerProfile t d l j)))) else 0):=by
  let a:=PowerSeries.C (A Y)*shiftVariable 1*complexityShift 1 (formalCusp P Y d.length)
  change a*(∑j∈Finset.range d.length,PowerSeries.C (2*(d[j]!:ℝ)+1)*coefficientSum (fun l=>
      if 1 ≤ t+d[j]!+l then PowerSeries.C (weight Y l)*complexityShift 1 (formalProfile P Y (mergerProfile t d l j)) else 0))=_
  rw[Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj':j<d.length:=Finset.mem_range.mp hj
  let F:ℕ→Series:=fun l=>if 1 ≤ t+d[j]!+l then
    PowerSeries.C (weight Y l)*complexityShift 1 (formalProfile P Y (mergerProfile t d l j)) else 0
  have hF:∀n:ℕ,Summable (fun l:ℕ=>PowerSeries.coeff n (F l)):=by
    intro n
    have hs:=merger_shifted_profile_coeff_summable P t j n d hj' Y hY
    convert hs using 1
    funext l
    dsimp only[F]
    split_ifs <;>simp only[PowerSeries.coeff_C_mul,map_zero]
  have hPull:=coefficientSum_mul_left a F hF
  change a*(PowerSeries.C (2*(d[j]!:ℝ)+1)*coefficientSum F)=_
  calc
    _=PowerSeries.C (2*(d[j]!:ℝ)+1)*(a*coefficientSum F):=by ring
    _=PowerSeries.C (2*(d[j]!:ℝ)+1)*coefficientSum (fun l=>a*F l):=by rw[←hPull]
    _=_:=by
      congr 1
      apply congrArg coefficientSum
      funext l
      dsimp only[F,a]
      split_ifs
      · rw[shifted_loss_one_formal_identity]
        ring
      · simp only[mul_zero]
def mergerAtomSeries (P:PsiTheory) (Y:ℝ) (t:ℕ) (d:List ℕ) (j l:ℕ):Series :=
  if 1 ≤ t+d[j]!+l then PowerSeries.C (A Y)*complexityShift 1
    (PowerSeries.X*(formalCusp P Y d.length*formalProfile P Y (mergerProfile t d l j))) else 0

def mergerAtomValue (P:PsiTheory) (g t:ℕ) (d:List ℕ) (Y:ℝ) (j l:ℕ):ℝ :=
  if 1 ≤ t+d[j]!+l then W P g d.length Y/W P g (d.length+1) Y*profile P g (mergerProfile t d l j) Y else 0

def recursiveMerger (P:PsiTheory) (g t:ℕ) (d:List ℕ) (Y:ℝ):ℝ :=
  ∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*∑'l:ℕ,weight Y l*mergerAtomValue P g t d Y j l

lemma merger_profile_weight_summable_scaled (P:PsiTheory) (g t j:ℕ) (d:List ℕ)
    (hg:2 ≤ g) (hj:j<d.length) (Y r:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    Summable (fun l:ℕ=>weight Y l*(if 1 ≤ t+d[j]!+l then r*profile P g (mergerProfile t d l j) Y else 0)):=by
  obtain ⟨C,B,hC,hB,hW⟩:=Analysis.weight_factorial_moments
  have hws:Summable (fun l:ℕ=>|weight Y l|):=by simpa only[pow_zero,one_mul] using (hW 0 Y hY).1
  have hprof (l:ℕ):|profile P g (mergerProfile t d l j) Y| ≤ 1:=by
    have hl:=mergerProfile_length_exact t l j d hj
    have hn:1 ≤ (mergerProfile t d l j).length:=by rw[hl];omega
    have hb:=(profile_monotone P g (mergerProfile t d l j) (by unfold Stable;omega) 0 (by omega) Y hY).2
    simpa only[abs_of_nonneg hb.1] using hb.2
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun l=>norm_nonneg _) _ (hws.mul_left |r|)
  intro l
  change |weight Y l*(if 1 ≤ t+d[j]!+l then r*profile P g (mergerProfile t d l j) Y else 0)| ≤ |r| *|weight Y l|
  split_ifs
  · rw[abs_mul,abs_mul]
    have hh:=mul_le_mul_of_nonneg_left (hprof l) (mul_nonneg (abs_nonneg (weight Y l)) (abs_nonneg r))
    convert hh using 1 <;>ring
  · simp only[mul_zero,abs_zero]
    positivity

lemma merger_atom_value_hasSum (P:PsiTheory) (g t j:ℕ) (d:List ℕ)
    (hg:2 ≤ g) (hj:j<d.length) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    HasSum (fun l:ℕ=>weight Y l*mergerAtomValue P g t d Y j l)
      (∑'l:ℕ,weight Y l*mergerAtomValue P g t d Y j l):=by
  exact (merger_profile_weight_summable_scaled P g t j d hg hj Y
    (W P g d.length Y/W P g (d.length+1) Y) hY).hasSum

lemma merger_atom_coefficient_summable (P:PsiTheory) (t j n:ℕ) (d:List ℕ)
    (hj:j<d.length) (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    Summable (fun l:ℕ=>weight Y l*PowerSeries.coeff n (mergerAtomSeries P Y t d j l)):=by
  let a:=PowerSeries.C (A Y)*shiftVariable 1*complexityShift 1 (formalCusp P Y d.length)
  let F:ℕ→Series:=fun l=>if 1 ≤ t+d[j]!+l then
    PowerSeries.C (weight Y l)*complexityShift 1 (formalProfile P Y (mergerProfile t d l j)) else 0
  have hF:∀i:ℕ,Summable (fun l:ℕ=>PowerSeries.coeff i (F l)):=by
    intro i
    have hs:=merger_shifted_profile_coeff_summable P t j i d hj Y hY
    convert hs using 1
    funext l
    dsimp only[F]
    split_ifs <;>simp only[PowerSeries.coeff_C_mul,map_zero]
  have hs:=(coefficientSum_mul_left_hasSum a F hF n).summable
  convert hs using 1
  funext l
  dsimp only[F,mergerAtomSeries]
  split_ifs
  · have heq:a*(PowerSeries.C (weight Y l)*complexityShift 1 (formalProfile P Y (mergerProfile t d l j)))=
      PowerSeries.C (weight Y l)*(PowerSeries.C (A Y)*complexityShift 1
        (PowerSeries.X*(formalCusp P Y d.length*formalProfile P Y (mergerProfile t d l j)))):=by
      rw[shifted_loss_one_formal_identity]
      dsimp[a]
      ring
    rw[heq]
    simp only[PowerSeries.coeff_C_mul]
  · simp only[mul_zero,map_zero]

lemma merger_atom_remainder_hasSum (P:PsiTheory) (g t j L:ℕ) (d:List ℕ)
    (hg:2 ≤ g) (hj:j<d.length) (Y z:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    HasSum (fun l:ℕ=>weight Y l*(mergerAtomValue P g t d Y j l-truncationValue (mergerAtomSeries P Y t d j l) L z))
      ((∑'l:ℕ,weight Y l*mergerAtomValue P g t d Y j l)-
        truncationValue (coefficientSum (fun l=>PowerSeries.C (weight Y l)*mergerAtomSeries P Y t d j l)) L z):=by
  exact weighted_operator_remainder_hasSum (weight Y) (mergerAtomValue P g t d Y j)
    (mergerAtomSeries P Y t d j) L z _ (merger_atom_value_hasSum P g t j d hg hj Y hY)
    (fun n hn=>merger_atom_coefficient_summable P t j n d hj Y hY)

lemma mergerSeries_eq_guarded_atom_sum (P:PsiTheory) (t:ℕ) (d:List ℕ)
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    mergerSeries Y (formalHierarchyJet P Y) t d=
      ∑j∈Finset.range d.length,PowerSeries.C (2*(d[j]!:ℝ)+1)*
        coefficientSum (fun l=>PowerSeries.C (weight Y l)*mergerAtomSeries P Y t d j l):=by
  rw[mergerSeries_eq_atom_sum P t d Y hY]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply congrArg coefficientSum
  funext l
  dsimp[mergerAtomSeries]
  split_ifs <;>simp only[mul_zero]

lemma truncationValue_finset_sum {ι:Type*} (s:Finset ι) (f:ι→Series) (L:ℕ) (z:ℝ) :
    truncationValue (∑i∈s,f i) L z=∑i∈s,truncationValue (f i) L z:=by
  simp only[truncationValue,map_sum,Finset.sum_mul]
  rw[Finset.sum_comm]

lemma recursiveMerger_remainder_identity (P:PsiTheory) (g t L:ℕ) (d:List ℕ)
    (Y z:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    recursiveMerger P g t d Y-truncationValue (mergerSeries Y (formalHierarchyJet P Y) t d) L z=
      ∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
        ((∑'l:ℕ,weight Y l*mergerAtomValue P g t d Y j l)-
          truncationValue (coefficientSum (fun l=>PowerSeries.C (weight Y l)*mergerAtomSeries P Y t d j l)) L z):=by
  rw[mergerSeries_eq_guarded_atom_sum P t d Y hY,truncationValue_finset_sum]
  simp only[truncationValue_C_mul,recursiveMerger,mul_sub,Finset.sum_sub_distrib]

lemma mergerAtomValue_zero_beyond_deficit (P:PsiTheory) (g t j l:ℕ) (d:List ℕ)
    (hg:2 ≤ g) (hj:j<d.length) (Y:ℝ) (hl:deficit g (t::d)<l) :
    mergerAtomValue P g t d Y j l=0:=by
  unfold mergerAtomValue
  split_ifs with hguard
  · have hsum:(mergerProfile t d l j).sum+1=(t::d).sum+l:=by
      obtain ⟨hs,hh⟩:=sum_eraseIdx_component d j hj
      simp only[mergerProfile,List.sum_cons]
      omega
    have hdim:dimension g d.length+1=dimension g (d.length+1):=by unfold dimension;omega
    have hlarge:dimension g (d.length+1)<(t::d).sum+l:=by
      unfold deficit at hl
      simp only[List.length_cons] at hl
      omega
    have hexcess:dimension g (mergerProfile t d l j).length<(mergerProfile t d l j).sum:=by
      rw[mergerProfile_length_exact t l j d hj]
      omega
    rw[profile_excess_zero P g _ Y hexcess,mul_zero]
  · rfl

lemma recursiveMerger_finite_prefix (P:PsiTheory) (g t:ℕ) (d:List ℕ) (hg:2 ≤ g) (Y:ℝ) :
    recursiveMerger P g t d Y=
      ∑l∈Finset.range (deficit g (t::d)+1),weight Y l*
        (W P g d.length Y/W P g (d.length+1) Y)*
        (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
          (if 1 ≤ t+d[j]!+l then profile P g (mergerProfile t d l j) Y else 0)):=by
  have hs (j:ℕ) (hj:j∈Finset.range d.length):
      (∑'l:ℕ,weight Y l*mergerAtomValue P g t d Y j l)=
        ∑l∈Finset.range (deficit g (t::d)+1),weight Y l*mergerAtomValue P g t d Y j l:=by
    apply (hasSum_sum_of_ne_finset_zero _).tsum_eq
    intro l hl
    have hlt:deficit g (t::d)<l:=by
      have hh:¬l<deficit g (t::d)+1:=by simpa only[Finset.mem_range] using hl
      omega
    rw[mergerAtomValue_zero_beyond_deficit P g t j l d hg (Finset.mem_range.mp hj) Y hlt,mul_zero]
  unfold recursiveMerger
  calc
    _=∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
      ∑l∈Finset.range (deficit g (t::d)+1),weight Y l*mergerAtomValue P g t d Y j l:=by
        apply Finset.sum_congr rfl
        intro j hj
        rw[hs j hj]
    _=_:=by
      simp only[Finset.mul_sum]
      rw[Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only[mergerAtomValue]
      split_ifs <;>ring
end WP.HigherOrder
