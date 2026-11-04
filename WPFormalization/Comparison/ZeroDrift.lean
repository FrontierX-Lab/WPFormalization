import WPFormalization.Weighted.LayerBudget
/-! The actual zero-count drift of the linear recursion.
Positive-pivot mergers lose a factor two at zero labels, while only the
two endpoint node pairs can create zeros. The full finite layer estimate
is proved for positive and all-zero pivots at the paper threshold 24. -/
noncomputable section
namespace WP
open Set

def zeroPowerRatio (parent child:List ℕ):ℝ:=(2:ℝ)^(zeros child)/(2:ℝ)^(zeros parent)
lemma zeroPowerRatio_nonneg (parent child:List ℕ):0≤zeroPowerRatio parent child:=by unfold zeroPowerRatio;positivity
lemma zeroPowerRatio_le_one (parent child:List ℕ)(hz:zeros child≤zeros parent):
    zeroPowerRatio parent child≤1 := by
  unfold zeroPowerRatio
  apply (div_le_one (by positivity)).mpr
  exact pow_le_pow_right₀ (by norm_num) hz
lemma zeroPowerRatio_le_four (parent child:List ℕ)(hz:zeros child≤zeros parent+2):
    zeroPowerRatio parent child≤4 := by
  unfold zeroPowerRatio
  calc _≤(2:ℝ)^(zeros parent+2)/(2:ℝ)^(zeros parent):=
           div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hz) (by positivity)
       _=4:=by rw[pow_add];field_simp;norm_num
lemma zeroPowerRatio_merger_cap (pivot q l:ℕ)(d:List ℕ)(hp:1≤pivot):
    zeroPowerRatio (pivot::q::d) ((pivot+q+l-1)::d)≤1 := by
  apply zeroPowerRatio_le_one
  exact (counts_antitone_head q (pivot+q+l-1) d (by omega)).1.trans (zeros_cons_bounds pivot (q::d)).1
lemma zeroPowerRatio_zero_merger (pivot l:ℕ)(d:List ℕ)(hp:1≤pivot)(hex:pivot+l≠1):
    zeroPowerRatio (pivot::0::d) ((pivot+l-1)::d)=1/2 := by
  have hp0:pivot≠0:=by omega
  have hk:pivot+l-1≠0:=by omega
  unfold zeroPowerRatio
  simp only[zeros_cons_eq,hp0,hk,ite_false,ite_true,add_zero]
  rw[pow_succ]
  field_simp
lemma zeroPowerRatio_contraction_cap (pivot u v:ℕ)(d:List ℕ):
    zeroPowerRatio (pivot::d) (u::v::d)≤4 := by
  apply zeroPowerRatio_le_four
  simp only[zeros_cons_eq]
  split_ifs <;> omega
lemma zeroPowerRatio_contraction_no_birth (pivot u v:ℕ)(d:List ℕ)(hu:1≤u)(hv:1≤v):
    zeroPowerRatio (pivot::d) (u::v::d)≤1 := by
  apply zeroPowerRatio_le_one
  have hu0:u≠0:=by omega
  have hv0:v≠0:=by omega
  simp only[zeros_cons_eq,hu0,hv0,ite_false,add_zero]
  split_ifs <;> omega

def zeroPairIndices (K:ℕ):Finset ℕ:=(Finset.range K).filter (fun u=>u=0 ∨K-1-u=0)
lemma zeroPairIndices_card (K:ℕ):(zeroPairIndices K).card≤2 := by
  have hsub:zeroPairIndices K⊆{0,K-1}:=by
    intro u hu
    obtain ⟨hu,hcase⟩:=Finset.mem_filter.mp hu
    have hu':=Finset.mem_range.mp hu
    simp only[Finset.mem_insert,Finset.mem_singleton]
    omega
  have hcard:=Finset.card_le_card hsub
  have hc:=Finset.card_insert_le (0:ℕ) ({K-1}:Finset ℕ)
  simp only[Finset.card_singleton] at hc
  omega
lemma zero_contraction_sum_bound (K:ℕ)(f:ℕ→ℝ)
    (hall:∀u∈Finset.range K,f u≤4)
    (hno:∀u∈Finset.range K,1≤u→1≤K-1-u→f u≤1):
    (∑u∈Finset.range K,f u)≤(K:ℝ)+6 := by
  have hterm:∀u∈Finset.range K,f u≤1+(if u=0 ∨K-1-u=0 then 3 else 0):=by
    intro u hu
    split_ifs with hbad
    · linarith[hall u hu]
    · simp only[add_zero]
      exact hno u hu (by omega) (by omega)
  have hs:=Finset.sum_le_sum hterm
  rw[Finset.sum_add_distrib] at hs
  simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hs
  have hbad:(∑u∈Finset.range K,if u=0 ∨K-1-u=0 then (3:ℝ) else 0)≤6:=by
    rw[←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    have hc:( ((Finset.range K).filter (fun u=>u=0 ∨K-1-u=0)).card:ℝ)≤2:=by
      exact_mod_cast zeroPairIndices_card K
    linarith
  linarith
lemma zero_index_sum (d:List ℕ):
    (∑j∈Finset.range d.length,if d[j]! = 0 then (1:ℕ) else 0)=zeros d := by
  induction d with
  | nil => simp[zeros]
  | cons k d ih =>
    simp only[List.length_cons,Finset.sum_range_succ',List.getElem!_cons_zero,List.getElem!_cons_succ,ih,zeros_cons_eq]

def zeroPotentialLayer (pivot:ℕ)(d:List ℕ)(l:ℕ):ℝ:=
  (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
    (if 1≤pivot+d[j]!+l then zeroPowerRatio (pivot::d) (mergerProfile pivot d l j) else 0))+
  2*∑u∈Finset.range (pivot+l-1),zeroPowerRatio (pivot::d) (contractionProfile pivot d l u)
lemma zeroPotentialLayer_positive_drift (pivot:ℕ)(d:List ℕ)(l:ℕ)(hp:1≤pivot)
    (hZ:24≤zeros (pivot::d)):
    zeroPotentialLayer pivot d l≤(∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1))+2*(pivot+l-1:ℕ) := by
  have hp0:pivot≠0:=by omega
  have hparent:zeros (pivot::d)=zeros d:=by simp only[zeros_cons_eq,hp0,ite_false,add_zero]
  have hall:∀j∈Finset.range d.length,zeroPowerRatio (pivot::d) (mergerProfile pivot d l j)≤1:=by
    intro j hj
    have hj':=Finset.mem_range.mp hj
    have hperm:(d[j]!::d.eraseIdx j).Perm d:=by simpa[hj'] using List.getElem_cons_eraseIdx_perm hj'
    have he:=zeroPowerRatio_merger_cap pivot d[j]! l (d.eraseIdx j) hp
    unfold zeroPowerRatio at he ⊢
    rw[zeros_perm (List.Perm.cons pivot hperm)] at he
    exact he
  have hvalid:∀j∈Finset.range d.length,1≤pivot+d[j]!+l:=by intro j hj;omega
  have hLayer:zeroPotentialLayer pivot d l=
      (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*zeroPowerRatio (pivot::d) (mergerProfile pivot d l j))+
      2*∑u∈Finset.range (pivot+l-1),zeroPowerRatio (pivot::d) (contractionProfile pivot d l u):=by
    unfold zeroPotentialLayer
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw[if_pos (hvalid j hj)]
  rw[hLayer]
  by_cases hex:pivot+l=1
  · have hp1:pivot=1:=by omega
    have hl0:l=0:=by omega
    have hc:(∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*zeroPowerRatio (pivot::d) (mergerProfile pivot d l j))≤
      ∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1):=by
      apply Finset.sum_le_sum
      intro j hj
      have hcoef:0≤2*(d[j]!:ℝ)+1:=by positivity
      simpa only[mul_one] using mul_le_mul_of_nonneg_left (hall j hj) hcoef
    simpa[hp1,hl0] using hc
  · have hm: (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*zeroPowerRatio (pivot::d) (mergerProfile pivot d l j))≤
        (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1))-(1/2:ℝ)*zeros d := by
      have he:=finite_label_savings (Finset.range d.length)
        ((Finset.range d.length).filter (fun j=>d[j]! = 0)) (Finset.filter_subset _ _)
        (fun j=>2*(d[j]!:ℝ)+1) (fun j=>zeroPowerRatio (pivot::d) (mergerProfile pivot d l j))
        (1/2:ℝ) (by norm_num) (by intro j hj;have hv:(0:ℝ)≤(d[j]!:ℝ):=Nat.cast_nonneg _;linarith) hall (by
          intro j hj
          have hj':=(Finset.mem_filter.mp hj).1
          have hz: d[j]! = 0:=(Finset.mem_filter.mp hj).2
          have hlt:=Finset.mem_range.mp hj'
          have hperm:(0::d.eraseIdx j).Perm d:=by
            have ht:(d[j]!::d.eraseIdx j).Perm d:=by simpa[hlt] using List.getElem_cons_eraseIdx_perm hlt
            simpa only[hz] using ht
          have hh:=zeroPowerRatio_zero_merger pivot l (d.eraseIdx j) hp hex
          unfold zeroPowerRatio at hh ⊢
          rw[zeros_perm (List.Perm.cons pivot hperm)] at hh
          simpa only[mergerProfile,hz,add_zero,hh] using le_refl (1/2:ℝ))
      have hcard:((Finset.range d.length).filter (fun j=>d[j]! = 0)).card=zeros d:=by
        simpa only[Finset.sum_boole,Nat.cast_id] using zero_index_sum d
      simpa only[hcard,show (1:ℝ)-1/2=1/2 by norm_num] using he
    have hc:=zero_contraction_sum_bound (pivot+l-1)
      (fun u=>zeroPowerRatio (pivot::d) (contractionProfile pivot d l u))
      (by intro u hu;exact zeroPowerRatio_contraction_cap pivot u (pivot+l-2-u) d)
      (by intro u hu hu0 hv0;apply zeroPowerRatio_contraction_no_birth pivot u (pivot+l-2-u) d hu0;omega)
    have hZR:(24:ℝ)≤zeros d:=by rw[hparent] at hZ;exact_mod_cast hZ
    nlinarith
end WP
namespace WP
open Set
lemma zeroPowerRatio_le_two (parent child:List ℕ)(hz:zeros child≤zeros parent+1):
    zeroPowerRatio parent child≤2 := by
  unfold zeroPowerRatio
  calc _≤(2:ℝ)^(zeros parent+1)/(2:ℝ)^(zeros parent):=
           div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hz) (by positivity)
       _=2:=by rw[pow_succ];field_simp
lemma zeroPowerRatio_le_half (parent child:List ℕ)(hz:zeros child+1≤zeros parent):
    zeroPowerRatio parent child≤1/2 := by
  unfold zeroPowerRatio
  apply (div_le_iff₀ (by positivity)).mpr
  have he:(2:ℝ)^(zeros child+1)≤(2:ℝ)^(zeros parent):=pow_le_pow_right₀ (by norm_num) hz
  rw[pow_succ] at he
  linarith
lemma zeroPowerRatio_zero_pivot_contraction_cap (u v:ℕ)(d:List ℕ):
    zeroPowerRatio (0::d) (u::v::d)≤2 := by
  apply zeroPowerRatio_le_two
  simp only[zeros_cons_eq,ite_true]
  split_ifs <;> omega
lemma zeroPowerRatio_zero_pivot_no_birth (u v:ℕ)(d:List ℕ)(huv:1≤u+v):
    zeroPowerRatio (0::d) (u::v::d)≤1 := by
  apply zeroPowerRatio_le_one
  simp only[zeros_cons_eq,ite_true]
  split_ifs <;> omega
lemma zeroPotentialLayer_zero_drift (d:List ℕ)(hd:∀k∈d,k=0)(l:ℕ)(hZ:24≤zeros (0::d)):
    zeroPotentialLayer 0 d l≤(d.length:ℝ)*(if 1≤l then 1 else 0)+2*(l-1:ℕ) := by
  have hq:∀j∈Finset.range d.length,d[j]! = 0:=by
    intro j hj
    apply hd
    have hj':=Finset.mem_range.mp hj
    simpa[hj'] using List.getElem_mem (l:=d) j hj'
  have hrep:d=List.replicate d.length 0:=List.eq_replicate_iff.mpr ⟨rfl,hd⟩
  have hzlen:zeros d=d.length:=by rw[hrep];simp[zeros]
  have hlength:4≤d.length:=by simp only[zeros_cons_eq,ite_true] at hZ;rw[hzlen] at hZ;omega
  by_cases hl:l=0
  · subst l
    unfold zeroPotentialLayer
    simp only[Nat.zero_add,Nat.zero_sub,Finset.range_zero,Finset.sum_empty,mul_zero,add_zero,
      show ¬1≤(0:ℕ) by omega,ite_false]
    norm_num only[Nat.cast_zero,mul_zero,add_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro j hj
    simp[hq j hj]
  · have hl1:1≤l:=by omega
    have hcap:∀j∈Finset.range d.length,zeroPowerRatio (0::d) (mergerProfile 0 d l j)≤1/2:=by
      intro j hj
      have hj':=Finset.mem_range.mp hj
      have hperm:(0::d.eraseIdx j).Perm d:=by
        have ht:(d[j]!::d.eraseIdx j).Perm d:=by simpa[hj'] using List.getElem_cons_eraseIdx_perm hj'
        simpa only[hq j hj] using ht
      have hz:zeros d=zeros (d.eraseIdx j)+1:=by
        rw[←zeros_perm hperm]
        simp[zeros_cons_eq]
      apply zeroPowerRatio_le_half
      simp only[mergerProfile,hq j hj,Nat.zero_add,zeros_cons_eq,ite_true]
      split_ifs <;> omega
    have hm:(∑j∈Finset.range d.length,zeroPowerRatio (0::d) (mergerProfile 0 d l j))≤(d.length:ℝ)/2:=by
      calc _≤∑j∈Finset.range d.length,(1/2:ℝ):=Finset.sum_le_sum hcap
           _=_:=by simp;ring
    have he:zeroPotentialLayer 0 d l=
        (∑j∈Finset.range d.length,zeroPowerRatio (0::d) (mergerProfile 0 d l j))+
        2*∑u∈Finset.range (l-1),zeroPowerRatio (0::d) (contractionProfile 0 d l u):=by
      unfold zeroPotentialLayer
      simp only[Nat.zero_add]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only[hq j hj,Nat.cast_zero,mul_zero,zero_add,one_mul,hl1,ite_true]
    rw[he,if_pos hl1,mul_one]
    by_cases hl2:l=2
    · subst l
      have hn:(∑u∈Finset.range (2-1),zeroPowerRatio (0::d) (contractionProfile 0 d 2 u))≤2:=by
        simpa [contractionProfile] using
          zeroPowerRatio_zero_pivot_contraction_cap 0 (2-2-0) d
      have hlenR:(4:ℝ)≤d.length:=by exact_mod_cast hlength
      norm_num only[Nat.reduceSub,Nat.cast_one] at *
      linarith
    · have hn:(∑u∈Finset.range (l-1),zeroPowerRatio (0::d) (contractionProfile 0 d l u))≤(l-1:ℕ):=by
        calc _≤∑u∈Finset.range (l-1),(1:ℝ):=by
              apply Finset.sum_le_sum
              intro u hu
              apply zeroPowerRatio_zero_pivot_no_birth
              have hu':=Finset.mem_range.mp hu
              omega
             _=_:=by simp
      have hzR:(0:ℝ)≤d.length:=by positivity
      linarith
end WP
