import WPFormalization.HigherOrder.SecondProfile
import WPFormalization.HigherOrder.Coherence
import WPFormalization.Marked.DilatonCorrection
import WPFormalization.Marked.SecondDegreeLayer

/-! Exact zero-marking child algebra and the three guarded terms in Appendix C.9. -/
noncomputable section
namespace WP.HigherOrder

lemma degreeCorrection_head_zero (k p : ℕ) (Y : ℝ) :
    degreeCorrection (k::List.replicate p (0:ℕ)) Y=
      A Y*(Theta Y*((k:ℝ)^2+((p:ℝ)-3)*k)+2*moment₁ Y*k+
        if 1 ≤ k then 2-(p:ℝ) else 0) := by
  by_cases hk : k=0
  · subst k
    have he : (0::List.replicate p (0:ℕ))=List.replicate (p+1) 0 := by simp [List.replicate_succ]
    rw [he,degreeCorrection_zero_tuple]
    simp
  · rw [degreeCorrection_single_positive k p (by omega) Y,if_pos (by omega)]
    ring

lemma degreeCorrection_two_positive (u v p : ℕ) (hu : 0<u) (hv : 0<v) (Y : ℝ) :
    degreeCorrection (u::v::List.replicate p (0:ℕ)) Y=
      A Y*(Theta Y*(((u:ℝ)+v)^2+((p:ℝ)-2)*((u:ℝ)+v))+
        2*moment₁ Y*((u:ℝ)+v)+3-2*p) := by
  have hf : (u::v::List.replicate p (0:ℕ)).filter (fun k=>0<k)=[u,v] := by simp [hu,hv]
  simp only [degreeCorrection,hf,List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,
    List.length_cons,List.length_nil,List.length_replicate,Nat.cast_add,Nat.cast_one,Nat.cast_zero]
  ring

lemma degreeCorrection_zero_head (u p : ℕ) (Y : ℝ) :
    degreeCorrection (0::u::List.replicate p (0:ℕ)) Y=degreeCorrection (u::List.replicate (p+1) 0) Y := by
  apply degreeCorrection_perm
  simpa [List.replicate_succ] using (List.Perm.swap 0 u (List.replicate p (0:ℕ))).symm

lemma sum_degreeCorrection_two_split (s p : ℕ) (Y : ℝ) :
    (∑ u∈Finset.range (s+1),degreeCorrection (u::(s-u)::List.replicate p (0:ℕ)) Y)=
      A Y*(((s:ℝ)+1)*(Theta Y*((s:ℝ)^2+((p:ℝ)-2)*s)+2*moment₁ Y*s)+
        (3-2*(p:ℝ))*s-1+(if s=0 then 1 else 0)) := by
  cases s with
  | zero => simp [degreeCorrection,Finset.sum_range_one]
  | succ s =>
    rw [Finset.sum_range_succ',Finset.sum_range_succ]
    have hmid (u : ℕ) (hu : u∈Finset.range s) :
        degreeCorrection ((u+1)::(s+1-(u+1))::List.replicate p (0:ℕ)) Y=
          A Y*(Theta Y*(((s:ℝ)+1)^2+((p:ℝ)-2)*((s:ℝ)+1))+
            2*moment₁ Y*((s:ℝ)+1)+3-2*p) := by
      have hu' := Finset.mem_range.mp hu
      rw [degreeCorrection_two_positive (u+1) (s+1-(u+1)) p (by omega) (by omega) Y]
      have he : ((u+1:ℕ):ℝ)+(s+1-(u+1):ℕ)=s+1 := by exact_mod_cast (show u+1+(s+1-(u+1))=s+1 by omega)
      rw [he]
    rw [Finset.sum_congr rfl hmid,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    simp only [Nat.sub_zero]
    rw [degreeCorrection_zero_head,degreeCorrection_single_positive (s+1) (p+1) (by omega) Y]
    have he : (s+1-(s+1):ℕ)=0 := by omega
    rw [he]
    rw [show (s+1)::0::List.replicate p (0:ℕ)=(s+1)::List.replicate (p+1) 0 by simp [List.replicate_succ]]
    rw [degreeCorrection_single_positive (s+1) (p+1) (by omega) Y]
    simp only [Nat.add_sub_cancel_left,show s+1≠0 by omega,ite_false,Nat.cast_add,Nat.cast_one]
    ring
lemma second_merger_head_point (p t l j : ℕ) (hj : j<p) (Y : ℝ) (hn : 1≤t+l) :
    1-transportBeta p Y-degreeCorrection (mergerProfile t (List.replicate p (0:ℕ)) l j) Y=
      rInfinity (p+1) Y ((t:ℝ)+l-1)+(if t+l=1 then A Y*(3-(p:ℝ)) else 0) := by
  have hj' : j<(List.replicate p (0:ℕ)).length := by simpa using hj
  have hget : (List.replicate p (0:ℕ))[j]! = 0 := by simp
  have herase : (List.replicate p (0:ℕ)).eraseIdx j=List.replicate (p-1) 0 := by simp only [List.eraseIdx_replicate,hj,ite_true]
  unfold mergerProfile
  rw [hget,herase,add_zero,degreeCorrection_head_zero]
  have ht : (t+l-1:ℕ)≥0 := Nat.zero_le _
  have hcast : ((t+l-1:ℕ):ℝ)=(t:ℝ)+l-1 := by rw [Nat.cast_sub hn,Nat.cast_add,Nat.cast_one]
  have hp1 : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (show 1≤p by omega),Nat.cast_one]
  simp only [rInfinity,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,hcast,hp1]
  by_cases he : t+l=1
  · simp only [he,show ¬1≤t+l-1 by omega,ite_false,ite_true]
    have hc : (t:ℝ)+l-1=0 := by exact_mod_cast (show t+l-1=0 by omega)
    rw [hc]
    norm_num
    <;>ring
  · simp only [show 1≤t+l-1 by omega,ite_true,he,ite_false]
    ring

lemma second_handle_head_point (p t l : ℕ) (Y : ℝ) (hn : 2≤t+l) :
    (∑u∈Finset.range (t+l-1),(1-transportBeta (p+2) Y-alpha (p+1) Y-
      degreeCorrection (contractionProfile t (List.replicate p (0:ℕ)) l u) Y))=
      sInfinity (p+1) Y ((t:ℝ)+l-2)-(if t+l=2 then A Y else 0) := by
  have hr : t+l-1=(t+l-2)+1 := by omega
  simp only [contractionProfile,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [hr,sum_degreeCorrection_two_split]
  have hc : ((t+l-2:ℕ):ℝ)=(t:ℝ)+l-2 := by rw [Nat.cast_sub hn,Nat.cast_add];norm_num
  simp only [sInfinity,Nat.add_assoc,show 1+1=2 by omega,Nat.cast_add,Nat.cast_one,hc]
  by_cases he : t+l=2
  · simp only [he,show t+l-2=0 by omega,ite_true]
    have hs : (t:ℝ)+l-2=0 := by exact_mod_cast (show t+l-2=0 by omega)
    rw [hs]
    ring
  · simp only [he,show t+l-2≠0 by omega,ite_false]
    ring
lemma secondDegreeCountLayer_head (p t l : ℕ) (Y : ℝ) :
    secondDegreeCountLayer Y t (List.replicate p (0:ℕ)) l=
      A Y*(p:ℝ)*(if 1≤t+l then rInfinity (p+1) Y ((t:ℝ)+l-1)+
        (if t+l=1 then A Y*(3-(p:ℝ)) else 0) else 0)+
      2*A Y*(if 2≤t+l then sInfinity (p+1) Y ((t:ℝ)+l-2)-
        (if t+l=2 then A Y else 0) else 0)+
      (A Y)^2*((if 2≤t+l then (Nat.choose p 2:ℝ)+theta Y 1/2 else 0)+
        (if 3≤t+l then (1/2:ℝ) else 0)) := by
  have hm : (∑j∈Finset.range (List.replicate p (0:ℕ)).length,(2*((List.replicate p (0:ℕ))[j]!:ℝ)+1)*
      (if 1≤t+(List.replicate p (0:ℕ))[j]!+l then 1-transportBeta (List.replicate p (0:ℕ)).length Y-
        degreeCorrection (mergerProfile t (List.replicate p (0:ℕ)) l j) Y else 0))=
        (p:ℝ)*(if 1≤t+l then rInfinity (p+1) Y ((t:ℝ)+l-1)+
          (if t+l=1 then A Y*(3-(p:ℝ)) else 0) else 0) := by
    simp only [List.length_replicate]
    trans ∑j∈Finset.range p,(if 1≤t+l then rInfinity (p+1) Y ((t:ℝ)+l-1)+
      (if t+l=1 then A Y*(3-(p:ℝ)) else 0) else 0)
    · apply Finset.sum_congr rfl
      intro j hj
      have hz : (List.replicate p (0:ℕ))[j]! = 0 := by simp
      rw [hz]
      simp only [Nat.cast_zero,mul_zero,zero_add,one_mul,add_zero]
      by_cases hn : 1≤t+l
      · rw [if_pos hn,if_pos hn,second_merger_head_point p t l j (Finset.mem_range.mp hj) Y hn]
      · simp only [if_neg hn]
    · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hh : (∑u∈Finset.range (t+l-1),(1-transportBeta ((List.replicate p (0:ℕ)).length+2) Y-
      alpha ((List.replicate p (0:ℕ)).length+1) Y-degreeCorrection (contractionProfile t (List.replicate p (0:ℕ)) l u) Y))=
      (if 2≤t+l then sInfinity (p+1) Y ((t:ℝ)+l-2)-(if t+l=2 then A Y else 0) else 0) := by
    simp only [List.length_replicate]
    by_cases hn : 2≤t+l
    · rw [if_pos hn,second_handle_head_point p t l Y hn]
    · rw [if_neg hn,show t+l-1=0 by omega,Finset.range_zero,Finset.sum_empty]
  unfold secondDegreeCountLayer
  rw [hm,hh]
  have hz : zeros (List.replicate p (0:ℕ))=p := by simp [zeros]
  rw [hz]
  ring

end WP.HigherOrder
