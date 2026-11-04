import WPFormalization.Weighted.LinearNormalization
import WPFormalization.Intersection.PainleveComparison
noncomputable section
namespace WP
open Set
lemma normInt_eq_validModel_mul_ratio (P:PsiTheory)(g:ℕ)(ds:List ℤ)(Y:ℝ)(hY:Y∈Icc 0 y₀):
    normInt P g ds Y=validModel g ds Y*ratio P g (ds.map Int.toNat) Y:=by
  by_cases hc:∀k∈ds,0 ≤ k
  · rw [normInt,if_pos hc]
    by_cases hs:Stable g ds.length
    · by_cases hd:(ds.map Int.toNat).sum ≤ dimension g (ds.map Int.toNat).length
      · rw [validModel,if_pos ⟨hc,hs,by simpa only[List.length_map] using hd⟩]
        unfold ratio
        exact (mul_div_cancel₀ _ (model_pos g _ Y (by simpa using hs) hY).ne').symm
      · have hz:=normalized_excess P g (ds.map Int.toNat) Y (by omega)
        rw [hz,validModel,if_neg (by simp only[List.length_map] at hd;tauto),zero_mul]
    · have hz:=normalized_unstable P g (ds.map Int.toNat) Y (by simpa using hs)
      rw [hz,validModel,if_neg (by tauto),zero_mul]
  · simp only [normInt,if_neg hc,validModel,not_false_eq_true]
    rw [if_neg (by tauto),zero_mul]

lemma normInt_nonneg_nonempty (P:PsiTheory)(g:ℕ)(ds:List ℤ)(hn:1 ≤ ds.length)
    (Y:ℝ)(hY:Y∈Icc 0 y₀):0 ≤ normInt P g ds Y:=by
  unfold normInt
  split_ifs
  · exact (normalized_critical_nonneg P g _).trans
      (normalized_pi_le P g _ (by simpa using hn) Y hY)
  · exact le_rfl

lemma positiveRHS_linear_le (P:PsiTheory)(g pivot:ℕ)(d:List ℕ)(Y:ℝ)(hY:Y∈Icc 0 y₀)
    (hg:2 ≤ g)(hd:(pivot::d).sum ≤ dimension g (d.length+1)):
    ((∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
      ∑l∈Finset.range (deficit g (pivot::d)+1),theta Y l*normInt P g
        (((pivot:ℤ)+d[j]!+l-1)::(d.eraseIdx j).map Int.ofNat) Y)+
      (1/2:ℝ)*∑l∈Finset.range (deficit g (pivot::d)+1),theta Y l*
        ∑u∈Finset.range (pivot+l-1),normInt P (g-1)
          ((u:ℤ)::((pivot:ℤ)+l-2-u)::d.map Int.ofNat) Y) ≤
      normalized P g (pivot::d) Y:=by
  rw [positive_recursion P g pivot d Y (by unfold complexity;omega) hd hY]
  unfold positiveRHS
  dsimp only
  rw [if_neg (by omega:g≠0)]
  apply le_add_of_nonneg_right
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro l hl
  apply mul_nonneg (theta_nonneg Y hY l)
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro g₁ hg₁
  apply Finset.sum_nonneg
  intro I hI
  exact mul_nonneg (normInt_nonneg_nonempty P g₁ _ (by simp) Y hY)
    (normInt_nonneg_nonempty P (g-g₁) _ (by simp) Y hY)
end WP
namespace WP
open Set
lemma normInt_merger_ratio (P:PsiTheory)(Y:ℝ)(g pivot:ℕ)(d:List ℕ)(l j:ℕ)
    (hg:2 ≤ g)(hd:(pivot::d).sum ≤ dimension g (d.length+1))
    (hl:l ≤ deficit g (pivot::d))(hj:j<d.length)(hY:Y∈Icc 0 y₀):
    theta Y l*normInt P g (((pivot:ℤ)+d[j]!+l-1)::(d.eraseIdx j).map Int.ofNat) Y /
      model g (pivot::d) Y =
      if 1 ≤ pivot+d[j]!+l then
        linearQ Y (complexity g (d.length+1)) (deficit g (pivot::d)) l /
          (3*((complexity g (d.length+1):ℝ)-1))*ratio P g (mergerProfile pivot d l j) Y else 0:=by
  let ds:=((pivot:ℤ)+(d[j]!:ℤ)+l-1)::(d.eraseIdx j).map Int.ofNat
  change theta Y l*normInt P g ds Y / model g (pivot::d) Y = _
  rw [normInt_eq_validModel_mul_ratio P g ds Y hY]
  by_cases hnode:1 ≤ pivot+d[j]!+l
  · rw [if_pos hnode]
    have he:ds.map Int.toNat=mergerProfile pivot d l j:=by
      dsimp only[ds,mergerProfile]
      simp only[List.map_cons,List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id_fun',id_eq]
      congr 1
      omega
    calc
      _ = (theta Y l*validModel g ds Y/model g (pivot::d) Y)*ratio P g (ds.map Int.toNat) Y:=by ring
      _ = _:=by rw [validModel_merger_ratio g pivot d l j Y hg hd hl hj (by omega) hY,he]
  · rw [if_neg hnode]
    have hneg:validModel g ds Y=0:=by
      apply validModel_zero_negative
      have hp:pivot=0:=by omega
      have hl0:l=0:=by omega
      have hdj:d[j]! = 0:=by omega
      exact ⟨-1,by simp[ds,hp,hl0,hdj],by norm_num⟩
    rw [hneg]
    ring

lemma normInt_contraction_ratio (P:PsiTheory)(Y:ℝ)(g pivot:ℕ)(d:List ℕ)(l u:ℕ)
    (hg:2 ≤ g)(hd:(pivot::d).sum ≤ dimension g (d.length+1))
    (hl:l ≤ deficit g (pivot::d))(hu:u∈Finset.range (pivot+l-1))(hY:Y∈Icc 0 y₀):
    theta Y l*normInt P (g-1) ((u:ℤ)::((pivot:ℤ)+l-2-u)::d.map Int.ofNat) Y /
      model g (pivot::d) Y =
        (4*linearQ Y (complexity g (d.length+1)) (deficit g (pivot::d)) l /
          (3*((complexity g (d.length+1):ℝ)-1)))*ratio P (g-1) (contractionProfile pivot d l u) Y:=by
  let ds:=(u:ℤ)::((pivot:ℤ)+l-2-u)::d.map Int.ofNat
  have hu':=Finset.mem_range.mp hu
  have he:ds.map Int.toNat=contractionProfile pivot d l u:=by
    dsimp only[ds,contractionProfile]
    simp only[List.map_cons,List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id_fun',id_eq]
    congr 1
    congr 1
    omega
  change theta Y l*normInt P (g-1) ds Y/model g (pivot::d) Y = _
  rw [normInt_eq_validModel_mul_ratio P (g-1) ds Y hY]
  calc
    _ = (theta Y l*validModel (g-1) ds Y/model g (pivot::d) Y)*ratio P (g-1) (ds.map Int.toNat) Y:=by ring
    _ = _:=by rw [validModel_contraction_ratio g pivot d l u Y hg hd hl hu hY,he]
end WP
namespace WP
open Set
lemma linear_ratio_subaveraging (P:PsiTheory)(Y:ℝ)(g pivot:ℕ)(d:List ℕ)
    (hg:2 ≤ g)(hd:(pivot::d).sum ≤ dimension g (d.length+1))(hY:Y∈Icc 0 y₀):
    (∑l∈Finset.range (deficit g (pivot::d)+1),
      (linearQ Y (complexity g (d.length+1)) (deficit g (pivot::d)) l /
        (3*((complexity g (d.length+1):ℝ)-1)))*
        ((∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
          (if 1 ≤ pivot+d[j]!+l then ratio P g (mergerProfile pivot d l j) Y else 0))+
          2*∑u∈Finset.range (pivot+l-1),ratio P (g-1) (contractionProfile pivot d l u) Y)) ≤
      ratio P g (pivot::d) Y:=by
  have hpar:0 < model g (pivot::d) Y:=model_pos g _ Y (by unfold Stable;simp only[List.length_cons];omega) hY
  have hm:
      (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
        ∑l∈Finset.range (deficit g (pivot::d)+1),theta Y l*normInt P g
          (((pivot:ℤ)+d[j]!+l-1)::(d.eraseIdx j).map Int.ofNat) Y)/model g (pivot::d) Y =
      ∑l∈Finset.range (deficit g (pivot::d)+1),
        (linearQ Y (complexity g (d.length+1)) (deficit g (pivot::d)) l /
          (3*((complexity g (d.length+1):ℝ)-1)))*
          (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
            (if 1 ≤ pivot+d[j]!+l then ratio P g (mergerProfile pivot d l j) Y else 0)):=by
    simp only[Finset.sum_div,Finset.mul_sum,mul_div_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro j hj
    have hterm:=normInt_merger_ratio P Y g pivot d l j hg hd (by have :=Finset.mem_range.mp hl;omega) (Finset.mem_range.mp hj) hY
    rw [mul_div_assoc] at hterm
    rw [hterm]
    split_ifs <;> ring
  have hn:
      ((1/2:ℝ)*∑l∈Finset.range (deficit g (pivot::d)+1),theta Y l*
        ∑u∈Finset.range (pivot+l-1),normInt P (g-1)
          ((u:ℤ)::((pivot:ℤ)+l-2-u)::d.map Int.ofNat) Y)/model g (pivot::d) Y =
      ∑l∈Finset.range (deficit g (pivot::d)+1),
        (linearQ Y (complexity g (d.length+1)) (deficit g (pivot::d)) l /
          (3*((complexity g (d.length+1):ℝ)-1)))*
          (2*∑u∈Finset.range (pivot+l-1),ratio P (g-1) (contractionProfile pivot d l u) Y):=by
    simp only[Finset.sum_div,Finset.mul_sum,mul_div_assoc]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro u hu
    have hterm:=normInt_contraction_ratio P Y g pivot d l u hg hd (by have :=Finset.mem_range.mp hl;omega) hu hY
    rw [mul_div_assoc] at hterm
    rw [hterm]
    ring
  have hlin:=div_le_div_of_nonneg_right (positiveRHS_linear_le P g pivot d Y hY hg hd) hpar.le
  rw [add_div,hm,hn,←Finset.sum_add_distrib] at hlin
  convert hlin using 1 <;> try rfl
  apply Finset.sum_congr rfl
  intro l hl
  ring
end WP
