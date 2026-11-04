import WPFormalization.HigherOrder.SecondLinearCoefficients
import WPFormalization.Marked.SecondSeparatingInitial
import WPFormalization.Analysis.FiniteLossTwo

/-! The actual formal separating coefficient in degree two comes from exactly the sphere and torus components of loss two. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

lemma ratioSeries_coeff_lt_loss (Y : ℝ) (F : HierarchyJet) (p j s k : ℕ) (hk : k<2*j+s) :
    PowerSeries.coeff k (ratioSeries Y F p j s)=0 := by
  unfold ratioSeries
  simp only [mul_pow,←map_pow,mul_assoc]
  rw [PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul',if_neg (by omega)]
  simp

lemma ratioSeries_coeff_loss (Y : ℝ) (F : HierarchyJet)
    (hc : ∀p,constantCoeff (F.cusp p)=1) (hg : ∀p,constantCoeff (F.genus p)=1)
    (p j s : ℕ) : PowerSeries.coeff (2*j+s) (ratioSeries Y F p j s)=A Y^(2*j+s) := by
  unfold ratioSeries
  simp only [mul_pow,←map_pow,mul_assoc]
  rw [PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul',if_pos le_rfl,Nat.sub_self,
    coeff_zero_eq_constantCoeff]
  simp [hc,hg,complexityShift_constant]

lemma ratioSeries_two (Y : ℝ) (F : HierarchyJet)
    (hc : ∀p,constantCoeff (F.cusp p)=1) (hg : ∀p,constantCoeff (F.genus p)=1)
    (p j s : ℕ) (hr : 2≤2*j+s) :
    PowerSeries.coeff 2 (ratioSeries Y F p j s)=if 2*j+s=2 then (A Y)^2 else 0 := by
  by_cases he : 2*j+s=2
  · rw [if_pos he,←he,ratioSeries_coeff_loss Y F hc hg]
  · rw [if_neg he,ratioSeries_coeff_lt_loss Y F p j s 2 (by omega)]

lemma selectedNat_int_map (d : List ℕ) (I : Finset ℕ) :
    (selectedNat d I).map Int.ofNat=selected (d.map Int.ofNat) I := by
  unfold selectedNat selected
  simp only [List.map_map,List.length_map]
  apply List.map_congr_left
  intro j hj
  have hj' : j<d.length := (List.mem_range.mp (List.mem_filter.mp hj).1)
  simp [hj']

lemma smallW_sphere_selected (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀)
    (d : List ℕ) (u : ℕ) (I : Finset ℕ) (hI : I⊆Finset.range d.length) (hcard : I.card=2) :
    smallW P Y 0 (u::selectedNat d I)=(if u=0 ∧ ∀j∈I,d[j]! = 0 then 1 else 0) := by
  have hi:=normInt_sphere_selected P d u I hI hcard Y hY
  have he : ((u::selectedNat d I).map Int.ofNat)=((u:ℤ)::selected (d.map Int.ofNat) I) := by
    simp only [List.map_cons,selectedNat_int_map]
    rfl
  rw [←he] at hi
  have hn : ∀k∈((u::selectedNat d I).map Int.ofNat),0≤k := by simp
  simpa only [normInt,if_pos hn,List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id',smallW,pow_zero,one_mul] using hi

lemma smallW_torus_one (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (u : ℕ) :
    smallW P Y 1 [u]=(if u=0 then theta Y 1/2 else if u=1 then 1/2 else 0) := by
  have hn : ∀k∈([(u:ℤ)] : List ℤ),0≤k := by simp
  simpa only [normInt,if_pos hn,List.map_cons,List.map_nil,Int.toNat_natCast,smallW,pow_one] using
    normInt_torus_one P u Y hY
lemma separatingSeries_two_raw (P : PsiTheory) (Y : ℝ) (t : ℕ) (d : List ℕ) :
    PowerSeries.coeff 2 (separatingSeries P Y (hierarchyJet P Y 1) 2 t d)=
      (A Y)^2*((∑I∈(Finset.range d.length).powerset,if I.card=2 then
        (∑'l:ℕ,weight Y l*(∑u∈Finset.range (t+l-1),smallW P Y 0 (u::selectedNat d I))) else 0)+
        (∑'l:ℕ,weight Y l*(∑u∈Finset.range (t+l-1),smallW P Y 1 [u]))) := by
  let F:=hierarchyJet P Y 1
  let B : ℕ→Finset ℕ→Series:=fun j I=>coefficientSum (fun l=>C (weight Y l)*
    ∑u∈Finset.range (t+l-1),C (smallW P Y j (u::selectedNat d I))*
      complexityShift (2*j+I.card) (F.profile ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))
  have hB (j : ℕ) (I : Finset ℕ) : constantCoeff (B j I)=
      ∑'l:ℕ,weight Y l*(∑u∈Finset.range (t+l-1),smallW P Y j (u::selectedNat d I)) := by
    simp only [B,coefficientSum_constant,map_mul,map_sum,constantCoeff_C,
      complexityShift_constant,F,hierarchy_one_profile_constant,mul_one]
  have hterm (j : ℕ) (I : Finset ℕ) :
      PowerSeries.coeff 2 (if Stable j (I.card+1) ∧ 2≤2*j+I.card ∧ 2*j+I.card≤2 then
        ratioSeries Y F (d.length+1) j I.card*B j I else 0)=
      if 2*j+I.card=2 then (A Y)^2*constantCoeff (B j I) else 0 := by
    by_cases he : 2*j+I.card=2
    · have hs : Stable j (I.card+1) := by unfold Stable;omega
      rw [if_pos ⟨hs,by omega,by omega⟩,if_pos he,coeff_two_mul,
        ratioSeries_coeff_lt_loss Y F (d.length+1) j I.card 1 (by omega),
        show constantCoeff (ratioSeries Y F (d.length+1) j I.card)=0 by
          rw [←coeff_zero_eq_constantCoeff];exact ratioSeries_coeff_lt_loss Y F (d.length+1) j I.card 0 (by omega),
        ratioSeries_two Y F (hierarchy_one_cusp_constant P Y) (hierarchy_one_genus_constant P Y)
          (d.length+1) j I.card (by omega),if_pos he]
      ring
    · have hs : ¬(Stable j (I.card+1) ∧ 2≤2*j+I.card ∧ 2*j+I.card≤2) := by omega
      rw [if_neg hs,if_neg he]
      simp
  change PowerSeries.coeff 2 (∑j∈Finset.range (2+1),∑I∈(Finset.range d.length).powerset,
    if Stable j (I.card+1) ∧ 2≤2*j+I.card ∧ 2*j+I.card≤2 then
      ratioSeries Y F (d.length+1) j I.card*B j I else 0)=_
  simp only [map_sum,hterm,hB]
  rw [Analysis.finite_loss_two_sum 2 (by omega),Analysis.sum_card_zero]
  have he : selectedNat d ∅=[] := by simp [selectedNat]
  rw [he,mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;>ring
lemma smallW_sphere_pair_sum (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀)
    (k : ℕ) (d : List ℕ) (I : Finset ℕ) (hI : I⊆Finset.range d.length) (hcard : I.card=2) :
    (∑u∈Finset.range (k-1),smallW P Y 0 (u::selectedNat d I))=
      (if ∀j∈I,d[j]! = 0 then (if 2≤k then (1:ℝ) else 0) else 0) := by
  simp_rw [smallW_sphere_selected P Y hY d _ I hI hcard]
  have hk : (0<k-1)↔(2≤k) := by omega
  by_cases hz : ∀j∈I,d[j]! = 0
  · rw [if_pos hz]
    have he (u:ℕ) : (u=0 ∧ ∀j∈I,d[j]! = 0)↔u=0 := by
      exact ⟨And.left,fun hu=>⟨hu,hz⟩⟩
    simp_rw [he]
    simp [Finset.mem_range,hk]
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro u hu
    exact if_neg (fun hh=>hz hh.2)

lemma smallW_torus_pair_sum (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (k : ℕ) :
    (∑u∈Finset.range (k-1),smallW P Y 1 [u])=
      (if 2≤k then theta Y 1/2 else 0)+(if 3≤k then (1/2:ℝ) else 0) := by
  simp_rw [smallW_torus_one P Y hY]
  have he (u:ℕ) : (if u=0 then theta Y 1/2 else if u=1 then (1/2:ℝ) else 0)=
      (if u=0 then theta Y 1/2 else 0)+(if u=1 then (1/2:ℝ) else 0) := by
    split_ifs
    all_goals first | omega | ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have hk₀ : (0<k-1)↔(2≤k) := by omega
  have hk₁ : (1<k-1)↔(3≤k) := by omega
  simp [Finset.mem_range,hk₀,hk₁]

lemma smallW_sphere_weighted_sum (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀)
    (t : ℕ) (d : List ℕ) (I : Finset ℕ) (hI : I⊆Finset.range d.length) (hcard : I.card=2) :
    (∑'l:ℕ,weight Y l*(∑u∈Finset.range (t+l-1),smallW P Y 0 (u::selectedNat d I)))=
      (if ∀j∈I,d[j]! = 0 then tailWeight Y (2-t) else 0) := by
  simp_rw [smallW_sphere_pair_sum P Y hY _ d I hI hcard]
  by_cases hz : ∀j∈I,d[j]! = 0
  · simp only [if_pos hz,mul_ite,mul_one,mul_zero]
    exact (weight_cutoff_hasSum Y hY 2 t).tsum_eq
  · simp only [if_neg hz,mul_zero,tsum_zero]

lemma smallW_torus_weighted_sum (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (t : ℕ) :
    (∑'l:ℕ,weight Y l*(∑u∈Finset.range (t+l-1),smallW P Y 1 [u]))=
      (theta Y 1/2)*tailWeight Y (2-t)+(1/2:ℝ)*tailWeight Y (3-t) := by
  have hs:=((weight_cutoff_hasSum Y hY 2 t).mul_left (theta Y 1/2)).add
    ((weight_cutoff_hasSum Y hY 3 t).mul_left (1/2:ℝ))
  apply HasSum.tsum_eq
  convert! hs using 1
  funext l
  rw [smallW_torus_pair_sum P Y hY]
  split_ifs <;>ring

lemma separatingSeries_two (P : PsiTheory) (Y : ℝ) (hY : Y∈Set.Icc (0:ℝ) y₀) (t : ℕ) (d : List ℕ) :
    PowerSeries.coeff 2 (separatingSeries P Y (hierarchyJet P Y 1) 2 t d)=
      (A Y)^2*(((Nat.choose (zeros d) 2:ℝ)+theta Y 1/2)*tailWeight Y (2-t)+tailWeight Y (3-t)/2) := by
  rw [separatingSeries_two_raw,smallW_torus_weighted_sum P Y hY]
  have hsp : (∑I∈(Finset.range d.length).powerset,if I.card=2 then
      (∑'l:ℕ,weight Y l*(∑u∈Finset.range (t+l-1),smallW P Y 0 (u::selectedNat d I))) else 0)=
      (Nat.choose (zeros d) 2:ℝ)*tailWeight Y (2-t) := by
    trans ∑I∈(Finset.range d.length).powerset,
      (if I.card=2 ∧ ∀j∈I,d[j]! = 0 then (1:ℝ) else 0)*tailWeight Y (2-t)
    · apply Finset.sum_congr rfl
      intro I hI
      by_cases hc : I.card=2
      · rw [if_pos hc,smallW_sphere_weighted_sum P Y hY t d I (Finset.mem_powerset.mp hI) hc]
        by_cases hz : ∀j∈I,d[j]?.getD (0:ℕ) = 0 <;>simp [hc,hz]
      · simp only [hc,false_and,ite_false,zero_mul]
    · rw [←Finset.sum_mul,sum_zero_pair_subsets]
  rw [hsp]
  ring

end WP.HigherOrder
