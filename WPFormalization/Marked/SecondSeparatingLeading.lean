import WPFormalization.Marked.SecondSeparatingInitial
import WPFormalization.Marked.SecondSeparatingRatios
import WPFormalization.Analysis.FiniteLossTwo

/-! Exact sphere and torus extraction and their genuine uniform leading terms. -/

noncomputable section
open Set

namespace WP
lemma secondSeparatingLeading_eq_low_genera (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (hg : 1 ≤ g) (Y : ℝ) :
    secondSeparatingLeading P g k d Y=
      ∑ u ∈ Finset.range (k-1),((∑ I ∈ (Finset.range d.length).powerset,
        if I.card=2 then secondSeparatingTerm P g k d u 0 I Y else 0)+
          secondSeparatingTerm P g k d u 1 ∅ Y) := by
  unfold secondSeparatingLeading
  apply Finset.sum_congr rfl
  intro u hu
  rw [Analysis.finite_loss_two_sum g hg,Analysis.sum_card_zero]

lemma secondSeparatingTerm_sphere (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (u : ℕ) (I : Finset ℕ) (hg : 1 ≤ g) (hu : u∈Finset.range (k-1))
    (hI : I⊆Finset.range d.length) (hcard : I.card=2) (Y : ℝ) (hY : Y∈Icc 0 y₀) :
    secondSeparatingTerm P g k d u 0 I Y=
      (if u=0 ∧ ∀j∈I,d[j]! = 0 then
        (W P g (d.length-1) Y/W P g (d.length+1) Y)*
          profile P g (splitLargeProfile (k-2) d ((Finset.range d.length)\I)) Y else 0) := by
  unfold secondSeparatingTerm
  rw [normInt_sphere_selected P d u I hI hcard Y hY]
  by_cases hz : u=0 ∧ ∀j∈I,d[j]! = 0
  · rw [if_pos hz,if_pos hz]
    have hu' := Finset.mem_range.mp hu
    have hk : 2 ≤ k := by omega
    have hn : (k:ℤ)-2-u=(k-2:ℕ) := by omega
    have hcardI : I.card ≤ d.length := by simpa only [Finset.card_range] using Finset.card_le_card hI
    have hlen : ((Finset.range d.length)\I).card+1=d.length-1 := by
      rw [Finset.card_sdiff_of_subset hI,Finset.card_range,hcard]
      omega
    rw [Nat.sub_zero,hn,mul_one]
    have hi := normInt_splitLargeProfile P g (k-2) d ((Finset.range d.length)\I) hg Finset.sdiff_subset Y hY
    rw [hlen] at hi
    rw [hi]
    ring
  · rw [if_neg hz,if_neg hz,mul_zero,zero_mul,zero_div]

lemma secondSeparatingTerm_torus (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (u : ℕ) (hg : 2 ≤ g) (hu : u∈Finset.range (k-1)) (Y : ℝ) (hY : Y∈Icc 0 y₀) :
    secondSeparatingTerm P g k d u 1 ∅ Y=
      (if u=0 then theta Y 1/2 else if u=1 then 1/2 else 0)*
        ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
          profile P (g-1) (splitLargeProfile (k-2-u) d (Finset.range d.length)) Y) := by
  have hu' := Finset.mem_range.mp hu
  have hn : (k:ℤ)-2-u=(k-2-u:ℕ) := by omega
  have hpow : (4:ℝ)^g=4*(4:ℝ)^(g-1) := by rw [←pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ g)]
  have he : selected (d.map Int.ofNat) ∅=[] := by simp [selected]
  unfold secondSeparatingTerm
  rw [he,Finset.sdiff_empty,hn]
  calc
    _ = ((4:ℝ)*normInt P 1 [(u:ℤ)] Y)*
        ((4:ℝ)^(g-1)*normInt P (g-1) (((k-2-u:ℕ):ℤ)::selected (d.map Int.ofNat) (Finset.range d.length)) Y)/
          W P g (d.length+1) Y := by rw [hpow];ring
    _ = _ := by
      rw [normInt_torus_one P u Y hY,normInt_splitLargeProfile P (g-1) (k-2-u) d (Finset.range d.length)
        (by omega) (by rfl) Y hY,Finset.card_range]
      ring
end WP

namespace WP

def secondSeparatingSphere (P : PsiTheory) (g k : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  ∑ u ∈ Finset.range (k-1),∑ I ∈ (Finset.range d.length).powerset,
    if I.card=2 then secondSeparatingTerm P g k d u 0 I Y else 0

def secondSeparatingTorus (P : PsiTheory) (g k : ℕ) (d : List ℕ) (Y : ℝ) : ℝ :=
  ∑ u ∈ Finset.range (k-1),secondSeparatingTerm P g k d u 1 ∅ Y

lemma secondSeparatingLeading_sphere_torus (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (hg : 1 ≤ g) (Y : ℝ) :
    secondSeparatingLeading P g k d Y=secondSeparatingSphere P g k d Y+secondSeparatingTorus P g k d Y := by
  rw [secondSeparatingLeading_eq_low_genera P g k d hg Y,Finset.sum_add_distrib]
  rfl

lemma secondSeparatingSphere_formula (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (hg : 1 ≤ g) (Y : ℝ) (hY : Y∈Icc 0 y₀) :
    secondSeparatingSphere P g k d Y=
      if 2 ≤ k then ∑ I ∈ (Finset.range d.length).powerset,
        if I.card=2 ∧ ∀j∈I,d[j]! = 0 then
          (W P g (d.length-1) Y/W P g (d.length+1) Y)*
            profile P g (splitLargeProfile (k-2) d ((Finset.range d.length)\I)) Y else 0
      else 0 := by
  classical
  by_cases hk : 2 ≤ k
  · rw [if_pos hk]
    unfold secondSeparatingSphere
    rw [Finset.sum_eq_single 0]
    · apply Finset.sum_congr rfl
      intro I hI
      by_cases hc : I.card=2
      · rw [if_pos hc,secondSeparatingTerm_sphere P g k d 0 I hg
          (by simp;omega) (Finset.mem_powerset.mp hI) hc Y hY]
        simp only [true_and,if_pos rfl,hc]
      · have hm : ¬(I.card=2 ∧ ∀j∈I,d[j]! = 0) := by tauto
        rw [if_neg hc,if_neg hm]
    · intro u hu hne
      apply Finset.sum_eq_zero
      intro I hI
      by_cases hc : I.card=2
      · rw [if_pos hc,secondSeparatingTerm_sphere P g k d u I hg hu
          (Finset.mem_powerset.mp hI) hc Y hY]
        simp [hne]
      · exact if_neg hc
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  · have he : k-1=0 := by omega
    simp only [secondSeparatingSphere,he,Finset.range_zero,Finset.sum_empty,if_neg hk]

lemma secondSeparatingTorus_formula (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (Y : ℝ) (hY : Y∈Icc 0 y₀) :
    secondSeparatingTorus P g k d Y=
      (if 2 ≤ k then (theta Y 1/2)*
        ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
          profile P (g-1) (splitLargeProfile (k-2) d (Finset.range d.length)) Y) else 0)+
      (if 3 ≤ k then (1/2:ℝ)*
        ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
          profile P (g-1) (splitLargeProfile (k-3) d (Finset.range d.length)) Y) else 0) := by
  classical
  have hp (u : ℕ) (hu : u∈Finset.range (k-1)) :
      secondSeparatingTerm P g k d u 1 ∅ Y=
      (if u=0 then (theta Y 1/2)*
        ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
          profile P (g-1) (splitLargeProfile (k-2) d (Finset.range d.length)) Y) else 0)+
      (if u=1 then (1/2:ℝ)*
        ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
          profile P (g-1) (splitLargeProfile (k-3) d (Finset.range d.length)) Y) else 0) := by
    rw [secondSeparatingTerm_torus P g k d u hg hu Y hY]
    by_cases h0 : u=0
    · subst u
      simp
    · by_cases h1 : u=1
      · subst u
        simp only [if_neg (by omega : ¬(1:ℕ)=0),if_pos rfl,zero_add]
        rw [show k-2-1=k-3 by omega]
        simp only [ite_true]
      · simp [h0,h1]
  unfold secondSeparatingTorus
  calc
    _ = ∑ u ∈ Finset.range (k-1),
      ((if u=0 then (theta Y 1/2)*
        ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
          profile P (g-1) (splitLargeProfile (k-2) d (Finset.range d.length)) Y) else 0)+
      (if u=1 then (1/2:ℝ)*
        ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
          profile P (g-1) (splitLargeProfile (k-3) d (Finset.range d.length)) Y) else 0)) :=
      Finset.sum_congr rfl hp
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_range]
      have h0 : 0<k-1 ↔ 2 ≤ k := by omega
      have h1 : 1<k-1 ↔ 3 ≤ k := by omega
      simp only [h0,h1]
end WP

namespace WP
lemma secondSeparatingSphere_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ k : ℕ,∀ d : List ℕ,d.length+1=p →
      ∀ Y∈Icc (0:ℝ) y₀,
      |secondSeparatingSphere P g k d Y-
        (if 2 ≤ k then (Nat.choose (zeros d) 2:ℝ)*(A Y)^2/(complexity g p:ℝ)^2 else 0)| ≤
        C*((k+d.sum:ℕ)+1:ℝ)^2/(complexity g p:ℝ)^3 := by
  by_cases hp3 : 3 ≤ p
  · obtain ⟨Cs,hCs,Gs,hs⟩ := sphere_split_profile_leading_uniform P p hp3
    refine ⟨(2:ℝ)^(p-1)*Cs,by positivity,max Gs 2,?_⟩
    intro g hg k d hd Y hY
    have hgS : Gs ≤ g := (le_max_left _ _).trans hg
    have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
    have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
    rw [secondSeparatingSphere_formula P g k d (by omega) Y hY]
    by_cases hk : 2 ≤ k
    · rw [if_pos hk,if_pos hk]
      have hpoint (I : Finset ℕ) (hI : I∈(Finset.range d.length).powerset) :
          |(if I.card=2 ∧ ∀j∈I,d[j]! = 0 then
            (W P g (d.length-1) Y/W P g (d.length+1) Y)*
              profile P g (splitLargeProfile (k-2) d ((Finset.range d.length)\I)) Y else 0)-
            (if I.card=2 ∧ ∀j∈I,d[j]! = 0 then (A Y)^2/(complexity g p:ℝ)^2 else 0)| ≤
          Cs*((k+d.sum:ℕ)+1:ℝ)^2/(complexity g p:ℝ)^3 := by
        by_cases hm : I.card=2 ∧ ∀j∈I,d[j]! = 0
        · rw [if_pos hm,if_pos hm]
          have hIs := Finset.mem_powerset.mp hI
          have hcard : I.card ≤ d.length := by simpa only [Finset.card_range] using Finset.card_le_card hIs
          have hl : (splitLargeProfile (k-2) d ((Finset.range d.length)\I)).length=p-2 := by
            rw [splitLargeProfile_length _ _ _ Finset.sdiff_subset,
              Finset.card_sdiff_of_subset hIs,Finset.card_range,hm.1]
            omega
          have hsum : (splitLargeProfile (k-2) d ((Finset.range d.length)\I)).sum ≤ k+d.sum :=
            (splitLargeProfile_sum_le _ _ _).trans (Nat.add_le_add_right (by omega) _)
          have he := hs g hgS _ hl (k+d.sum) hsum Y hY
          have hp' : d.length-1=p-2 := by omega
          simpa only [hp',hd] using he
        · rw [if_neg hm,if_neg hm,sub_self,abs_zero]
          positivity
      have hcenter : (∑ I∈(Finset.range d.length).powerset,
          if I.card=2 ∧ ∀j∈I,d[j]! = 0 then (A Y)^2/(complexity g p:ℝ)^2 else 0)=
          (Nat.choose (zeros d) 2:ℝ)*(A Y)^2/(complexity g p:ℝ)^2 := by
        have he := congrArg (fun x : ℝ => x*((A Y)^2/(complexity g p:ℝ)^2)) (sum_zero_pair_subsets d)
        rw [Finset.sum_mul] at he
        convert he using 1
        · apply Finset.sum_congr rfl
          intro I hI
          split_ifs <;> ring
        · ring
      rw [←hcenter,←Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ I∈(Finset.range d.length).powerset,
          |(if I.card=2 ∧ ∀j∈I,d[j]! = 0 then
            (W P g (d.length-1) Y/W P g (d.length+1) Y)*
              profile P g (splitLargeProfile (k-2) d ((Finset.range d.length)\I)) Y else 0)-
            (if I.card=2 ∧ ∀j∈I,d[j]! = 0 then (A Y)^2/(complexity g p:ℝ)^2 else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ I∈(Finset.range d.length).powerset,Cs*((k+d.sum:ℕ)+1:ℝ)^2/(complexity g p:ℝ)^3 :=
          Finset.sum_le_sum hpoint
        _ = _ := by
          simp only [Finset.sum_const,Finset.card_powerset,Finset.card_range,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
          rw [show d.length=p-1 by omega]
          ring
    · rw [if_neg hk,if_neg hk,sub_self,abs_zero]
      positivity
  · refine ⟨1,by norm_num,2,?_⟩
    intro g hg k d hd Y hY
    have hd2 : d.length<2 := by omega
    have hz : zeros d<2 := by
      have he : zeros d ≤ d.length := List.length_filter_le _ _
      omega
    have hchoose : Nat.choose (zeros d) 2=0 := Nat.choose_eq_zero_of_lt hz
    have hzero : (∑ I∈(Finset.range d.length).powerset,
        if I.card=2 ∧ ∀j∈I,d[j]! = 0 then
          (W P g (d.length-1) Y/W P g (d.length+1) Y)*
            profile P g (splitLargeProfile (k-2) d ((Finset.range d.length)\I)) Y else 0)=0 := by
      apply Finset.sum_eq_zero
      intro I hI
      have hc : I.card ≤ d.length := by simpa only [Finset.card_range] using Finset.card_le_card (Finset.mem_powerset.mp hI)
      exact if_neg (by omega)
    rw [secondSeparatingSphere_formula P g k d (by omega) Y hY,hzero,hchoose]
    simp only [Nat.cast_zero,zero_mul,zero_div,ite_self,sub_self,abs_zero]
    positivity
end WP

namespace WP
lemma secondSeparatingTorus_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ k : ℕ,∀ d : List ℕ,d.length+1=p →
      ∀ Y∈Icc (0:ℝ) y₀,
      |secondSeparatingTorus P g k d Y-
        ((if 2 ≤ k then theta Y 1/2 else 0)+(if 3 ≤ k then (1/2:ℝ) else 0))*
          (A Y)^2/(complexity g p:ℝ)^2| ≤
        C*((k+d.sum:ℕ)+1:ℝ)^2/(complexity g p:ℝ)^3 := by
  obtain ⟨Ct,hCt,Gt,ht⟩ := torus_split_profile_leading_uniform P p hp
  obtain ⟨T,hT⟩ := Analysis.theta_uniform_bound
  let B : ℝ := max 1 T
  have hB : 1 ≤ B := le_max_left _ _
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨2*B*Ct,by positivity,max Gt 2,?_⟩
  intro g hg k d hd Y hY
  have hgT : Gt ≤ g := (le_max_left _ _).trans hg
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hnode (s : ℕ) :
      |(W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
        profile P (g-1) (splitLargeProfile (k-s) d (Finset.range d.length)) Y-
          (A Y)^2/(complexity g p:ℝ)^2| ≤
        Ct*((k+d.sum:ℕ)+1:ℝ)^2/(complexity g p:ℝ)^3 := by
    have hl : (splitLargeProfile (k-s) d (Finset.range d.length)).length=p := by
      rw [splitLargeProfile_length _ _ _ (by rfl),Finset.card_range,hd]
    have hsum : (splitLargeProfile (k-s) d (Finset.range d.length)).sum ≤ k+d.sum :=
      (splitLargeProfile_sum_le _ _ _).trans (Nat.add_le_add_right (by omega) _)
    simpa only [hd] using ht g hgT _ hl (k+d.sum) hsum Y hY
  have htheta : |theta Y 1/2| ≤ B := by
    rw [abs_div,abs_of_nonneg (theta_nonneg Y hY 1),abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hu : theta Y 1 ≤ B := (hT Y hY 1).trans (le_max_right _ _)
    linarith
  have h0 : |(if 2 ≤ k then (theta Y 1/2)*
      ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
        profile P (g-1) (splitLargeProfile (k-2) d (Finset.range d.length)) Y) else 0)-
      (if 2 ≤ k then (theta Y 1/2)*((A Y)^2/(complexity g p:ℝ)^2) else 0)| ≤
      B*Ct*((k+d.sum:ℕ)+1:ℝ)^2/(complexity g p:ℝ)^3 := by
    by_cases hk : 2 ≤ k
    · rw [if_pos hk,if_pos hk,←mul_sub,abs_mul]
      have hb := mul_le_mul htheta (hnode 2) (abs_nonneg _) hBp.le
      simpa only [mul_div_assoc,mul_assoc] using hb
    · rw [if_neg hk,if_neg hk,sub_self,abs_zero]
      positivity
  have h1 : |(if 3 ≤ k then (1/2:ℝ)*
      ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
        profile P (g-1) (splitLargeProfile (k-3) d (Finset.range d.length)) Y) else 0)-
      (if 3 ≤ k then (1/2:ℝ)*((A Y)^2/(complexity g p:ℝ)^2) else 0)| ≤
      B*Ct*((k+d.sum:ℕ)+1:ℝ)^2/(complexity g p:ℝ)^3 := by
    by_cases hk : 3 ≤ k
    · rw [if_pos hk,if_pos hk,←mul_sub,abs_mul]
      have hc : |(1/2:ℝ)| ≤ B := by norm_num;linarith
      have hb := mul_le_mul hc (hnode 3) (abs_nonneg _) hBp.le
      simpa only [mul_div_assoc,mul_assoc] using hb
    · rw [if_neg hk,if_neg hk,sub_self,abs_zero]
      positivity
  rw [secondSeparatingTorus_formula P g k d hg2 Y hY]
  have he :
      (if 2 ≤ k then (theta Y 1/2)*
        ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
          profile P (g-1) (splitLargeProfile (k-2) d (Finset.range d.length)) Y) else 0)+
      (if 3 ≤ k then (1/2:ℝ)*
        ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
          profile P (g-1) (splitLargeProfile (k-3) d (Finset.range d.length)) Y) else 0)-
      ((if 2 ≤ k then theta Y 1/2 else 0)+(if 3 ≤ k then (1/2:ℝ) else 0))*
        (A Y)^2/(complexity g p:ℝ)^2=
      ((if 2 ≤ k then (theta Y 1/2)*
        ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
          profile P (g-1) (splitLargeProfile (k-2) d (Finset.range d.length)) Y) else 0)-
        (if 2 ≤ k then (theta Y 1/2)*((A Y)^2/(complexity g p:ℝ)^2) else 0))+
      ((if 3 ≤ k then (1/2:ℝ)*
        ((W P (g-1) (d.length+1) Y/W P g (d.length+1) Y)*
          profile P (g-1) (splitLargeProfile (k-3) d (Finset.range d.length)) Y) else 0)-
        (if 3 ≤ k then (1/2:ℝ)*((A Y)^2/(complexity g p:ℝ)^2) else 0)) := by
    split_ifs <;> ring
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add h0 h1).trans (by ring_nf;exact le_rfl))
end WP
