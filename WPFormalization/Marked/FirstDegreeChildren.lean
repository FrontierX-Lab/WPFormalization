import WPFormalization.Marked.SingleMarkingProfile
import WPFormalization.Weighted.LinearNormalization

/-! Exact signed merger and handle profiles and the real genus normalization of each recursion layer. The proved all-marking quadratic profile estimate controls every child, including excess degree. -/

noncomputable section
open Set Filter
open scoped Topology

namespace WP
lemma normalized_eq_zero_mul_profile (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hn : 1 ≤ d.length) (hs : Stable g d.length) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    normalized P g d Y = normalized P g (List.replicate d.length 0) Y*profile P g d Y := by
  have hz := normalized_pos_valid_nonempty P g (List.replicate d.length 0)
    (by simpa only [List.length_replicate] using hn) (by simpa only [List.length_replicate] using hs) (by simp) Y hY
  unfold profile
  field_simp

lemma normInt_merger_zero_profile (P : PsiTheory) (g t l j : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (hj : j<d.length) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    normInt P g (((t:ℤ)+d[j]!+l-1)::(d.eraseIdx j).map Int.ofNat) Y =
      normalized P g (List.replicate d.length 0) Y *
        (if 1 ≤ t+d[j]!+l then profile P g (mergerProfile t d l j) Y else 0) := by
  let ds := ((t:ℤ)+d[j]!+l-1)::(d.eraseIdx j).map Int.ofNat
  change normInt P g ds Y= _
  by_cases hnode : 1 ≤ t+d[j]!+l
  · have hn : ∀ k ∈ ds, 0 ≤ k := by
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · omega
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hk
        exact Int.natCast_nonneg _
    have he : ds.map Int.toNat=mergerProfile t d l j := by
      dsimp only [ds,mergerProfile]
      simp only [List.map_cons,List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id_fun',id_eq]
      congr 1
      omega
    have hlen : (mergerProfile t d l j).length=d.length := by
      simp only [mergerProfile,List.length_cons,List.length_eraseIdx_of_lt hj]
      omega
    rw [normInt,if_pos hn,he,if_pos hnode]
    have hi := normalized_eq_zero_mul_profile P g (mergerProfile t d l j)
      (by rw [hlen];omega) (by rw [hlen];unfold Stable;omega) Y hY
    simpa only [hlen] using hi
  · have hp : t=0 := by omega
    have hl : l=0 := by omega
    have hdj : d[j]! = 0 := by omega
    have hn : ¬∀ k ∈ ds, 0 ≤ k := by
      intro hall
      have hi := hall (-1) (by simp [ds,hp,hl,hdj])
      omega
    simp only [normInt,if_neg hn,if_neg hnode,mul_zero]

lemma normInt_handle_zero_profile (P : PsiTheory) (g t l u : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (hu : u ∈ Finset.range (t+l-1)) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    normInt P (g-1) ((u:ℤ)::((t:ℤ)+l-2-u)::d.map Int.ofNat) Y =
      normalized P (g-1) (List.replicate (d.length+2) 0) Y *
        profile P (g-1) (contractionProfile t d l u) Y := by
  let ds := (u:ℤ)::((t:ℤ)+l-2-u)::d.map Int.ofNat
  have hu' := Finset.mem_range.mp hu
  have hn : ∀ k ∈ ds, 0 ≤ k := by
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · positivity
    · rcases List.mem_cons.mp hk with rfl | hk
      · omega
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hk
        exact Int.natCast_nonneg _
  have he : ds.map Int.toNat=contractionProfile t d l u := by
    dsimp only [ds,contractionProfile]
    simp only [List.map_cons,List.map_map,Function.comp_def,Int.ofNat_eq_natCast,Int.toNat_natCast,List.map_id_fun',id_eq]
    congr 1
    congr 1
    omega
  have hlen : (contractionProfile t d l u).length=d.length+2 := by simp [contractionProfile]
  change normInt P (g-1) ds Y= _
  rw [normInt,if_pos hn,he]
  have hi := normalized_eq_zero_mul_profile P (g-1) (contractionProfile t d l u)
    (by rw [hlen];omega) (by rw [hlen];unfold Stable;omega) Y hY
  simpa only [hlen] using hi
end WP
namespace WP
lemma normalizedChildren_scaled_decomposition (P : PsiTheory) (g t l : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    (4:ℝ)^g*normalizedChildren P g (t+l) (d.map Int.ofNat) Y/W P g (d.length+1) Y =
      (W P g d.length Y/W P g (d.length+1) Y)*
        (∑ j ∈ Finset.range d.length, (2*(d[j]!:ℝ)+1)*
          (if 1 ≤ t+d[j]!+l then profile P g (mergerProfile t d l j) Y else 0)) +
      2*(W P (g-1) (d.length+2) Y/W P g (d.length+1) Y)*
        (∑ u ∈ Finset.range (t+l-1), profile P (g-1) (contractionProfile t d l u) Y) +
      (1/2:ℝ)*(4:ℝ)^g*
        (∑ u ∈ Finset.range (t+l-1), ∑ j ∈ Finset.range (g+1),
          ∑ I ∈ (Finset.range d.length).powerset,
            normInt P j ((u:ℤ)::selected (d.map Int.ofNat) I) Y *
            normInt P (g-j) (((t:ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length) \ I)) Y)/
        W P g (d.length+1) Y := by
  rw [normalizedChildren_as_normInt,if_neg (by omega : g≠0)]
  simp only [List.length_map]
  rw [mul_add,mul_add,add_div,add_div]
  apply congrArg₂ (fun a b : ℝ => a+b)
  · apply congrArg₂ (fun a b : ℝ => a+b)
    · rw [Finset.mul_sum,Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hget : (d.map Int.ofNat)[j]! = (d[j]!:ℤ) := by simp [hj']
      rw [hget,List.eraseIdx_map]
      have hi := normInt_merger_zero_profile P g t l j d hg hj' Y hY
      rw [show ((t+l:ℕ):ℤ)+(d[j]!:ℤ)-1=(t:ℤ)+d[j]!+l-1 by push_cast;ring,hi]
      unfold W
      simp only [Int.cast_natCast]
      ring
    · rw [←mul_assoc,Finset.mul_sum,Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have hi := normInt_handle_zero_profile P g t l u d hg hu Y hY
      rw [show ((t+l:ℕ):ℤ)-2-u=(t:ℤ)+l-2-u by push_cast;ring,hi]
      have hpow : (4:ℝ)^g=4*(4:ℝ)^(g-1) := by rw [←pow_succ',Nat.sub_add_cancel (by omega : 1≤g)]
      unfold W
      rw [hpow]
      ring
  · simp only [Nat.cast_add]
    ring
end WP
namespace WP
lemma normalizedChildren_separating_bound (P : PsiTheory) (g t l : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    0 ≤ (1/2:ℝ)*(4:ℝ)^g*
      (∑ u ∈ Finset.range (t+l-1), ∑ j ∈ Finset.range (g+1),
        ∑ I ∈ (Finset.range d.length).powerset,
          normInt P j ((u:ℤ)::selected (d.map Int.ofNat) I) Y *
          normInt P (g-j) (((t:ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length) \ I)) Y)/
      W P g (d.length+1) Y ∧
    (1/2:ℝ)*(4:ℝ)^g*
      (∑ u ∈ Finset.range (t+l-1), ∑ j ∈ Finset.range (g+1),
        ∑ I ∈ (Finset.range d.length).powerset,
          normInt P j ((u:ℤ)::selected (d.map Int.ofNat) I) Y *
          normInt P (g-j) (((t:ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length) \ I)) Y)/
      W P g (d.length+1) Y ≤ ((t+l+1:ℕ):ℝ)/2*separatingS P g (d.length+1) Y := by
  have hW : 0<W P g (d.length+1) Y := W_pos P g _ (by omega) (by unfold Stable;omega) Y hY
  have hraw0 : 0 ≤ ∑ u ∈ Finset.range (t+l-1), ∑ j ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        normInt P j ((u:ℤ)::selected (d.map Int.ofNat) I) Y *
        normInt P (g-j) (((t:ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length) \ I)) Y := by
    apply Finset.sum_nonneg;intro u hu
    apply Finset.sum_nonneg;intro j hj
    apply Finset.sum_nonneg;intro I hI
    exact mul_nonneg (normInt_nonneg_profile P j _ (by simp) Y hY)
      (normInt_nonneg_profile P (g-j) _ (by simp) Y hY)
  refine ⟨div_nonneg (by positivity) hW.le,?_⟩
  let Z := ∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (d.length+1),
      (d.length.choose s:ℝ)*normalized P j (List.replicate (s+1) 0) Y *
        normalized P (g-j) (List.replicate (d.length-s+1) 0) Y
  have hZ : 0 ≤ Z := by
    apply Finset.sum_nonneg;intro j hj
    apply Finset.sum_nonneg;intro s hs
    exact mul_nonneg (mul_nonneg (by positivity) (normalized_nonneg_nonempty P j _ (by simp) Y hY))
      (normalized_nonneg_nonempty P (g-j) _ (by simp) Y hY)
  have hraw : (∑ u ∈ Finset.range (t+l-1), ∑ j ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        normInt P j ((u:ℤ)::selected (d.map Int.ofNat) I) Y *
        normInt P (g-j) (((t:ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length) \ I)) Y) ≤ ((t+l+1:ℕ):ℝ)*Z := by
    calc _ ≤ ∑ u ∈ Finset.range (t+l-1), Z := by
           apply Finset.sum_le_sum
           intro u hu
           simpa only [List.length_map,Nat.cast_add] using zero_profile_split_sum P g (d.map Int.ofNat) u (t+l) Y hY
         _ = ((t+l-1:ℕ):ℝ)*Z := by simp
         _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show t+l-1 ≤ t+l+1 by omega)) hZ
  have hroot := W_zero_split_identity P g d.length (by omega) Y hY
  change (4:ℝ)^g*Z=W P g (d.length+1) Y*separatingS P g (d.length+1) Y at hroot
  calc _ ≤ ((1/2:ℝ)*(4:ℝ)^g*(((t+l+1:ℕ):ℝ)*Z))/W P g (d.length+1) Y := by
         apply div_le_div_of_nonneg_right _ hW.le
         exact mul_le_mul_of_nonneg_left hraw (by positivity)
       _ = (((t+l+1:ℕ):ℝ)/2)*((4:ℝ)^g*Z)/W P g (d.length+1) Y := by ring
       _ = _ := by rw [hroot];field_simp
end WP
namespace WP
lemma merger_child_quadratic_uniform (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ Q : ℝ, 0<Q ∧ ∀ g : ℕ, 2 ≤ g → ∀ t : ℕ, ∀ d : List ℕ, (t::d).length=p →
      ∀ l j : ℕ, j<d.length → ∀ Y ∈ Icc (0:ℝ) y₀,
      |(if 1 ≤ t+d[j]!+l then profile P g (mergerProfile t d l j) Y else 0)-
        (if 1 ≤ t+d[j]!+l then 1 else 0)| ≤
      Q*(((t::d).sum:ℝ)+l+1)^2/(complexity g p:ℝ) := by
  obtain ⟨Q,hQ,hquad⟩ := quadratic_profile_all_markings_proof P (p-1) (by omega)
  let C : ℝ := (2*(p+2):ℕ)
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨Q*C,by positivity,?_⟩
  intro g hg t d hd l j hj Y hY
  have hh : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  by_cases hn : 1 ≤ t+d[j]!+l
  · rw [if_pos hn,if_pos hn,abs_sub_comm]
    have hlen : (mergerProfile t d l j).length=p-1 := by
      simp only [mergerProfile,List.length_cons,List.length_eraseIdx_of_lt hj]
      simp only [List.length_cons] at hd
      omega
    have hsum : (mergerProfile t d l j).sum ≤ (t::d).sum+l := by
      have hs : d[j]!+(d.eraseIdx j).sum=d.sum := by simpa [hj] using (List.getElem_cons_eraseIdx_perm hj).sum_eq
      simp only [mergerProfile,List.sum_cons]
      omega
    have hb := hquad g (by omega) (mergerProfile t d l j) hlen Y hY
    rw [abs_of_nonneg hb.1]
    have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
    have hsize : (complexity g p:ℝ) ≤ C*(g:ℝ) := by
      dsimp [C]
      have hbase : complexity g p ≤ 2*g+p := by unfold complexity;omega
      have hmul : p ≤ p*g := by simpa using Nat.mul_le_mul_left p (show 1≤g by omega)
      exact_mod_cast hbase.trans (show 2*g+p ≤ (2*(p+2))*g by nlinarith)
    calc _ ≤ Q*((mergerProfile t d l j).sum:ℝ)*((mergerProfile t d l j).sum+1)/(g:ℝ) := hb.2
         _ ≤ Q*(((t::d).sum:ℝ)+l+1)^2/(g:ℝ) := by
           apply div_le_div_of_nonneg_right _ hgp.le
           have hs : ((mergerProfile t d l j).sum:ℝ) ≤ ((t::d).sum:ℝ)+l := by exact_mod_cast hsum
           have hs0 : (0:ℝ) ≤ (mergerProfile t d l j).sum := Nat.cast_nonneg _
           have hB0 : (0:ℝ) ≤ ((t::d).sum:ℝ)+l := by positivity
           nlinarith [mul_nonneg hQ.le (show 0 ≤ (((t::d).sum:ℝ)+l+1)^2-
             ((mergerProfile t d l j).sum:ℝ)*((mergerProfile t d l j).sum+1) by nlinarith)]
         _ ≤ _ := by
           apply (div_le_div_iff₀ hgp hh).2
           calc _ ≤ (Q*(((t::d).sum:ℝ)+l+1)^2)*(C*(g:ℝ)) :=
                  mul_le_mul_of_nonneg_left hsize (by positivity)
                _ = _ := by ring
  · rw [if_neg hn,if_neg hn,sub_self,abs_zero]
    positivity

lemma handle_child_quadratic_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ Q : ℝ, 0<Q ∧ ∀ g : ℕ, 2 ≤ g → ∀ t : ℕ, ∀ d : List ℕ, (t::d).length=p →
      ∀ l u : ℕ, u∈Finset.range (t+l-1) → ∀ Y ∈ Icc (0:ℝ) y₀,
      |1-profile P (g-1) (contractionProfile t d l u) Y| ≤
      Q*(((t::d).sum:ℝ)+l+1)^2/(complexity g p:ℝ) := by
  obtain ⟨Q,hQ,hquad⟩ := quadratic_profile_all_markings_proof P (p+1) (by omega)
  let C : ℝ := (2*(p+2):ℕ)
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨Q*C,by positivity,?_⟩
  intro g hg t d hd l u hu Y hY
  have hh : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hlen : (contractionProfile t d l u).length=p+1 := by
    simp only [contractionProfile,List.length_cons]
    simp only [List.length_cons] at hd
    omega
  have hsum : (contractionProfile t d l u).sum ≤ (t::d).sum+l := by
    have hu' := Finset.mem_range.mp hu
    simp only [contractionProfile,List.sum_cons]
    omega
  have hb := hquad (g-1) (by omega) (contractionProfile t d l u) hlen Y hY
  rw [abs_of_nonneg hb.1]
  have hgp : (0:ℝ)<(g-1:ℕ) := by exact_mod_cast (show 0<g-1 by omega)
  have hsize : (complexity g p:ℝ) ≤ C*(g-1:ℕ) := by
    dsimp [C]
    have hbase : complexity g p ≤ 2*g+p := by unfold complexity;omega
    have hmul : p ≤ p*(g-1) := by simpa using Nat.mul_le_mul_left p (show 1≤g-1 by omega)
    have hsub : g-1+1=g := by omega
    exact_mod_cast hbase.trans (show 2*g+p ≤ (2*(p+2))*(g-1) by nlinarith)
  calc _ ≤ Q*((contractionProfile t d l u).sum:ℝ)*((contractionProfile t d l u).sum+1)/(g-1:ℕ) := hb.2
       _ ≤ Q*(((t::d).sum:ℝ)+l+1)^2/(g-1:ℕ) := by
         apply div_le_div_of_nonneg_right _ hgp.le
         have hs : ((contractionProfile t d l u).sum:ℝ) ≤ ((t::d).sum:ℝ)+l := by exact_mod_cast hsum
         have hs0 : (0:ℝ) ≤ (contractionProfile t d l u).sum := Nat.cast_nonneg _
         have hB0 : (0:ℝ) ≤ ((t::d).sum:ℝ)+l := by positivity
         nlinarith [mul_nonneg hQ.le (show 0 ≤ (((t::d).sum:ℝ)+l+1)^2-
           ((contractionProfile t d l u).sum:ℝ)*((contractionProfile t d l u).sum+1) by nlinarith)]
       _ ≤ _ := by
         apply (div_le_div_iff₀ hgp hh).2
         calc _ ≤ (Q*(((t::d).sum:ℝ)+l+1)^2)*(C*(g-1:ℕ)) :=
                mul_le_mul_of_nonneg_left hsize (by positivity)
              _ = _ := by ring
end WP
namespace WP
lemma merger_child_quadratic_uniform_all (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ Q : ℝ, 0<Q ∧ ∀ g : ℕ, 2 ≤ g → ∀ t : ℕ, ∀ d : List ℕ, (t::d).length=p →
      ∀ l j : ℕ, j<d.length → ∀ Y ∈ Icc (0:ℝ) y₀,
      |(if 1 ≤ t+d[j]!+l then profile P g (mergerProfile t d l j) Y else 0)-
        (if 1 ≤ t+d[j]!+l then 1 else 0)| ≤
      Q*(((t::d).sum:ℝ)+l+1)^2/(complexity g p:ℝ) := by
  by_cases hp1 : p=1
  · subst p
    refine ⟨1,by norm_num,?_⟩
    intro g hg t d hd l j hj Y hY
    simp only [List.length_cons] at hd
    omega
  · exact merger_child_quadratic_uniform P p (by omega)
end WP
