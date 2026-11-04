import WPFormalization.Statements.MarkedCusp
import WPFormalization.Statements.QuadraticProfile
/-! The one-marking extension in (6.17)–(6.18). The inverse cusp ratio
controls the handle term and transfers the true two-marking separating
bound to one marking. The same degree induction then extends the quadratic
profile estimate to every positive marking count. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP
lemma singleMarking_A_uniform_lower : ∃ a₀ : ℝ, 0<a₀ ∧ ∀ Y ∈ Icc (0:ℝ) y₀, a₀ ≤ A Y := by
  let S := Icc (0:ℝ) y₀
  have hc : Continuous (fun Y : S => A (Y:ℝ)) := by
    exact (Complex.continuous_re.comp (Analysis.barH_joint_continuous.comp
      (continuous_id.prodMk continuous_const))).div_const 3
  have hS : (univ : Set S).Nonempty := ⟨⟨0,le_rfl,y₀_pos.le⟩,mem_univ _⟩
  obtain ⟨Ymin,_,hmin⟩ := isCompact_univ.exists_isMinOn (f := fun Y:S => A (Y:ℝ)) hS hc.continuousOn
  refine ⟨A Ymin,?_,?_⟩
  · exact div_pos (Analysis.barH_one_re_pos Ymin Ymin.property) (by norm_num)
  · intro Y hY
    exact (isMinOn_iff.mp hmin) (⟨Y,hY⟩:S) (mem_univ _)

lemma W_one_cusp_inverse_uniform (P : PsiTheory) : ∃ C : ℝ, 0<C ∧ ∃ G : ℕ,
    ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀, W P g 2 Y ≤ C*(g:ℝ)*W P g 1 Y := by
  obtain ⟨a₀,ha₀,hA⟩ := singleMarking_A_uniform_lower
  obtain ⟨C,hC,g₀,hstep⟩ := marked_cusp P 1 (by omega)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*C/a₀)
  refine ⟨4/a₀,by positivity,max 2 (max g₀ N),?_⟩
  intro g hg Y hY
  have hg₂ : 2 ≤ g := (le_max_left _ _).trans hg
  have hgg : g₀ ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgN : N ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hN' : (2*C)/a₀ < (g:ℝ) := hN.trans_le (by exact_mod_cast hgN)
  have hsmall : C/(g:ℝ) ≤ a₀/2 := by
    apply (div_le_iff₀ hgp).2
    have hi := (div_lt_iff₀ ha₀).mp hN'
    nlinarith
  have hrat := (abs_le.mp (hstep g hgg Y hY)).1
  have hW1 : 0<W P g 1 Y := W_pos P g 1 (by omega) (by unfold Stable;omega) Y hY
  have hW2 : 0<W P g 2 Y := W_pos P g 2 (by omega) (by unfold Stable;omega) Y hY
  have hlo : a₀/2 ≤ (complexity g 1:ℝ)*W P g 1 Y/W P g 2 Y := by
    have hi := hA Y hY
    norm_num only [Nat.reduceAdd] at hrat
    linarith
  have hi := (le_div_iff₀ hW2).mp hlo
  have hh : (complexity g 1:ℝ) ≤ 2*(g:ℝ) := by exact_mod_cast (show complexity g 1 ≤ 2*g by unfold complexity;omega)
  have hprod := mul_le_mul_of_nonneg_right hh hW1.le
  rw [show 4/a₀*(g:ℝ)*W P g 1 Y = (4*(g:ℝ)*W P g 1 Y)/a₀ by ring]
  apply (le_div_iff₀ ha₀).2
  nlinarith

lemma W_one_to_two_cusp (C : ℝ)
    (hcusp : ∀ P : PsiTheory, ∀ g p : ℕ, Stable g p → ∀ Y ∈ Icc (0:ℝ) y₀,
      (complexity g p:ℝ)*W P g p Y ≤ C*W P g (p+1) Y)
    (P : PsiTheory) (g : ℕ) (hg : 1 ≤ g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    (g:ℝ)*W P g 1 Y ≤ C*W P g 2 Y := by
  have hh : (g:ℝ) ≤ complexity g 1 := by exact_mod_cast (show g ≤ complexity g 1 by unfold complexity;omega)
  exact (mul_le_mul_of_nonneg_right hh (W_nonneg P g 1 (by omega) Y hY)).trans
    (hcusp P g 1 (by unfold Stable;omega) Y hY)

lemma W_one_nonsep_uniform (P : PsiTheory) : ∃ C : ℝ, 0<C ∧ ∃ G : ℕ,
    ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      (g:ℝ)*W P (g-1) 2 Y ≤ C*W P g 1 Y := by
  obtain ⟨Cr,hCr,hcusp⟩ := W_cusp_uniform_bound
  obtain ⟨Ci,hCi,G,hInv⟩ := W_one_cusp_inverse_uniform P
  refine ⟨Cr^2*Ci,by positivity,max 2 G,?_⟩
  intro g hg Y hY
  have hg₂ : 2 ≤ g := (le_max_left _ _).trans hg
  have hgG : G ≤ g := (le_max_right _ _).trans hg
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hstep (q : ℕ) (hq : 2 ≤ q) :
      (g:ℝ)*W P (g-1) q Y ≤ Cr*W P (g-1) (q+1) Y := by
    have hh : (g:ℝ) ≤ complexity (g-1) q := by exact_mod_cast (show g ≤ complexity (g-1) q by unfold complexity;omega)
    exact (mul_le_mul_of_nonneg_right hh (W_nonneg P (g-1) q (by omega) Y hY)).trans
      (hcusp P (g-1) q (by unfold Stable;omega) Y hY)
  have hi : (g:ℝ)*((g:ℝ)*W P (g-1) 2 Y) ≤ (g:ℝ)*(Cr^2*Ci*W P g 1 Y) := by
    calc _ ≤ (g:ℝ)*(Cr*W P (g-1) 3 Y) := mul_le_mul_of_nonneg_left (hstep 2 (by omega)) hgp.le
         _ = Cr*((g:ℝ)*W P (g-1) 3 Y) := by ring
         _ ≤ Cr*(Cr*W P (g-1) 4 Y) := mul_le_mul_of_nonneg_left (hstep 3 (by omega)) hCr.le
         _ ≤ Cr*(Cr*W P g 2 Y) := by gcongr;exact W_genus_exchange_le P g 2 (by omega) (by omega) Y hY
         _ ≤ Cr*(Cr*(Ci*(g:ℝ)*W P g 1 Y)) := by gcongr;exact hInv g hgG Y hY
         _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hgp).mp (by simpa only [mul_comm (g:ℝ)] using hi)
end WP
namespace WP
lemma W_unstable_zero_single (P : PsiTheory) (g p : ℕ) (hs : ¬ Stable g p) (Y : ℝ) : W P g p Y=0 := by
  unfold W
  rw [normalized_unstable P g _ Y (by simpa only [List.length_replicate] using hs),mul_zero]

lemma separatingS_one_term_bound (C : ℝ) (hC : 0 ≤ C)
    (hcusp : ∀ P : PsiTheory, ∀ g p : ℕ, Stable g p → ∀ Y ∈ Icc (0:ℝ) y₀,
      (complexity g p:ℝ)*W P g p Y ≤ C*W P g (p+1) Y)
    (P : PsiTheory) (g j : ℕ) (hg : 2 ≤ g) (hj : j ≤ g)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    (g:ℝ)*(W P j 1 Y*W P (g-j) 1 Y) ≤ 2*C^2*(W P j 2 Y*W P (g-j) 2 Y) := by
  by_cases hz : j=0 ∨ g-j=0
  · rcases hz with hz | hz
    · subst j
      rw [W_unstable_zero_single P 0 1 (by norm_num [Stable]) Y,zero_mul,mul_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (W_nonneg P 0 2 (by omega) Y hY) (W_nonneg P (g-0) 2 (by omega) Y hY))
    · rw [hz,W_unstable_zero_single P 0 1 (by norm_num [Stable]) Y,mul_zero,mul_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (W_nonneg P j 2 (by omega) Y hY) (W_nonneg P 0 2 (by omega) Y hY))
  · have hj₁ : 1 ≤ j := by omega
    have hj₂ : 1 ≤ g-j := by omega
    have hjR : (1:ℝ) ≤ j := by exact_mod_cast hj₁
    have hkR : (1:ℝ) ≤ (g-j:ℕ) := by exact_mod_cast hj₂
    have hsum : (j:ℝ)+(g-j:ℕ)=g := by exact_mod_cast (Nat.add_sub_of_le hj)
    have hcost : (g:ℝ) ≤ 2*(j:ℝ)*(g-j:ℕ) := by
      have hgR : (2:ℝ) ≤ g := by exact_mod_cast hg
      nlinarith [mul_nonneg (sub_nonneg.mpr hjR) (sub_nonneg.mpr hkR)]
    have h₁ := W_one_to_two_cusp C hcusp P j hj₁ Y hY
    have h₂ := W_one_to_two_cusp C hcusp P (g-j) hj₂ Y hY
    have hprod := mul_le_mul h₁ h₂
      (mul_nonneg (Nat.cast_nonneg _) (W_nonneg P (g-j) 1 (by omega) Y hY))
      (mul_nonneg hC (W_nonneg P j 2 (by omega) Y hY))
    calc _ ≤ (2*(j:ℝ)*(g-j:ℕ))*(W P j 1 Y*W P (g-j) 1 Y) :=
           mul_le_mul_of_nonneg_right hcost (mul_nonneg (W_nonneg P j 1 (by omega) Y hY) (W_nonneg P (g-j) 1 (by omega) Y hY))
         _ = 2*(((j:ℝ)*W P j 1 Y)*((g-j:ℕ)*W P (g-j) 1 Y)) := by ring
         _ ≤ 2*((C*W P j 2 Y)*(C*W P (g-j) 2 Y)) := mul_le_mul_of_nonneg_left hprod (by norm_num)
         _ = _ := by ring

lemma separatingS_one_uniform (P : PsiTheory) : ∃ C : ℝ, 0<C ∧ ∃ G : ℕ,
    ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀, separatingS P g 1 Y ≤ C/(g:ℝ) := by
  obtain ⟨Cr,hCr,hcusp⟩ := W_cusp_uniform_bound
  obtain ⟨Ci,hCi,Gi,hInv⟩ := W_one_cusp_inverse_uniform P
  obtain ⟨Ct,hCt,Gt,hT⟩ := separating_estimates P 2 (by omega)
  refine ⟨2*Cr^2*Ci*Ct,by positivity,max 2 (max Gi Gt),?_⟩
  intro g hg Y hY
  have hg₂ : 2 ≤ g := (le_max_left _ _).trans hg
  have hgi : Gi ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgt : Gt ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hW1 : 0<W P g 1 Y := W_pos P g 1 (by omega) (by unfold Stable;omega) Y hY
  have hW2 : 0<W P g 2 Y := W_pos P g 2 (by omega) (by unfold Stable;omega) Y hY
  have hs : separatingS P g 1 Y=(∑ j ∈ Finset.range (g+1), W P j 1 Y*W P (g-j) 1 Y)/W P g 1 Y := by
    simp [separatingS]
  have ht : separatingT P g 2 Y=(∑ j ∈ Finset.range (g+1), W P j 2 Y*W P (g-j) 2 Y)/W P g 2 Y := by
    simp [separatingT]
  have hb : (∑ j ∈ Finset.range (g+1), W P j 2 Y*W P (g-j) 2 Y) ≤ Ci*Ct*W P g 1 Y := by
    have hTbound : separatingT P g 2 Y ≤ Ct/(g:ℝ) := (le_abs_self _).trans (hT g hgt Y hY).2
    rw [ht] at hTbound
    have hsum := (div_le_iff₀ hW2).mp hTbound
    calc _ ≤ (Ct/(g:ℝ))*W P g 2 Y := hsum
         _ ≤ (Ct/(g:ℝ))*(Ci*(g:ℝ)*W P g 1 Y) :=
           mul_le_mul_of_nonneg_left (hInv g hgi Y hY) (by positivity)
         _ = _ := by field_simp
  have hsum : (g:ℝ)*(∑ j ∈ Finset.range (g+1), W P j 1 Y*W P (g-j) 1 Y) ≤
      (2*Cr^2)* (∑ j ∈ Finset.range (g+1), W P j 2 Y*W P (g-j) 2 Y) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact separatingS_one_term_bound Cr hCr.le hcusp P g j hg₂ (by have := Finset.mem_range.mp hj;omega) Y hY
  rw [hs]
  apply (div_le_div_iff₀ hW1 hgp).2
  calc _ ≤ _ := by simpa only [mul_comm (g:ℝ)] using hsum
       _ ≤ (2*Cr^2)*(Ci*Ct*W P g 1 Y) := mul_le_mul_of_nonneg_left hb (by positivity)
       _ = _ := by ring
end WP
namespace WP
lemma normalizedChildren_one_uniform_from_ratios (P : PsiTheory) (g k l : ℕ)
    (hg : 2 ≤ g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) (Cn Cs : ℝ) (hCn : 0 ≤ Cn) (hCs : 0 ≤ Cs)
    (hhandle : (g:ℝ)*W P (g-1) 2 Y ≤ Cn*W P g 1 Y)
    (hsep : separatingS P g 1 Y ≤ Cs/(g:ℝ)) :
    (4:ℝ)^g * normalizedChildren P g (k+l) [] Y / W P g 1 Y ≤
      (2*Cn+Cs)*((k:ℝ)+1)*(1+(l:ℝ))/(g:ℝ) := by
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hw : 0<W P g 1 Y := W_pos P g 1 (by omega) (by unfold Stable;omega) Y hY
  have hh : W P (g-1) 2 Y / W P g 1 Y ≤ Cn/(g:ℝ) := by
    apply (div_le_div_iff₀ hw hgp).2
    simpa only [mul_comm (g:ℝ)] using hhandle
  have hc := normalizedChildren_W_bound P g (k+l) [] (by omega) Y hY
  simp only [List.sum_nil,List.length_nil,List.map_nil,Nat.cast_zero,mul_zero,zero_mul,zero_add] at hc
  have hc' : (4:ℝ)^g * normalizedChildren P g (k+l) [] Y / W P g 1 Y ≤
      2*((k+l+1:ℕ):ℝ)*(W P (g-1) 2 Y / W P g 1 Y)+
      ((k+l+1:ℕ):ℝ)/2*separatingS P g 1 Y := by
    convert div_le_div_of_nonneg_right hc hw.le using 1 <;> field_simp <;> ring
  let F : ℝ := ((k:ℝ)+1)*(1+(l:ℝ))
  have hF : ((k+l+1:ℕ):ℝ) ≤ F := by
    dsimp [F]
    push_cast
    nlinarith [mul_nonneg (show (0:ℝ)≤k from Nat.cast_nonneg _) (show (0:ℝ)≤l from Nat.cast_nonneg _)]
  have hF0 : 0 ≤ F := by dsimp [F];positivity
  calc
    _ ≤ 2*((k+l+1:ℕ):ℝ)*(Cn/(g:ℝ))+((k+l+1:ℕ):ℝ)/2*(Cs/(g:ℝ)) :=
      hc'.trans (add_le_add (mul_le_mul_of_nonneg_left hh (by positivity))
        (mul_le_mul_of_nonneg_left hsep (by positivity)))
    _ = (2*((k+l+1:ℕ):ℝ)*Cn+((k+l+1:ℕ):ℝ)/2*Cs)/(g:ℝ) := by ring
    _ ≤ (2*F*Cn+F*Cs)/(g:ℝ) := by
      apply div_le_div_of_nonneg_right _ hgp.le
      exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF (by norm_num)) hCn)
        (mul_le_mul_of_nonneg_right (by linarith : ((k+l+1:ℕ):ℝ)/2 ≤ F) hCs)
    _ = _ := by dsimp [F];ring

lemma profile_adjacent_one_uniform_bound (P : PsiTheory) : ∃ C : ℝ, 0<C ∧
    ∀ g : ℕ, 1 ≤ g → ∀ k : ℕ, ∀ Y ∈ Icc (0:ℝ) y₀,
      profile P g [k] Y-profile P g [k+1] Y ≤ C*((k:ℝ)+1)/(g:ℝ) := by
  obtain ⟨Cn,hCn,Gn,hHandle⟩ := W_one_nonsep_uniform P
  obtain ⟨Cs,hCs,Gs,hSep⟩ := separatingS_one_uniform P
  obtain ⟨M,hM⟩ := uniform_kernel_moments.2 1
  let B : ℝ := max 1 M
  have hB : 0<B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let K : ℝ := 2*Cn+Cs
  have hK : 0<K := by dsimp [K];positivity
  let G : ℕ := max 2 (max Gn Gs)
  let C : ℝ := max (K*B) G
  have hC : 0<C := lt_of_lt_of_le (mul_pos hK hB) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro g hg k Y hY
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  by_cases hlarge : G ≤ g
  · have hg₂ : 2 ≤ g := (le_max_left _ _).trans hlarge
    have hgn : Gn ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
    have hgs : Gs ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
    by_cases had : [k].sum ≤ dimension g 1
    · rw [profile_adjacent_degree_difference P g k [] hg Y hY (by unfold complexity;simp;omega)
        (by simpa only [List.length_nil,Nat.zero_add] using had)]
      have hsum : ∑ l ∈ Finset.range (deficit g [k]+1), (1+(l:ℝ))*weight Y l ≤ B := by
        have hm := hM Y hY
        simp only [pow_one] at hm
        exact ((hm.1.sum_le_tsum _ (fun l _ => mul_nonneg (by positivity) (weight_nonneg Y hY l))).trans hm.2).trans
          (le_max_right _ _)
      calc
        _ ≤ ∑ l ∈ Finset.range (deficit g [k]+1), weight Y l *
            (K*((k:ℝ)+1)*(1+(l:ℝ))/(g:ℝ)) := by
          apply Finset.sum_le_sum
          intro l hl
          apply mul_le_mul_of_nonneg_left _ (weight_nonneg Y hY l)
          simpa only [K,List.map_nil,List.length_nil,Nat.zero_add] using
            normalizedChildren_one_uniform_from_ratios P g k l hg₂ Y hY Cn Cs hCn.le hCs.le
              (hHandle g hgn Y hY) (hSep g hgs Y hY)
        _ = (K*((k:ℝ)+1)/(g:ℝ))* ∑ l ∈ Finset.range (deficit g [k]+1), (1+(l:ℝ))*weight Y l := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          ring
        _ ≤ (K*((k:ℝ)+1)/(g:ℝ))*B := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ ≤ C*((k:ℝ)+1)/(g:ℝ) := by
          calc _ = K*B*(((k:ℝ)+1)/(g:ℝ)) := by ring
               _ ≤ C*(((k:ℝ)+1)/(g:ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
               _ = _ := by ring
    · have hz₀ : normalized P g [k] Y=0 := normalized_excess P g _ Y (by simpa only [List.length_singleton] using Nat.lt_of_not_ge had)
      have hz₁ : normalized P g [k+1] Y=0 := normalized_excess P g _ Y (by simp only [List.length_singleton,List.sum_singleton] at *;omega)
      simp only [profile,hz₀,hz₁,zero_div,sub_self]
      positivity
  · have hst : Stable g 1 := by unfold Stable;omega
    have hbound₀ := normalized_profile_bounds P g [k] (by simpa using hst) (by simp) Y hY
    have hbound₁ := normalized_profile_bounds P g [k+1] (by simpa using hst) (by simp) Y hY
    have hgG : (g:ℝ) ≤ (G:ℝ) := by exact_mod_cast (show g ≤ G by omega)
    have hCg : (g:ℝ) ≤ C := hgG.trans (le_max_right _ _)
    have he : 1 ≤ C*((k:ℝ)+1)/(g:ℝ) := by
      apply (le_div_iff₀ hgp).2
      have hD : (1:ℝ) ≤ (k:ℝ)+1 := by linarith [show (0:ℝ)≤k from Nat.cast_nonneg _]
      have hi := mul_le_mul_of_nonneg_left hD hC.le
      linarith
    exact (show profile P g [k] Y-profile P g [k+1] Y ≤ 1 by
      change normalized P g [k] Y/normalized P g (List.replicate [k].length 0) Y-
        normalized P g [k+1] Y/normalized P g (List.replicate [k+1].length 0) Y ≤ 1
      linarith [hbound₀.2,hbound₁.1]).trans he

lemma quadratic_profile_one_proof (P : PsiTheory) : ∃ C : ℝ, 0<C ∧
    ∀ g : ℕ, 1 ≤ g → ∀ d : List ℕ, d.length=1 → ∀ Y ∈ Icc (0:ℝ) y₀,
      0 ≤ 1-profile P g d Y ∧ 1-profile P g d Y ≤ C*(d.sum:ℝ)*(d.sum+1)/(g:ℝ) := by
  obtain ⟨C,hC,hstep⟩ := profile_adjacent_one_uniform_bound P
  refine ⟨C,hC,?_⟩
  intro g hg d hd Y hY
  apply profile_quadratic_of_adjacent P g 1 (by omega) (by unfold Stable;omega) (by omega) Y hY C hC.le
    (fun k e he => ?_) d hd
  have he' : e=[] := List.eq_nil_of_length_eq_zero (by simpa only [List.length_cons] using Nat.succ.inj he)
  subst e
  simpa only [List.sum_singleton] using hstep g hg k Y hY

lemma quadratic_profile_all_markings_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∀ g : ℕ, 1 ≤ g → ∀ d : List ℕ, d.length=p →
    ∀ Y ∈ Icc (0:ℝ) y₀, 0 ≤ 1-profile P g d Y ∧
      1-profile P g d Y ≤ C*(d.sum:ℝ)*(d.sum+1)/(g:ℝ) := by
  by_cases hp1 : p=1
  · subst p;exact quadratic_profile_one_proof P
  · exact quadratic_profile_proof P p (by omega)
end WP
namespace WP
lemma separatingS_one_le_multiple_T (C Ci : ℝ) (hC : 0 ≤ C) (hCi : 0 ≤ Ci)
    (hcusp : ∀ P : PsiTheory, ∀ g p : ℕ, Stable g p → ∀ Y ∈ Icc (0:ℝ) y₀,
      (complexity g p:ℝ)*W P g p Y ≤ C*W P g (p+1) Y)
    (P : PsiTheory) (g : ℕ) (hg : 2 ≤ g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀)
    (hInv : W P g 2 Y ≤ Ci*(g:ℝ)*W P g 1 Y) :
    separatingS P g 1 Y ≤ (2*C^2*Ci)*separatingT P g 2 Y := by
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hW1 : 0<W P g 1 Y := W_pos P g 1 (by omega) (by unfold Stable;omega) Y hY
  have hW2 : 0<W P g 2 Y := W_pos P g 2 (by omega) (by unfold Stable;omega) Y hY
  have hs : separatingS P g 1 Y=(∑ j ∈ Finset.range (g+1), W P j 1 Y*W P (g-j) 1 Y)/W P g 1 Y := by simp [separatingS]
  have ht : separatingT P g 2 Y=(∑ j ∈ Finset.range (g+1), W P j 2 Y*W P (g-j) 2 Y)/W P g 2 Y := by simp [separatingT]
  have hT0 : 0 ≤ separatingT P g 2 Y := by
    rw [ht]
    apply div_nonneg _ hW2.le
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (W_nonneg P j 2 (by omega) Y hY) (W_nonneg P (g-j) 2 (by omega) Y hY)
  have heT : (∑ j ∈ Finset.range (g+1), W P j 2 Y*W P (g-j) 2 Y) =
      W P g 2 Y*separatingT P g 2 Y := by rw [ht];field_simp
  have hsum : (g:ℝ)*(∑ j ∈ Finset.range (g+1), W P j 1 Y*W P (g-j) 1 Y) ≤
      (2*C^2)* (∑ j ∈ Finset.range (g+1), W P j 2 Y*W P (g-j) 2 Y) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact separatingS_one_term_bound C hC hcusp P g j hg (by have := Finset.mem_range.mp hj;omega) Y hY
  have hscaled : (g:ℝ)*separatingS P g 1 Y ≤ (g:ℝ)*((2*C^2*Ci)*separatingT P g 2 Y) := by
    rw [hs,←mul_div_assoc]
    apply (div_le_iff₀ hW1).2
    calc _ ≤ (2*C^2)* (∑ j ∈ Finset.range (g+1), W P j 2 Y*W P (g-j) 2 Y) := hsum
         _ = (2*C^2)*(W P g 2 Y*separatingT P g 2 Y) := by rw [heT]
         _ ≤ (2*C^2)*((Ci*(g:ℝ)*W P g 1 Y)*separatingT P g 2 Y) :=
           mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hInv hT0) (by positivity)
         _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hgp).mp (by simpa only [mul_comm (g:ℝ)] using hscaled)

lemma separatingS_one_T_uniform (P : PsiTheory) : ∃ C : ℝ, 0<C ∧ ∃ G : ℕ,
    ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀, separatingS P g 1 Y ≤ C*separatingT P g 2 Y := by
  obtain ⟨Cr,hCr,hcusp⟩ := W_cusp_uniform_bound
  obtain ⟨Ci,hCi,G,hInv⟩ := W_one_cusp_inverse_uniform P
  refine ⟨2*Cr^2*Ci,by positivity,max 2 G,?_⟩
  intro g hg Y hY
  exact separatingS_one_le_multiple_T Cr Ci hCr.le hCi.le hcusp P g
    ((le_max_left _ _).trans hg) Y hY (hInv g ((le_max_right _ _).trans hg) Y hY)
end WP
namespace WP
lemma separatingS_one_quadratic_uniform (P : PsiTheory) : ∃ C : ℝ, 0<C ∧ ∃ G : ℕ,
    ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀, |separatingS P g 1 Y| ≤ C/(g:ℝ)^2 := by
  obtain ⟨C₁,hC₁,G₁,hS⟩ := separatingS_one_T_uniform P
  obtain ⟨C₂,hC₂,G₂,hT⟩ := separatingT_two_estimate P
  refine ⟨C₁*C₂,by positivity,max G₁ G₂,?_⟩
  intro g hg Y hY
  have hS0 : 0 ≤ separatingS P g 1 Y := by
    have hs : separatingS P g 1 Y=(∑ j ∈ Finset.range (g+1), W P j 1 Y*W P (g-j) 1 Y)/W P g 1 Y := by simp [separatingS]
    rw [hs]
    apply div_nonneg _ (W_nonneg P g 1 (by omega) Y hY)
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (W_nonneg P j 1 (by omega) Y hY) (W_nonneg P (g-j) 1 (by omega) Y hY)
  rw [abs_of_nonneg hS0]
  calc _ ≤ C₁*separatingT P g 2 Y := hS g ((le_max_left _ _).trans hg) Y hY
       _ ≤ C₁*|separatingT P g 2 Y| := mul_le_mul_of_nonneg_left (le_abs_self _) hC₁.le
       _ ≤ C₁*(C₂/(g:ℝ)^2) := mul_le_mul_of_nonneg_left (hT g ((le_max_right _ _).trans hg) Y hY) hC₁.le
       _ = _ := by ring
end WP

namespace WP
lemma separatingS_all_complexity_bound (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |separatingS P g p Y| ≤ C/(complexity g p:ℝ)^2 := by
  have hs : ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |separatingS P g p Y| ≤ C/(g:ℝ)^2 := by
    by_cases hp1 : p=1
    · subst p;exact separatingS_one_quadratic_uniform P
    · obtain ⟨C,hC,G,hbound⟩ := separating_estimates P p (by omega)
      exact ⟨C,hC,G,fun g hg Y hY => (hbound g hg Y hY).1⟩
  obtain ⟨C,hC,G,hbound⟩ := hs
  refine ⟨C*((p:ℝ)+2)^2,by positivity,max 2 G,?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := (le_max_left _ _).trans hg
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hsize : (complexity g p:ℝ) ≤ ((p:ℝ)+2)*(g:ℝ) := by
    have hmul : p ≤ p*g := by simpa using Nat.mul_le_mul_left p (show 1≤g by omega)
    exact_mod_cast (calc complexity g p ≤ 2*g+p := by unfold complexity;omega
                        _ ≤ 2*g+p*g := by omega
                        _ = (p+2)*g := by ring)
  have hpow := pow_le_pow_left₀ hhp.le hsize 2
  calc _ ≤ C/(g:ℝ)^2 := hbound g ((le_max_right _ _).trans hg) Y hY
       _ ≤ _ := by
         apply (div_le_div_iff₀ (sq_pos_of_pos hgp) (sq_pos_of_pos hhp)).2
         have hi := mul_le_mul_of_nonneg_left hpow hC.le
         simpa only [mul_pow,mul_assoc] using hi
end WP
