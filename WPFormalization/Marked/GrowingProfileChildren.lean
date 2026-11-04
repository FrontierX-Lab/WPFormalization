import WPFormalization.Marked.GrowingSeparatingBounds
import WPFormalization.Marked.QuadraticProfile

/-! Actual recursion children are bounded with the linear size D+p+l, before summing the kernel. Coordinate induction retains the sharp D(D+p+1) weight. -/
noncomputable section
namespace WP
open Set
lemma normalizedChildren_uniform_from_ratios_linear_size (P : PsiTheory) (g p k l : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (hp : 2 ≤ p) (hd : (k::d).length=p) (Y : ℝ) (hY : Y ∈ Icc 0 y₀)
    (C Cs : ℝ) (hC : 0 ≤ C) (hCs : 0 ≤ Cs)
    (hmerge : (g:ℝ)*W P g (p-1) Y ≤ C*W P g p Y)
    (hhandle : (g:ℝ)*W P (g-1) (p+1) Y ≤ C*W P g p Y)
    (hsep : separatingS P g p Y ≤ Cs/(g:ℝ)) :
    (4:ℝ)^g * normalizedChildren P g (k+l) (d.map Int.ofNat) Y / W P g p Y ≤
      (4*C+Cs)*(((k::d).sum:ℝ)+p+l+1)/(g:ℝ) := by
  have hdlen : d.length+1=p := by simpa only [List.length_cons] using hd
  have hd1 : 1 ≤ d.length := by omega
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hw : 0<W P g p Y := W_pos P g p (by omega) (by unfold Stable;omega) Y hY
  have hm : W P g d.length Y / W P g p Y ≤ C/(g:ℝ) := by
    apply (div_le_div_iff₀ hw hgp).2
    simpa only [show p-1=d.length by omega,mul_comm (g:ℝ)] using hmerge
  have hh : W P (g-1) (d.length+2) Y / W P g p Y ≤ C/(g:ℝ) := by
    apply (div_le_div_iff₀ hw hgp).2
    simpa only [show p+1=d.length+2 by omega,mul_comm (g:ℝ)] using hhandle
  have hc := normalizedChildren_W_bound P g (k+l) d (by omega) Y hY
  rw [hdlen] at hc
  have hc' : (4:ℝ)^g * normalizedChildren P g (k+l) (d.map Int.ofNat) Y / W P g p Y ≤
      (2*(d.sum:ℝ)+d.length)*(W P g d.length Y / W P g p Y) +
      2*((k+l+1:ℕ):ℝ)*(W P (g-1) (d.length+2) Y / W P g p Y) +
      ((k+l+1:ℕ):ℝ)/2 * separatingS P g p Y := by
    convert div_le_div_of_nonneg_right hc hw.le using 1 <;> field_simp
  let S : ℝ := ((k::d).sum:ℝ)+p+l+1
  have hsum : ((k::d).sum:ℝ)=(k:ℝ)+(d.sum:ℝ) := by simp only [List.sum_cons,Nat.cast_add]
  have hlen : (d.length:ℝ)+1=p := by exact_mod_cast hdlen
  have hkl : ((k+l+1:ℕ):ℝ)=(k:ℝ)+l+1 := by push_cast;ring
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hd0 : (0:ℝ) ≤ d.sum := Nat.cast_nonneg _
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg _
  have hl0 : (0:ℝ) ≤ l := Nat.cast_nonneg _
  have hFa : 2*(d.sum:ℝ)+d.length+2*((k+l+1:ℕ):ℝ) ≤ 4*S := by
    simp only [S,List.sum_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hsum,hlen,hk0,hd0,hp0,hl0]
  have hFb : ((k+l+1:ℕ):ℝ)/2 ≤ S := by
    simp only [S,List.sum_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hsum,hk0,hd0,hp0,hl0]
  calc
    _ ≤ (2*(d.sum:ℝ)+d.length)*(C/(g:ℝ)) +
          2*((k+l+1:ℕ):ℝ)*(C/(g:ℝ)) + ((k+l+1:ℕ):ℝ)/2*(Cs/(g:ℝ)) := by
      exact hc'.trans (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
          (mul_le_mul_of_nonneg_left hh (by positivity)))
        (mul_le_mul_of_nonneg_left hsep (by positivity)))
    _ = ((2*(d.sum:ℝ)+d.length+2*((k+l+1:ℕ):ℝ))*C+((k+l+1:ℕ):ℝ)/2*Cs)/(g:ℝ) := by ring
    _ ≤ (4*S*C+S*Cs)/(g:ℝ) := by
      apply div_le_div_of_nonneg_right _ hgp.le
      exact add_le_add (mul_le_mul_of_nonneg_right hFa hC) (mul_le_mul_of_nonneg_right hFb hCs)
    _ = _ := by dsimp [S];ring
lemma profile_adjacent_growing_markings_bound (P : PsiTheory) (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ,0 < C ∧ ∃ G : ℕ,∀g≥G,∀p:ℕ,2 ≤ p →
      (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) → ∀k:ℕ,∀d:List ℕ,(k::d).length=p →
      ∀Y∈Icc (0:ℝ) y₀,profile P g (k::d) Y-profile P g ((k+1)::d) Y ≤
        C*(((k::d).sum:ℝ)+p+1)/(g:ℝ) := by
  obtain ⟨Cr,hCr,hcusp⟩ := W_cusp_uniform_bound
  obtain ⟨Cs,hCs,Gs,hsep⟩ := separatingS_growing_markings_genus_bound P M hM
  obtain ⟨U,hU⟩ := uniform_kernel_moments.2 1
  let B : ℝ := max 1 U
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let K : ℝ := 4*Cr+Cs
  have hK : 0 < K := by dsimp [K];positivity
  refine ⟨K*B,by positivity,Gs+2,?_⟩
  intro g hg p hp hpM k d hd Y hY
  have hg2 : 2 ≤ g := by omega
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hdlen : d.length+1=p := by simpa only [List.length_cons] using hd
  by_cases had : (k::d).sum ≤ dimension g (d.length+1)
  · rw [profile_adjacent_degree_difference P g k d (by omega) Y hY (by unfold complexity;omega) had]
    have hsum : ∑l∈Finset.range (deficit g (k::d)+1),(1+(l:ℝ))*weight Y l ≤ B := by
      have hm := hU Y hY
      simp only [pow_one] at hm
      exact ((hm.1.sum_le_tsum _ (fun l _=>mul_nonneg (by positivity) (weight_nonneg Y hY l))).trans hm.2).trans (le_max_right _ _)
    calc
      _ ≤ ∑l∈Finset.range (deficit g (k::d)+1),weight Y l*
          (K*(((k::d).sum:ℝ)+p+1)*(1+(l:ℝ))/(g:ℝ)) := by
        apply Finset.sum_le_sum
        intro l hl
        apply mul_le_mul_of_nonneg_left _ (weight_nonneg Y hY l)
        have hm := W_cusp_ratio_ge_genus Cr hcusp P g p hg2 hp Y hY
        have hh := W_nonsep_cusp_ratio_ge_genus Cr hCr.le hcusp P g p hg2 hp Y hY
        have hc := normalizedChildren_uniform_from_ratios_linear_size P g p k l d hg2 hp hd Y hY Cr Cs
          hCr.le hCs.le hm hh (hsep g (by omega) p (by omega) hpM Y hY)
        rw [hdlen]
        have hsize : ((k::d).sum:ℝ)+p+l+1 ≤ (((k::d).sum:ℝ)+p+1)*(1+(l:ℝ)) := by
          nlinarith only [mul_nonneg (show (0:ℝ) ≤ ((k::d).sum:ℝ)+p by positivity) (Nat.cast_nonneg (α:=ℝ) l)]
        apply hc.trans
        apply div_le_div_of_nonneg_right _ hgp.le
        have he := mul_le_mul_of_nonneg_left hsize hK.le
        convert he using 1 <;> dsimp [K] <;>ring
      _ = (K*(((k::d).sum:ℝ)+p+1)/(g:ℝ))*
          ∑l∈Finset.range (deficit g (k::d)+1),(1+(l:ℝ))*weight Y l := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ ≤ (K*(((k::d).sum:ℝ)+p+1)/(g:ℝ))*B := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  · have hz₀ : normalized P g (k::d) Y=0 := normalized_excess P g _ Y (by simpa only [List.length_cons] using Nat.lt_of_not_ge had)
    have hz₁ : normalized P g ((k+1)::d) Y=0 := normalized_excess P g _ Y (by simp only [List.length_cons,List.sum_cons] at *;omega)
    simp only [profile,hz₀,hz₁,zero_div,sub_self]
    positivity
lemma profile_linear_size_of_adjacent (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p)
    (hs : Stable g p) (hg : 0 < g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀)
    (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ k : ℕ, ∀ e : List ℕ, (k::e).length = p →
      profile P g (k::e) Y - profile P g ((k+1)::e) Y ≤ C*((k::e).sum+p+1)/(g:ℝ)) :
    ∀ d : List ℕ, d.length = p →
      0 ≤ 1-profile P g d Y ∧
      1-profile P g d Y ≤ C*(d.sum:ℝ)*(d.sum+p+1)/(g:ℝ) := by
  have hgp : (0:ℝ) < g := by exact_mod_cast hg
  have hbound : ∀ n : ℕ, ∀ d : List ℕ, d.sum = n → d.length = p →
      1-profile P g d Y ≤ C*(d.sum:ℝ)*(d.sum+p+1)/(g:ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hd hlen
      by_cases hz : d.sum=0
      · have he : d = List.replicate d.length 0 :=
          List.eq_replicate_of_mem (List.sum_eq_zero_iff_forall_eq_nat.mp hz)
        rw [he,hlen,profile_replicate_zero P g p hp hs Y hY]
        simp
      · obtain ⟨a,ha,hapos⟩ := List.sum_pos_iff_exists_pos_nat.mp (Nat.pos_of_ne_zero hz)
        obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hapos)
        obtain ⟨l,r,rfl⟩ := List.mem_iff_append.mp ha
        let e := l ++ k::r
        have helen : e.length = p := by simpa only [e,List.length_append,List.length_cons] using hlen
        have hes : e.sum < n := by simp only [e,List.sum_append,List.sum_cons] at hd ⊢;omega
        have hprev := ih e.sum hes e rfl helen
        have hperm₀ : e.Perm (k::(l++r)) := by exact List.perm_middle
        have hperm₁ : (l++(k+1)::r).Perm ((k+1)::(l++r)) := by exact List.perm_middle
        have hlen' : (k::(l++r)).length = p := by simpa using hperm₀.length_eq.symm.trans helen
        have hinc := hstep k (l++r) hlen'
        rw [←profile_perm P g hperm₀ Y,←profile_perm P g hperm₁ Y] at hinc
        have hsum : (l++(k+1)::r).sum=e.sum+1 := by simp only [e,List.sum_append,List.sum_cons];omega
        have hsume : (k::(l++r)).sum=e.sum := hperm₀.sum_eq.symm
        rw [hsume] at hinc
        rw [hsum,Nat.cast_add,Nat.cast_one]
        calc
          _ = (1-profile P g e Y)+(profile P g e Y-profile P g (l++(k+1)::r) Y) := by ring
          _ ≤ C*(e.sum:ℝ)*(e.sum+p+1)/(g:ℝ)+C*(e.sum+p+1)/(g:ℝ) := add_le_add hprev hinc
          _ ≤ _ := by
            rw [←add_div]
            apply div_le_div_of_nonneg_right _ hgp.le
            have he := mul_nonneg hC (show (0:ℝ) ≤ (e.sum:ℝ)+1 by positivity)
            nlinarith only [he]
  intro d hlen
  refine ⟨?_,hbound d.sum d rfl hlen⟩
  have hb := normalized_profile_bounds P g d (by rwa [hlen]) (by omega) Y hY
  exact sub_nonneg.mpr hb.2
end WP
