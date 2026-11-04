import WPFormalization.Marked.Positivity
import WPFormalization.Statements.MarkedSeparating
import WPFormalization.Intersection.PrimitiveSeparating
/-! The actual adjacent-degree difference is bounded using the real child
amplitudes, uniform kernel moments, and the separating estimate. A strong
induction on total degree proves the quadratic profile error for p ≥ 2,
including excess degrees and every stable genus. -/
noncomputable section
open Set
namespace WP
lemma normInt_le_all_zero (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hn : 1 ≤ d.length) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    normInt P g d Y ≤ normalized P g (List.replicate d.length 0) Y := by
  unfold normInt
  split_ifs with hnon
  · by_cases hs : Stable g d.length
    · simpa only [List.length_map] using normalized_le_all_zero P g (d.map Int.toNat)
        (by simpa only [List.length_map] using hs) Y hY
    · rw [normalized_unstable P g _ Y (by simpa only [List.length_map] using hs),
        normalized_unstable P g _ Y (by simpa only [List.length_replicate] using hs)]
  · exact normalized_nonneg_nonempty P g _ (by simpa only [List.length_replicate] using hn) Y hY

lemma normInt_nonneg_profile (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hn : 1 ≤ d.length) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) : 0 ≤ normInt P g d Y := by
  unfold normInt
  split_ifs
  · exact normalized_nonneg_nonempty P g _ (by simpa only [List.length_map] using hn) Y hY
  · exact le_rfl

lemma normalizedChildren_as_normInt (P : PsiTheory) (g p : ℕ) (d : List ℤ) (Y : ℝ) :
    normalizedChildren P g p d Y =
    (∑ j ∈ Finset.range d.length, (2*(d[j]! : ℝ)+1)*
      normInt P g (((p : ℤ)+d[j]!-1) :: d.eraseIdx j) Y) +
    (if g=0 then 0 else (1/2 : ℝ)*∑ u ∈ Finset.range (p-1),
      normInt P (g-1) ((u : ℤ) :: ((p : ℤ)-2-u) :: d) Y) +
    (1/2 : ℝ)*∑ u ∈ Finset.range (p-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset,
        normInt P g₁ ((u : ℤ) :: selected d I) Y *
        normInt P (g-g₁) (((p : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)) Y := rfl

lemma zero_profile_split_sum (P : PsiTheory) (g : ℕ) (d : List ℤ) (u p : ℕ)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    (∑ g₁ ∈ Finset.range (g+1), ∑ I ∈ (Finset.range d.length).powerset,
      normInt P g₁ ((u : ℤ) :: selected d I) Y *
      normInt P (g-g₁) (((p : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)) Y) ≤
    ∑ g₁ ∈ Finset.range (g+1), ∑ s ∈ Finset.range (d.length+1),
      (d.length.choose s : ℝ) * normalized P g₁ (List.replicate (s+1) 0) Y *
        normalized P (g-g₁) (List.replicate (d.length-s+1) 0) Y := by
  apply Finset.sum_le_sum
  intro j hj
  calc
    _ ≤ ∑ I ∈ (Finset.range d.length).powerset,
        normalized P j (List.replicate (I.card+1) 0) Y *
        normalized P (g-j) (List.replicate (d.length-I.card+1) 0) Y := by
      apply Finset.sum_le_sum
      intro I hI
      have hi := Finset.mem_powerset.mp hI
      have hl₁ := selected_length_card d I hi
      have hl₂ := selected_length_card d ((Finset.range d.length) \ I) Finset.sdiff_subset
      rw [Finset.card_sdiff_of_subset hi, Finset.card_range] at hl₂
      have hleft := normInt_le_all_zero P j ((u : ℤ) :: selected d I) (by simp) Y hY
      have hright := normInt_le_all_zero P (g-j)
        (((p : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)) (by simp) Y hY
      simp only [List.length_cons,hl₁,hl₂] at hleft hright
      exact mul_le_mul hleft hright
        (normInt_nonneg_profile P _ _ (by simp) Y hY)
        (normalized_nonneg_nonempty P _ _ (by simp) Y hY)
    _ = _ := by
      simpa only [Finset.card_range,nsmul_eq_mul,mul_assoc] using
        Finset.sum_powerset_apply_card
          (fun s => normalized P j (List.replicate (s+1) 0) Y *
            normalized P (g-j) (List.replicate (d.length-s+1) 0) Y)
          (x := Finset.range d.length)

lemma normalizedChildren_zero_bound (P : PsiTheory) (g t : ℕ) (d : List ℕ)
    (hg : 1 ≤ g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    normalizedChildren P g t (d.map Int.ofNat) Y ≤
      (2*(d.sum:ℝ)+d.length)*normalized P g (List.replicate d.length 0) Y +
      ((t+1:ℕ):ℝ)/2 * normalized P (g-1) (List.replicate (d.length+2) 0) Y +
      ((t+1:ℕ):ℝ)/2 *
        ∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (d.length+1),
          (d.length.choose s : ℝ)*normalized P j (List.replicate (s+1) 0) Y *
            normalized P (g-j) (List.replicate (d.length-s+1) 0) Y := by
  rw [normalizedChildren_as_normInt,if_neg (by omega : g≠0)]
  apply add_le_add
  · apply add_le_add
    · calc
        _ ≤ ∑ j ∈ Finset.range d.length,
            (2*(d[j]!:ℝ)+1)*normalized P g (List.replicate d.length 0) Y := by
          simp only [List.length_map]
          apply Finset.sum_le_sum
          intro j hj
          have hj' := Finset.mem_range.mp hj
          have hget : (d.map Int.ofNat)[j]! = (d[j]!:ℤ) := by simp [hj']
          rw [hget]
          apply mul_le_mul_of_nonneg_left
          · have hi := normInt_le_all_zero P g
              (((t:ℤ)+(d[j]!:ℤ)-1) :: (d.map Int.ofNat).eraseIdx j)
              (by simp) Y hY
            simpa only [List.length_cons,List.length_eraseIdx,List.length_map,if_pos hj',
              show d.length-1+1=d.length by omega] using hi
          · positivity
        _ = _ := by
          rw [← Finset.sum_mul,Finset.sum_add_distrib,← Finset.mul_sum]
          have he := sum_range_getElem d (fun k : ℕ => (k:ℝ))
          have hc : (d.map (fun k : ℕ => (k:ℝ))).sum = (d.sum:ℝ) := by exact (map_list_sum (Nat.castAddMonoidHom ℝ) d).symm
          rw [hc] at he
          simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    · calc
        _ ≤ (1/2:ℝ) * ∑ u ∈ Finset.range (t-1),
            normalized P (g-1) (List.replicate (d.length+2) 0) Y := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum
          intro u hu
          have hi := normInt_le_all_zero P (g-1) ((u:ℤ)::((t:ℤ)-2-u)::d.map Int.ofNat)
            (by simp) Y hY
          simpa only [List.length_cons,List.length_map,Nat.add_assoc,add_comm 2] using hi
        _ ≤ _ := by
          simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
          have hn : ((t-1:ℕ):ℝ) ≤ (t+1:ℕ) := by exact_mod_cast (show t-1 ≤ t+1 by omega)
          nlinarith [normalized_nonneg_nonempty P (g-1) (List.replicate (d.length+2) 0) (by simp) Y hY]
  · calc
      _ ≤ (1/2:ℝ)*∑ u ∈ Finset.range (t-1),
          ∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (d.length+1),
            (d.length.choose s:ℝ)*normalized P j (List.replicate (s+1) 0) Y *
              normalized P (g-j) (List.replicate (d.length-s+1) 0) Y := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro u hu
        simpa only [List.length_map] using zero_profile_split_sum P g (d.map Int.ofNat) u t Y hY
      _ ≤ _ := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        have hn : ((t-1:ℕ):ℝ) ≤ (t+1:ℕ) := by exact_mod_cast (show t-1 ≤ t+1 by omega)
        have hs : 0 ≤ ∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (d.length+1),
            (d.length.choose s:ℝ)*normalized P j (List.replicate (s+1) 0) Y *
              normalized P (g-j) (List.replicate (d.length-s+1) 0) Y := by
          apply Finset.sum_nonneg;intro j hj
          apply Finset.sum_nonneg;intro s hs
          exact mul_nonneg (mul_nonneg (by positivity)
            (normalized_nonneg_nonempty P j _ (by simp) Y hY))
            (normalized_nonneg_nonempty P (g-j) _ (by simp) Y hY)
        nlinarith
end WP
namespace WP
lemma W_zero_split_identity (P : PsiTheory) (g n : ℕ) (hg : 1 ≤ g)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    (4:ℝ)^g *
      (∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (n+1),
        (n.choose s:ℝ)*normalized P j (List.replicate (s+1) 0) Y *
          normalized P (g-j) (List.replicate (n-s+1) 0) Y) =
      W P g (n+1) Y * separatingS P g (n+1) Y := by
  have hpos : 0 < W P g (n+1) Y := W_pos P g _ (by omega) (by unfold Stable;omega) Y hY
  have he : W P g (n+1) Y * separatingS P g (n+1) Y =
      ∑ j ∈ Finset.range (g+1), ∑ s ∈ Finset.range (n+1),
        (n.choose s:ℝ)*W P j (s+1) Y * W P (g-j) (n+1-s) Y := by
    unfold separatingS
    simp only [Nat.add_sub_cancel]
    field_simp
  rw [he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsj : s ≤ n := by have := Finset.mem_range.mp hs;omega
  have hgj : j ≤ g := by have := Finset.mem_range.mp hj;omega
  have hpow : (4:ℝ)^j*(4:ℝ)^(g-j)=(4:ℝ)^g := by rw [←pow_add,Nat.add_sub_of_le hgj]
  have hlen : n+1-s=n-s+1 := by omega
  unfold W
  rw [hlen]
  calc
    _ = (4:ℝ)^g * ((n.choose s:ℝ)*normalized P j (List.replicate (s+1) 0) Y *
        normalized P (g-j) (List.replicate (n-s+1) 0) Y) := rfl
    _ = _ := by rw [←hpow];ring

lemma normalizedChildren_W_bound (P : PsiTheory) (g t : ℕ) (d : List ℕ)
    (hg : 1 ≤ g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    (4:ℝ)^g * normalizedChildren P g t (d.map Int.ofNat) Y ≤
      (2*(d.sum:ℝ)+d.length)*W P g d.length Y +
      2*((t+1:ℕ):ℝ)*W P (g-1) (d.length+2) Y +
      ((t+1:ℕ):ℝ)/2 * (W P g (d.length+1) Y * separatingS P g (d.length+1) Y) := by
  have hi := mul_le_mul_of_nonneg_left (normalizedChildren_zero_bound P g t d hg Y hY)
    (by positivity : (0:ℝ) ≤ 4^g)
  have hpow : (4:ℝ)^g = 4*(4:ℝ)^(g-1) := by rw [←pow_succ',Nat.sub_add_cancel hg]
  calc
    _ ≤ _ := hi
    _ = _ := by
      rw [mul_add,mul_add]
      have hs := W_zero_split_identity P g d.length hg Y hY
      rw [←hs]
      unfold W
      rw [hpow]
      ring
end WP
namespace WP
lemma profile_adjacent_degree_difference (P : PsiTheory) (g k : ℕ) (d : List ℕ)
    (hg : 1 ≤ g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀)
    (hh : 2 ≤ complexity g (d.length+1)) (hd : (k::d).sum ≤ dimension g (d.length+1)) :
    profile P g (k::d) Y - profile P g ((k+1)::d) Y =
    ∑ l ∈ Finset.range (deficit g (k::d)+1), weight Y l *
      ((4:ℝ)^g * normalizedChildren P g (k+l) (d.map Int.ofNat) Y / W P g (d.length+1) Y) := by
  have hn : 0 < normalized P g (List.replicate (d.length+1) 0) Y :=
    normalized_pos_valid_nonempty P g _ (by simp) (by simp only [List.length_replicate];unfold Stable;omega)
      (by simp) Y hY
  unfold profile
  simp only [List.length_cons]
  rw [←sub_div,normalized_adjacent_degree_difference P g k d Y hY hh hd,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l hl
  unfold W
  field_simp

lemma W_cusp_ratio_ge_genus (C : ℝ)
    (hcusp : ∀ P : PsiTheory, ∀ g p : ℕ, Stable g p → ∀ Y ∈ Icc (0:ℝ) y₀,
      (complexity g p:ℝ)*W P g p Y ≤ C*W P g (p+1) Y)
    (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) (hp : 2 ≤ p)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    (g:ℝ)*W P g (p-1) Y ≤ C*W P g p Y := by
  have hs : Stable g (p-1) := by unfold Stable;omega
  have hsize : (g:ℝ) ≤ complexity g (p-1) := by exact_mod_cast (show g ≤ complexity g (p-1) by unfold complexity;omega)
  have hi := hcusp P g (p-1) hs Y hY
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at hi
  exact (mul_le_mul_of_nonneg_right hsize (W_nonneg P g (p-1) (by omega) Y hY)).trans hi

lemma W_nonsep_cusp_ratio_ge_genus (C : ℝ) (hC : 0 ≤ C)
    (hcusp : ∀ P : PsiTheory, ∀ g p : ℕ, Stable g p → ∀ Y ∈ Icc (0:ℝ) y₀,
      (complexity g p:ℝ)*W P g p Y ≤ C*W P g (p+1) Y)
    (P : PsiTheory) (g p : ℕ) (hg : 2 ≤ g) (hp : 2 ≤ p)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    (g:ℝ)*W P (g-1) (p+1) Y ≤ C*W P g p Y := by
  have hs : Stable (g-1) (p+1) := by unfold Stable;omega
  have hsize : (g:ℝ) ≤ complexity (g-1) (p+1) := by exact_mod_cast (show g ≤ complexity (g-1) (p+1) by unfold complexity;omega)
  have hi := hcusp P (g-1) (p+1) hs Y hY
  rw [show p+1+1=p+2 by omega] at hi
  exact ((mul_le_mul_of_nonneg_right hsize (W_nonneg P (g-1) (p+1) (by omega) Y hY)).trans hi).trans
    (mul_le_mul_of_nonneg_left (W_genus_exchange_le P g p (by omega) hp Y hY) hC)
end WP
namespace WP
lemma normalizedChildren_uniform_from_ratios (P : PsiTheory) (g p k l : ℕ) (d : List ℕ)
    (hg : 2 ≤ g) (hp : 2 ≤ p) (hd : (k::d).length=p) (Y : ℝ) (hY : Y ∈ Icc 0 y₀)
    (C Cs : ℝ) (hC : 0 ≤ C) (hCs : 0 ≤ Cs)
    (hmerge : (g:ℝ)*W P g (p-1) Y ≤ C*W P g p Y)
    (hhandle : (g:ℝ)*W P (g-1) (p+1) Y ≤ C*W P g p Y)
    (hsep : separatingS P g p Y ≤ Cs/(g:ℝ)) :
    (4:ℝ)^g * normalizedChildren P g (k+l) (d.map Int.ofNat) Y / W P g p Y ≤
      (((p:ℝ)+4)*C+Cs)*((k::d).sum+1)*(1+(l:ℝ))/(g:ℝ) := by
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
  let F : ℝ := ((k::d).sum+1)*(1+(l:ℝ))
  have hF0 : 0 ≤ F := by dsimp [F];positivity
  have hFa : 2*(d.sum:ℝ)+d.length ≤ ((p:ℝ)+2)*F := by
    have hF : ((k::d).sum:ℝ)+1 ≤ F := by
      dsimp [F]
      nlinarith [mul_nonneg (show (0:ℝ)≤(k::d).sum+1 by positivity) (Nat.cast_nonneg l)]
    have htail : (d.sum:ℝ) ≤ (k::d).sum := by simp only [List.sum_cons,Nat.cast_add];linarith [show (0:ℝ) ≤ k from Nat.cast_nonneg k]
    have hlenR : (d.length:ℝ)+1=p := by exact_mod_cast hdlen
    have hp0 : (0:ℝ)≤p := Nat.cast_nonneg _
    nlinarith [mul_nonneg hp0 (show (0:ℝ)≤(k::d).sum by positivity)]
  have hFb : ((k+l+1:ℕ):ℝ) ≤ F := by
    dsimp [F]
    simp only [List.sum_cons,Nat.cast_add,Nat.cast_one]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ k from Nat.cast_nonneg k)
        (show (0:ℝ) ≤ l from Nat.cast_nonneg l),
      mul_nonneg (show (0:ℝ) ≤ d.sum from Nat.cast_nonneg _)
        (show (0:ℝ) ≤ l from Nat.cast_nonneg l),
      show (0:ℝ) ≤ d.sum from Nat.cast_nonneg _]
  have hFb2 : ((k+l+1:ℕ):ℝ)/2 ≤ F := by linarith
  calc
    _ ≤ (2*(d.sum:ℝ)+d.length)*(C/(g:ℝ)) +
          2*((k+l+1:ℕ):ℝ)*(C/(g:ℝ)) + ((k+l+1:ℕ):ℝ)/2*(Cs/(g:ℝ)) := by
      exact hc'.trans (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
          (mul_le_mul_of_nonneg_left hh (by positivity)))
        (mul_le_mul_of_nonneg_left hsep (by positivity)))
    _ = ((2*(d.sum:ℝ)+d.length)*C+2*((k+l+1:ℕ):ℝ)*C+((k+l+1:ℕ):ℝ)/2*Cs)/(g:ℝ) := by ring
    _ ≤ (((p:ℝ)+2)*F*C+2*F*C+F*Cs)/(g:ℝ) := by
      apply div_le_div_of_nonneg_right _ hgp.le
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hFa hC)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFb (by norm_num)) hC))
        (mul_le_mul_of_nonneg_right hFb2 hCs)
    _ = _ := by dsimp [F];ring
end WP
namespace WP
lemma profile_adjacent_uniform_bound (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∀ g : ℕ, 1 ≤ g → ∀ k : ℕ, ∀ d : List ℕ, (k::d).length=p →
      ∀ Y ∈ Icc (0:ℝ) y₀,
        profile P g (k::d) Y-profile P g ((k+1)::d) Y ≤ C*((k::d).sum+1)/(g:ℝ) := by
  obtain ⟨Cr,hCr,hcusp⟩ := W_cusp_uniform_bound
  obtain ⟨Cs,hCs,g₀,hsep⟩ := separating_estimates P p hp
  obtain ⟨M,hM⟩ := uniform_kernel_moments.2 1
  let B : ℝ := max 1 M
  have hB : 0<B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let K : ℝ := ((p:ℝ)+4)*Cr+Cs
  have hK : 0<K := by dsimp [K];positivity
  let G : ℕ := max 2 g₀
  let C : ℝ := max (K*B) G
  have hC : 0<C := lt_of_lt_of_le (mul_pos hK hB) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro g hg k d hd Y hY
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hst : Stable g p := by unfold Stable;omega
  have hst₀ : Stable g (k::d).length := by rwa [hd]
  have hst₁ : Stable g ((k+1)::d).length := by simpa only [List.length_cons] using hst₀
  have hden : 0<normalized P g (List.replicate p 0) Y := normalized_pos_valid_nonempty P g _
    (by simp;omega) (by simpa using hst) (by simp) Y hY
  by_cases hlarge : G ≤ g
  · have hg₂ : 2 ≤ g := (le_max_left _ _).trans hlarge
    have hg₀ : g₀ ≤ g := (le_max_right _ _).trans hlarge
    have hS : separatingS P g p Y ≤ Cs/(g:ℝ) := by
      calc _ ≤ |separatingS P g p Y| := le_abs_self _
           _ ≤ Cs/(g:ℝ)^2 := (hsep g hg₀ Y hY).1
           _ ≤ _ := by
             apply div_le_div_of_nonneg_left hCs.le hgp
             have hg1 : (1:ℝ) ≤ g := by exact_mod_cast hg
             nlinarith
    by_cases had : (k::d).sum ≤ dimension g (d.length+1)
    · have hh : 2 ≤ complexity g (d.length+1) := by unfold complexity;omega
      rw [profile_adjacent_degree_difference P g k d hg Y hY hh had]
      have hsum : ∑ l ∈ Finset.range (deficit g (k::d)+1), (1+(l:ℝ))*weight Y l ≤ B := by
        have hm := hM Y hY
        simp only [pow_one] at hm
        exact ((hm.1.sum_le_tsum _ (fun l _ => mul_nonneg (by positivity) (weight_nonneg Y hY l))).trans hm.2).trans
          (le_max_right _ _)
      calc
        _ ≤ ∑ l ∈ Finset.range (deficit g (k::d)+1), weight Y l *
            (K*((k::d).sum+1)*(1+(l:ℝ))/(g:ℝ)) := by
          apply Finset.sum_le_sum
          intro l hl
          apply mul_le_mul_of_nonneg_left _ (weight_nonneg Y hY l)
          have hm := W_cusp_ratio_ge_genus Cr hcusp P g p hg₂ hp Y hY
          have hh := W_nonsep_cusp_ratio_ge_genus Cr hCr.le hcusp P g p hg₂ hp Y hY
          have hb := normalizedChildren_uniform_from_ratios P g p k l d hg₂ hp hd Y hY Cr Cs hCr.le hCs.le hm hh hS
          simpa only [K,show d.length+1=p by simpa only [List.length_cons] using hd] using hb
        _ = (K*((k::d).sum+1)/(g:ℝ)) *
            ∑ l ∈ Finset.range (deficit g (k::d)+1), (1+(l:ℝ))*weight Y l := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          ring
        _ ≤ (K*((k::d).sum+1)/(g:ℝ))*B := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ ≤ C*((k::d).sum+1)/(g:ℝ) := by
          have hc := mul_le_mul_of_nonneg_right (le_max_left (K*B) (g:ℝ))
            (show (0:ℝ) ≤ ((k::d).sum+1)/(g:ℝ) by positivity)
          have hc' : K*B ≤ C := le_max_left _ _
          calc _ = K*B*(((k::d).sum+1)/(g:ℝ)) := by ring
               _ ≤ C*(((k::d).sum+1)/(g:ℝ)) := mul_le_mul_of_nonneg_right hc' (by positivity)
               _ = _ := by ring
    · have hz₀ : normalized P g (k::d) Y=0 := normalized_excess P g _ Y (by simpa only [List.length_cons] using Nat.lt_of_not_ge had)
      have hz₁ : normalized P g ((k+1)::d) Y=0 := normalized_excess P g _ Y (by simp only [List.length_cons,List.sum_cons] at *;omega)
      simp only [profile,hz₀,hz₁,zero_div,sub_self]
      positivity
  · have hbound₀ := normalized_profile_bounds P g (k::d) hst₀ (by simp) Y hY
    have hbound₁ := normalized_profile_bounds P g ((k+1)::d) hst₁ (by simp) Y hY
    have hgG : (g:ℝ) ≤ (G:ℝ) := by exact_mod_cast (show g ≤ G by omega)
    have hCg : (g:ℝ) ≤ C := hgG.trans (le_max_right _ _)
    have he : 1 ≤ C*((k::d).sum+1)/(g:ℝ) := by
      apply (le_div_iff₀ hgp).2
      have hD : (1:ℝ) ≤ (k::d).sum+1 := by linarith [show (0:ℝ) ≤ (k::d).sum from Nat.cast_nonneg _]
      have hi := mul_le_mul_of_nonneg_left hD hC.le
      linarith
    exact (show profile P g (k::d) Y-profile P g ((k+1)::d) Y ≤ 1 by
      change normalized P g (k::d) Y/normalized P g (List.replicate (k::d).length 0) Y-
        normalized P g ((k+1)::d) Y/normalized P g (List.replicate ((k+1)::d).length 0) Y ≤ 1
      linarith [hbound₀.2,hbound₁.1]).trans he
end WP

namespace WP
lemma profile_perm (P : PsiTheory) (g : ℕ) {d e : List ℕ} (hp : d.Perm e) (Y : ℝ) :
    profile P g d Y = profile P g e Y := by
  unfold profile
  rw [normalized_perm P g hp Y,hp.length_eq]

lemma profile_replicate_zero (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Icc 0 y₀) : profile P g (List.replicate p 0) Y = 1 := by
  unfold profile
  simp only [List.length_replicate]
  apply div_self
  exact (normalized_pos_valid_nonempty P g _ (by simpa using hp)
    (by simpa using hs) (by simp) Y hY).ne'

lemma profile_quadratic_of_adjacent (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p)
    (hs : Stable g p) (hg : 0 < g) (Y : ℝ) (hY : Y ∈ Icc 0 y₀)
    (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ k : ℕ, ∀ e : List ℕ, (k::e).length = p →
      profile P g (k::e) Y - profile P g ((k+1)::e) Y ≤ C*((k::e).sum+1)/(g:ℝ)) :
    ∀ d : List ℕ, d.length = p →
      0 ≤ 1-profile P g d Y ∧
      1-profile P g d Y ≤ C*(d.sum:ℝ)*(d.sum+1)/(g:ℝ) := by
  have hgp : (0:ℝ) < g := by exact_mod_cast hg
  have hbound : ∀ n : ℕ, ∀ d : List ℕ, d.sum = n → d.length = p →
      1-profile P g d Y ≤ C*(d.sum:ℝ)*(d.sum+1)/(g:ℝ) := by
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
          _ ≤ C*(e.sum:ℝ)*(e.sum+1)/(g:ℝ)+C*(e.sum+1)/(g:ℝ) := add_le_add hprev hinc
          _ ≤ _ := by
            rw [←add_div]
            apply div_le_div_of_nonneg_right _ hgp.le
            calc
              _ = C*(e.sum+1)*(e.sum+1+1)-C*(e.sum+1) := by ring
              _ ≤ _ := sub_le_self _ (mul_nonneg hC (by positivity))
  intro d hlen
  refine ⟨?_,hbound d.sum d rfl hlen⟩
  have hb := normalized_profile_bounds P g d (by rwa [hlen]) (by omega) Y hY
  exact sub_nonneg.mpr hb.2
end WP

namespace WP
lemma quadratic_profile_proof (P : PsiTheory) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0<C ∧ ∀ g : ℕ, 1 ≤ g → ∀ d : List ℕ, d.length=p →
    ∀ Y ∈ Icc (0:ℝ) y₀, 0 ≤ 1-profile P g d Y ∧
      1-profile P g d Y ≤ C*(d.sum:ℝ)*(d.sum+1)/(g:ℝ) := by
  obtain ⟨C,hC,hstep⟩ := profile_adjacent_uniform_bound P p hp
  refine ⟨C,hC,?_⟩
  intro g hg d hd Y hY
  exact profile_quadratic_of_adjacent P g p (by omega) (by unfold Stable;omega)
    (by omega) Y hY C hC.le (fun k e he => hstep g hg k e he Y hY) d hd
end WP
