import WPFormalization.Weighted.CoefficientConvolution
import WPFormalization.Weighted.ModelValidity

/-! Actual signed separating-model node support and full coefficient convolution. -/
noncomputable section
namespace WP
lemma harmonicCoeff_partial_convolution {α : Type*} [DecidableEq α]
    (s : Finset α) (a b : α → ℕ) (h₁ h₂ t : ℕ) (hh₁ : 1 ≤ h₁) (hh₂ : 1 ≤ h₂)
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (hinj : Set.InjOn a (s : Set α))
    (ht : ∀ i ∈ s, a i+b i=t) :
    (∑ i ∈ s, harmonicCoeff Y h₁ (a i)*harmonicCoeff Y h₂ (b i)) ≤
      harmonicCoeff Y (h₁+h₂) t := by
  rw [← harmonicCoeff_convolution Y hY h₁ h₂ t]
  apply Finset.sum_le_sum_of_injOn a hinj
  · intro j hj
    rcases Finset.mem_image.mp hj with ⟨i,hi,rfl⟩
    exact Finset.mem_range.mpr (by have := ht i hi; omega)
  · intro i hi
    rw [show b i=t-a i by have := ht i hi; omega]
  · intro j hj hj'
    exact mul_nonneg (harmonicCoeff_pos Y h₁ j hh₁ hY).le
      (harmonicCoeff_pos Y h₂ (t-j) hh₂ hY).le
lemma separating_node_deficits (g₁ g₂ pivot l u : ℕ) (d₁ d₂ : List ℕ)
    (hs₁ : Stable g₁ (d₁.length+1)) (hs₂ : Stable g₂ (d₂.length+1))
    (hu : u ∈ Finset.range (pivot+l-1))
    (hd₁ : u+d₁.sum ≤ dimension g₁ (d₁.length+1))
    (hd₂ : (pivot+l-2-u)+d₂.sum ≤ dimension g₂ (d₂.length+1))
    (hd : (pivot :: (d₁++d₂)).sum ≤ dimension (g₁+g₂) ((d₁++d₂).length+1))
    (hl : l ≤ deficit (g₁+g₂) (pivot :: (d₁++d₂))) :
    deficit g₁ (u::d₁)+deficit g₂ ((pivot+l-2-u)::d₂) =
      deficit (g₁+g₂) (pivot :: (d₁++d₂))-l := by
  have hu' := Finset.mem_range.mp hu
  unfold Stable at hs₁ hs₂
  unfold deficit dimension at *
  simp only [List.sum_cons,List.sum_append,List.length_cons,List.length_append] at *
  omega
lemma separating_node_deficit_injective (g : ℕ) (d : List ℕ) (u v : ℕ)
    (hu : u+d.sum ≤ dimension g (d.length+1))
    (hv : v+d.sum ≤ dimension g (d.length+1))
    (he : deficit g (u::d)=deficit g (v::d)) : u=v := by
  unfold deficit at he
  simp only [List.length_cons,List.sum_cons] at he
  omega
def separatingValidNodes (g₁ g₂ pivot l : ℕ) (d₁ d₂ : List ℕ) : Finset ℕ :=
  (Finset.range (pivot+l-1)).filter fun u =>
    u+d₁.sum ≤ dimension g₁ (d₁.length+1) ∧
      (pivot+l-2-u)+d₂.sum ≤ dimension g₂ (d₂.length+1)
lemma separating_node_convolution (g₁ g₂ pivot l : ℕ) (d₁ d₂ : List ℕ)
    (hs₁ : Stable g₁ (d₁.length+1)) (hs₂ : Stable g₂ (d₂.length+1))
    (hd : (pivot :: (d₁++d₂)).sum ≤ dimension (g₁+g₂) ((d₁++d₂).length+1))
    (hl : l ≤ deficit (g₁+g₂) (pivot :: (d₁++d₂)))
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    (∑ u ∈ separatingValidNodes g₁ g₂ pivot l d₁ d₂,
      harmonicCoeff Y (complexity g₁ (d₁.length+1)) (deficit g₁ (u::d₁))*
      harmonicCoeff Y (complexity g₂ (d₂.length+1)) (deficit g₂ ((pivot+l-2-u)::d₂))) ≤
      harmonicCoeff Y (complexity g₁ (d₁.length+1)+complexity g₂ (d₂.length+1))
        (deficit (g₁+g₂) (pivot :: (d₁++d₂))-l) := by
  apply harmonicCoeff_partial_convolution
  · unfold Stable at hs₁
    unfold complexity
    omega
  · unfold Stable at hs₂
    unfold complexity
    omega
  · exact hY
  · intro u hu v hv he
    have hu' := (Finset.mem_filter.mp hu).2.1
    have hv' := (Finset.mem_filter.mp hv).2.1
    exact separating_node_deficit_injective g₁ d₁ u v hu' hv' he
  · intro u hu
    have hu' := Finset.mem_filter.mp hu
    exact separating_node_deficits g₁ g₂ pivot l u d₁ d₂ hs₁ hs₂ hu'.1 hu'.2.1 hu'.2.2 hd hl
lemma separating_complexity_add (g₁ g₂ : ℕ) (d₁ d₂ : List ℕ)
    (hs₁ : Stable g₁ (d₁.length+1)) (hs₂ : Stable g₂ (d₂.length+1)) :
    complexity g₁ (d₁.length+1)+complexity g₂ (d₂.length+1)+1 =
      complexity (g₁+g₂) ((d₁++d₂).length+1) := by
  unfold complexity Stable at *
  simp only [List.length_append]
  omega
lemma validModel_ofNat_map (g : ℕ) (d : List ℕ) (Y : ℝ) (hs : Stable g d.length) :
    validModel g (d.map Int.ofNat) Y =
      if d.sum ≤ dimension g d.length then model g d Y else 0 := by
  have hc : ∀ k ∈ d.map Int.ofNat, 0 ≤ k := by
    intro k hk
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hk
    exact Int.natCast_nonneg _
  have hmap : (d.map Int.ofNat).map Int.toNat=d := by
    rw [List.map_map]
    change d.map (fun x => x)=d
    simp only [List.map_id_fun',id_eq]
  unfold validModel
  rw [hmap]
  simp only [List.length_map]
  by_cases hd : d.sum ≤ dimension g d.length
  · rw [if_pos ⟨hc,hs,hd⟩,if_pos hd]
  · rw [if_neg (by intro h; exact hd h.2.2),if_neg hd]
lemma validModel_separating_normalization (g₁ g₂ pivot l u : ℕ) (d₁ d₂ : List ℕ)
    (hs₁ : Stable g₁ (d₁.length+1)) (hs₂ : Stable g₂ (d₂.length+1))
    (hu : u ∈ Finset.range (pivot+l-1))
    (hd : (pivot :: (d₁++d₂)).sum ≤ dimension (g₁+g₂) ((d₁++d₂).length+1))
    (hl : l ≤ deficit (g₁+g₂) (pivot :: (d₁++d₂)))
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    theta Y l/2*validModel g₁ ((u : ℤ)::d₁.map Int.ofNat) Y*
      validModel g₂ (((pivot : ℤ)+l-2-u)::d₂.map Int.ofNat) Y/
      model (g₁+g₂) (pivot :: (d₁++d₂)) Y =
      if u ∈ separatingValidNodes g₁ g₂ pivot l d₁ d₂ then
        theta Y l/6*(Real.Gamma (complexity g₁ (d₁.length+1))*Real.Gamma (complexity g₂ (d₂.length+1))/
          Real.Gamma (complexity (g₁+g₂) ((d₁++d₂).length+1)))*
          (harmonicCoeff Y (complexity g₁ (d₁.length+1)) (deficit g₁ (u::d₁))*
            harmonicCoeff Y (complexity g₂ (d₂.length+1)) (deficit g₂ ((pivot+l-2-u)::d₂))/
            harmonicCoeff Y (complexity (g₁+g₂) ((d₁++d₂).length+1))
              (deficit (g₁+g₂) (pivot::(d₁++d₂)))) else 0 := by
  have hu' := Finset.mem_range.mp hu
  have hcast : (pivot : ℤ)+l-2-u = ((pivot+l-2-u : ℕ) : ℤ) := by omega
  rw [hcast]
  have h₁ : Stable g₁ (u::d₁).length := by simpa only [List.length_cons] using hs₁
  have h₂ : Stable g₂ ((pivot+l-2-u)::d₂).length := by simpa only [List.length_cons] using hs₂
  change theta Y l/2*validModel g₁ ((u::d₁).map Int.ofNat) Y*
      validModel g₂ (((pivot+l-2-u)::d₂).map Int.ofNat) Y/_ = _
  rw [validModel_ofNat_map g₁ (u::d₁) Y h₁,
    validModel_ofNat_map g₂ ((pivot+l-2-u)::d₂) Y h₂]
  by_cases hd₁ : u+d₁.sum ≤ dimension g₁ (d₁.length+1)
  · by_cases hd₂ : (pivot+l-2-u)+d₂.sum ≤ dimension g₂ (d₂.length+1)
    · have hv : u ∈ separatingValidNodes g₁ g₂ pivot l d₁ d₂ := Finset.mem_filter.mpr ⟨hu,hd₁,hd₂⟩
      simp only [List.sum_cons,List.length_cons,hd₁,hd₂,ite_true,hv]
      exact model_separating_ratio (g₁+g₂) g₁ g₂ (pivot::(d₁++d₂)) (u::d₁) ((pivot+l-2-u)::d₂) l Y rfl
        (by have hc := separating_complexity_add g₁ g₂ d₁ d₂ hs₁ hs₂; simpa only [List.length_cons] using (show 1 ≤ complexity (g₁+g₂) ((d₁++d₂).length+1) by omega))
        (by simpa only [List.length_cons] using separating_complexity_add g₁ g₂ d₁ d₂ hs₁ hs₂) hY
    · have hv : u ∉ separatingValidNodes g₁ g₂ pivot l d₁ d₂ := by
        intro h
        exact hd₂ (Finset.mem_filter.mp h).2.2
      simp only [List.sum_cons,List.length_cons,hd₂,ite_false,hv,mul_zero,zero_div]
  · have hv : u ∉ separatingValidNodes g₁ g₂ pivot l d₁ d₂ := by
      intro h
      exact hd₁ (Finset.mem_filter.mp h).2.1
    simp only [List.sum_cons,List.length_cons,hd₁,ite_false,hv,mul_zero,zero_mul,zero_div]
lemma validModel_separating_node_sum (g₁ g₂ pivot l : ℕ) (d₁ d₂ : List ℕ)
    (hs₁ : Stable g₁ (d₁.length+1)) (hs₂ : Stable g₂ (d₂.length+1))
    (hd : (pivot :: (d₁++d₂)).sum ≤ dimension (g₁+g₂) ((d₁++d₂).length+1))
    (hl : l ≤ deficit (g₁+g₂) (pivot :: (d₁++d₂)))
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) :
    (∑ u ∈ Finset.range (pivot+l-1), theta Y l/2*
      validModel g₁ ((u : ℤ)::d₁.map Int.ofNat) Y*
      validModel g₂ (((pivot : ℤ)+l-2-u)::d₂.map Int.ofNat) Y/
      model (g₁+g₂) (pivot :: (d₁++d₂)) Y) ≤
      (Real.Gamma (complexity g₁ (d₁.length+1))*Real.Gamma (complexity g₂ (d₂.length+1))/
        Real.Gamma (complexity (g₁+g₂) ((d₁++d₂).length+1)))/6*
          linearQ Y (complexity (g₁+g₂) ((d₁++d₂).length+1))
            (deficit (g₁+g₂) (pivot::(d₁++d₂))) l := by
  let h₁ := complexity g₁ (d₁.length+1)
  let h₂ := complexity g₂ (d₂.length+1)
  let h := complexity (g₁+g₂) ((d₁++d₂).length+1)
  let m := deficit (g₁+g₂) (pivot::(d₁++d₂))
  let G : ℝ := Real.Gamma h₁*Real.Gamma h₂/Real.Gamma h
  let C : ℝ := theta Y l/6*G/harmonicCoeff Y h m
  have hh₁ : 1 ≤ h₁ := by dsimp only [h₁]; unfold Stable at hs₁; unfold complexity; omega
  have hh₂ : 1 ≤ h₂ := by dsimp only [h₂]; unfold Stable at hs₂; unfold complexity; omega
  have hh : h₁+h₂+1=h := separating_complexity_add g₁ g₂ d₁ d₂ hs₁ hs₂
  have hh₀ : 1 ≤ h := by omega
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact div_nonneg (mul_nonneg (Real.Gamma_pos_of_pos (by exact_mod_cast (show 0<h₁ by omega))).le
      (Real.Gamma_pos_of_pos (by exact_mod_cast (show 0<h₂ by omega))).le)
      (Real.Gamma_pos_of_pos (by exact_mod_cast (show 0<h by omega))).le
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (div_nonneg (theta_nonneg Y hY l) (by norm_num)) hG)
    (harmonicCoeff_pos Y h m hh₀ hY).le
  let T := fun u => theta Y l/2*validModel g₁ ((u : ℤ)::d₁.map Int.ofNat) Y*
      validModel g₂ (((pivot : ℤ)+l-2-u)::d₂.map Int.ofNat) Y/
      model (g₁+g₂) (pivot :: (d₁++d₂)) Y
  let F := fun u => harmonicCoeff Y h₁ (deficit g₁ (u::d₁))*
      harmonicCoeff Y h₂ (deficit g₂ ((pivot+l-2-u)::d₂))
  have hnorm (u : ℕ) (hu : u ∈ Finset.range (pivot+l-1)) :
      T u = if u ∈ separatingValidNodes g₁ g₂ pivot l d₁ d₂ then C*F u else 0 := by
    have he := validModel_separating_normalization g₁ g₂ pivot l u d₁ d₂ hs₁ hs₂ hu hd hl Y hY
    dsimp only [T]
    rw [he]
    split_ifs <;> dsimp only [C,G,F,h₁,h₂,h,m] <;> ring
  have hsub : separatingValidNodes g₁ g₂ pivot l d₁ d₂ ⊆ Finset.range (pivot+l-1) := Finset.filter_subset _ _
  change (∑ u ∈ Finset.range (pivot+l-1), T u) ≤ _
  calc
    _ = ∑ u ∈ separatingValidNodes g₁ g₂ pivot l d₁ d₂, T u := by
      apply (Finset.sum_subset hsub _).symm
      intro u hu hnot
      rw [hnorm u hu,if_neg hnot]
    _ = C*(∑ u ∈ separatingValidNodes g₁ g₂ pivot l d₁ d₂, F u) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [hnorm u (hsub hu),if_pos hu]
    _ ≤ C*harmonicCoeff Y (h₁+h₂) (m-l) :=
      mul_le_mul_of_nonneg_left (separating_node_convolution g₁ g₂ pivot l d₁ d₂ hs₁ hs₂ hd hl Y hY) hC
    _ = _ := by
      change C*harmonicCoeff Y (h₁+h₂) (m-l) = G/6*linearQ Y h m l
      dsimp only [C]
      unfold linearQ
      rw [show h-1=h₁+h₂ by omega]
      ring
end WP
