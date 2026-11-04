import WPFormalization.Weighted.NodeConvolution
import WPFormalization.Weighted.ActiveDimension

/-! Actual model permutation, unstable and genus-zero support rules, and weighted node convolution. -/
noncomputable section
namespace WP
lemma model_perm (g : ℕ) {d e : List ℕ} (hp : d.Perm e) (Y : ℝ) : model g d Y=model g e Y := by
  unfold model deficit
  rw [hp.length_eq,hp.sum_eq]
lemma validModel_unstable_zero (g : ℕ) (d : List ℤ) (Y : ℝ) (hs : ¬ Stable g d.length) :
    validModel g d Y=0 := by
  unfold validModel
  apply if_neg
  intro h
  exact hs h.2.1
lemma separatingValidNodes_genus_zero_empty (g₂ pivot l : ℕ) (d₁ d₂ : List ℕ)
    (hs₁ : Stable 0 (d₁.length+1)) (hi : inactive d₁<2) :
    separatingValidNodes 0 g₂ pivot l d₁ d₂=∅ := by
  ext u
  simp only [separatingValidNodes,Finset.mem_filter,Finset.notMem_empty,iff_false]
  intro h
  have he := genus_zero_inactive_surplus u d₁ h.2.1 hs₁
  omega
lemma validModel_separating_node_weighted_sum (g₁ g₂ pivot l : ℕ) (d₁ d₂ : List ℕ)
    (hs₁ : Stable g₁ (d₁.length+1)) (hs₂ : Stable g₂ (d₂.length+1))
    (hd : (pivot :: (d₁++d₂)).sum ≤ dimension (g₁+g₂) ((d₁++d₂).length+1))
    (hl : l ≤ deficit (g₁+g₂) (pivot :: (d₁++d₂)))
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (F : ℕ → ℝ) (E : ℝ) (hE : 0≤E)
    (hF : ∀ u ∈ separatingValidNodes g₁ g₂ pivot l d₁ d₂, F u≤E) :
    (∑ u ∈ Finset.range (pivot+l-1), (theta Y l/2*
      validModel g₁ ((u : ℤ)::d₁.map Int.ofNat) Y*
      validModel g₂ (((pivot : ℤ)+l-2-u)::d₂.map Int.ofNat) Y/
      model (g₁+g₂) (pivot :: (d₁++d₂)) Y)*F u) ≤
      ((Real.Gamma (complexity g₁ (d₁.length+1))*Real.Gamma (complexity g₂ (d₂.length+1))/
        Real.Gamma (complexity (g₁+g₂) ((d₁++d₂).length+1)))/6*
          linearQ Y (complexity (g₁+g₂) ((d₁++d₂).length+1))
            (deficit (g₁+g₂) (pivot::(d₁++d₂))) l)*E := by
  let T := fun u => theta Y l/2*validModel g₁ ((u : ℤ)::d₁.map Int.ofNat) Y*
      validModel g₂ (((pivot : ℤ)+l-2-u)::d₂.map Int.ofNat) Y/
      model (g₁+g₂) (pivot :: (d₁++d₂)) Y
  have hs : Stable (g₁+g₂) (pivot :: (d₁++d₂)).length := by
    unfold Stable at *
    simp only [List.length_cons,List.length_append]
    omega
  have hT (u : ℕ) : 0≤T u := by
    dsimp only [T]
    exact div_nonneg (mul_nonneg (mul_nonneg (div_nonneg (theta_nonneg Y hY l) (by norm_num))
      (validModel_nonneg _ _ Y hY)) (validModel_nonneg _ _ Y hY)) (model_pos _ _ Y hs hY).le
  have hpart (u : ℕ) (hu : u ∈ Finset.range (pivot+l-1)) : T u*F u≤T u*E := by
    by_cases hv : u ∈ separatingValidNodes g₁ g₂ pivot l d₁ d₂
    · exact mul_le_mul_of_nonneg_left (hF u hv) (hT u)
    · have he := validModel_separating_normalization g₁ g₂ pivot l u d₁ d₂ hs₁ hs₂ hu hd hl Y hY
      rw [if_neg hv] at he
      change T u=0 at he
      rw [he,zero_mul,zero_mul]
  calc
    _ ≤ ∑ u ∈ Finset.range (pivot+l-1), T u*E := Finset.sum_le_sum hpart
    _ = (∑ u ∈ Finset.range (pivot+l-1), T u)*E := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (validModel_separating_node_sum g₁ g₂ pivot l d₁ d₂ hs₁ hs₂ hd hl Y hY) hE
end WP
