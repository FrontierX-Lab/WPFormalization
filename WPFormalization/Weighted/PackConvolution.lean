import WPFormalization.Weighted.SeparatingPack

/-! The original separating pack bounded by the full node convolution with a uniform node envelope. -/
noncomputable section
namespace WP
lemma separatingPack_node_bound (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l i : ℕ) (I : Finset ℕ)
    (hi : i≤g) (hd : (pivot::d).sum≤dimension g (d.length+1))
    (hl : l≤deficit g (pivot::d)) (hY : Y ∈ Set.Icc 0 y₀) :
    let e₁ := selectedNat d I
    let e₂ := selectedNat d ((Finset.range d.length)\I)
    Stable i (e₁.length+1) → Stable (g-i) (e₂.length+1) → ∀ E : ℝ, 0≤E →
    (∀ u ∈ separatingValidNodes i (g-i) pivot l e₁ e₂,
      (clippedWeight c (u::e₁)*clippedWeight c ((pivot+l-2-u)::e₂)/clippedWeight c (pivot::d))*
        Real.exp ((1/12 : ℝ)*min (complexity i (e₁.length+1)) (complexity (g-i) (e₂.length+1)))≤E) →
    separatingPack c Y g pivot d l (i,I)≤
      ((Real.Gamma (complexity i (e₁.length+1))*Real.Gamma (complexity (g-i) (e₂.length+1))/
        Real.Gamma (complexity g (d.length+1)))/6*
        linearQ Y (complexity g (d.length+1)) (deficit g (pivot::d)) l)*E := by
  dsimp only
  intro hs₁ hs₂ E hE hF
  let e₁ := selectedNat d I
  let e₂ := selectedNat d ((Finset.range d.length)\I)
  have hp : (e₁++e₂).Perm d := selectedNat_partition_perm d I
  have hg : i+(g-i)=g := by omega
  have hlen : (e₁++e₂).length=d.length := hp.length_eq
  have hpar := List.Perm.cons pivot hp
  have hDef : deficit g (pivot::(e₁++e₂))=deficit g (pivot::d) := by
    unfold deficit
    rw [hpar.length_eq,hpar.sum_eq]
  have hd' : (pivot::(e₁++e₂)).sum≤dimension (i+(g-i)) ((e₁++e₂).length+1) := by
    rw [hg,hpar.sum_eq,hlen]
    exact hd
  have hl' : l≤deficit (i+(g-i)) (pivot::(e₁++e₂)) := by rw [hg,hDef]; exact hl
  let F := fun u => (clippedWeight c (u::e₁)*clippedWeight c ((pivot+l-2-u)::e₂)/clippedWeight c (pivot::d))*
    Real.exp ((1/12 : ℝ)*min (complexity i (e₁.length+1)) (complexity (g-i) (e₂.length+1)))
  have he := validModel_separating_node_weighted_sum i (g-i) pivot l e₁ e₂ hs₁ hs₂ hd' hl' Y hY F E hE hF
  rw [hg,model_perm g hpar Y,hDef,hlen] at he
  rw [separatingPack_nat_eq]
  exact he
end WP
