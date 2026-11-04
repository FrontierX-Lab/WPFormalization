import WPFormalization.Weighted.NodeBounds
import WPFormalization.Weighted.TwoColorLabels

/-! Actual finite separating packs, nonnegativity, exact rearrangement, and left/right involution. -/
noncomputable section
namespace WP
lemma sum_le_twice_oriented {α : Type*} [DecidableEq α]
    (s : Finset α) (τ : α → α) (f : α → ℝ) (P : α → Prop) [DecidablePred P]
    (hmem : ∀ a∈s, τ a∈s) (hinv : ∀ a∈s, τ (τ a)=a)
    (hsym : ∀ a∈s, f (τ a)=f a) (hf : ∀ a∈s, 0≤f a)
    (hcover : ∀ a∈s, P a ∨ P (τ a)) :
    (∑ a∈s, f a)≤2*(∑ a∈s, if P a then f a else 0) := by
  have heq : (∑ a∈s, if P (τ a) then f (τ a) else 0)=(∑ a∈s, if P a then f a else 0) := by
    apply Finset.sum_bij (fun a ha => τ a)
    · exact hmem
    · intro a ha b hb he
      have he' := congrArg τ he
      rwa [hinv a ha,hinv b hb] at he'
    · intro b hb
      exact ⟨τ b,hmem b hb,hinv b hb⟩
    · intro a ha
      rfl
  have hpoint (a : α) (ha : a∈s) : f a≤
      (if P a then f a else 0)+(if P (τ a) then f (τ a) else 0) := by
    by_cases hp : P a
    · rw [if_pos hp]
      have hn : 0 ≤ (if P (τ a) then f (τ a) else 0) := by
        split_ifs
        · exact hf (τ a) (hmem a ha)
        · exact le_rfl
      linarith
    · have hpt := (hcover a ha).resolve_left hp
      rw [if_neg hp,if_pos hpt,hsym a ha,zero_add]
  have hs := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,heq] at hs
  linarith
def separatingLabelSwap (g n : ℕ) (iU : ℕ × Finset ℕ) : ℕ × Finset ℕ :=
  (g-iU.1,(Finset.range n)\iU.2)
lemma separatingLabelSwap_mem (g n : ℕ) (iU : ℕ × Finset ℕ)
    (h : iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range n).powerset) :
    separatingLabelSwap g n iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range n).powerset := by
  simp only [separatingLabelSwap,Finset.mem_product,Finset.mem_range,Finset.mem_powerset]
  exact ⟨by omega,Finset.sdiff_subset⟩
lemma separatingLabelSwap_involutive (g n : ℕ) (iU : ℕ × Finset ℕ)
    (h : iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range n).powerset) :
    separatingLabelSwap g n (separatingLabelSwap g n iU)=iU := by
  have hi := Finset.mem_range.mp (Finset.mem_product.mp h).1
  have hU := Finset.mem_powerset.mp (Finset.mem_product.mp h).2
  apply Prod.ext
  · dsimp only [separatingLabelSwap]
    omega
  · dsimp only [separatingLabelSwap]
    ext j
    simp only [Finset.mem_sdiff]
    constructor
    · intro hj
      by_contra hj'
      exact hj.2 ⟨hj.1,hj'⟩
    · intro hj
      exact ⟨hU hj,fun hbad => hbad.2 hj⟩
def separatingNodeTerm (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l u g₁ : ℕ) (I : Finset ℕ) : ℝ :=
  let d₁ := (u : ℤ)::selected (d.map Int.ofNat) I
  let d₂ := ((pivot : ℤ)+l-2-u)::selected (d.map Int.ofNat) ((Finset.range d.length)\I)
  theta Y l/2*validModel g₁ d₁ Y*validModel (g-g₁) d₂ Y/model g (pivot::d) Y*
    (signedWeight c d₁*signedWeight c d₂/clippedWeight c (pivot::d))*
      Real.exp ((1/12 : ℝ)*min (complexity g₁ d₁.length) (complexity (g-g₁) d₂.length))
def separatingPack (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l : ℕ) (iU : ℕ × Finset ℕ) : ℝ :=
  ∑ u ∈ Finset.range (pivot+l-1), separatingNodeTerm c Y g pivot d l u iU.1 iU.2
lemma separatingNodeTerm_nonneg (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l u g₁ : ℕ) (I : Finset ℕ)
    (hg : 2≤g) (hY : Y ∈ Set.Icc 0 y₀) :
    0 ≤ separatingNodeTerm c Y g pivot d l u g₁ I := by
  unfold separatingNodeTerm
  dsimp only
  apply mul_nonneg
  · apply mul_nonneg
    · apply div_nonneg
      · exact mul_nonneg (mul_nonneg (div_nonneg (theta_nonneg Y hY l) (by norm_num))
          (validModel_nonneg _ _ Y hY)) (validModel_nonneg _ _ Y hY)
      · exact (model_pos g (pivot::d) Y (by unfold Stable; simp only [List.length_cons]; omega) hY).le
    · exact div_nonneg (mul_nonneg (clippedWeight_pos c _).le (clippedWeight_pos c _).le) (clippedWeight_pos c _).le
  · exact (Real.exp_pos _).le
lemma weightedSeparating_eq_packs (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) :
    weightedSeparating c Y g pivot d =
      ∑ l ∈ Finset.range (deficit g (pivot::d)+1),
        ∑ iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range d.length).powerset,
          separatingPack c Y g pivot d l iU := by
  unfold weightedSeparating separatingPack separatingNodeTerm
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_product]
  rw [Finset.sum_comm (s := Finset.range (pivot+l-1))]
  simp_rw [Finset.sum_comm (s := Finset.range (pivot+l-1))]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g₁ hg₁
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring
lemma separatingPack_swap (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l : ℕ) (iU : ℕ × Finset ℕ)
    (h : iU ∈ (Finset.range (g+1)) ×ˢ (Finset.range d.length).powerset) :
    separatingPack c Y g pivot d l (separatingLabelSwap g d.length iU)=
      separatingPack c Y g pivot d l iU := by
  have hi := Finset.mem_range.mp (Finset.mem_product.mp h).1
  have hgenus : g-(g-iU.1)=iU.1 := by omega
  have hcomp := congrArg Prod.snd (separatingLabelSwap_involutive g d.length iU h)
  change (Finset.range d.length)\((Finset.range d.length)\iU.2)=iU.2 at hcomp
  unfold separatingPack
  apply Finset.sum_bij (fun u hu => pivot+l-2-u)
  · intro u hu
    have hu' := Finset.mem_range.mp hu
    exact Finset.mem_range.mpr (by omega)
  · intro u hu v hv he
    have hu' := Finset.mem_range.mp hu
    have hv' := Finset.mem_range.mp hv
    omega
  · intro v hv
    have hv' := Finset.mem_range.mp hv
    refine ⟨pivot+l-2-v,Finset.mem_range.mpr (by omega),?_⟩
    omega
  · intro u hu
    have hu' := Finset.mem_range.mp hu
    have hcast : ((pivot+l-2-u : ℕ) : ℤ)=(pivot : ℤ)+l-2-u := by omega
    have hcast' : (pivot : ℤ)+l-2-((pivot+l-2-u : ℕ) : ℤ)=u := by omega
    unfold separatingNodeTerm separatingLabelSwap
    dsimp only
    rw [hgenus,hcomp,hcast']
    rw [← hcast]
    simp only [List.length_cons]
    simp only [Nat.min_comm]
    ring
lemma signedWeight_ofNat_map (c : ℝ) (d : List ℕ) :
    signedWeight c (d.map Int.ofNat)=clippedWeight c d := by
  unfold signedWeight
  rw [List.map_map]
  change clippedWeight c (d.map (fun x => x))=clippedWeight c d
  simp only [List.map_id_fun',id_eq]
lemma separatingPack_nat_eq (c Y : ℝ) (g pivot : ℕ) (d : List ℕ) (l : ℕ) (iU : ℕ × Finset ℕ) :
    let e₁ := selectedNat d iU.2
    let e₂ := selectedNat d ((Finset.range d.length)\iU.2)
    separatingPack c Y g pivot d l iU =
      ∑ u ∈ Finset.range (pivot+l-1),
        (theta Y l/2*validModel iU.1 ((u : ℤ)::e₁.map Int.ofNat) Y*
          validModel (g-iU.1) (((pivot : ℤ)+l-2-u)::e₂.map Int.ofNat) Y/model g (pivot::d) Y)*
          ((clippedWeight c (u::e₁)*clippedWeight c ((pivot+l-2-u)::e₂)/clippedWeight c (pivot::d))*
            Real.exp ((1/12 : ℝ)*min (complexity iU.1 (e₁.length+1)) (complexity (g-iU.1) (e₂.length+1)))) := by
  dsimp only
  unfold separatingPack
  apply Finset.sum_congr rfl
  intro u hu
  have hu' := Finset.mem_range.mp hu
  have hv : (pivot : ℤ)+l-2-u=((pivot+l-2-u : ℕ) : ℤ) := by omega
  unfold separatingNodeTerm
  dsimp only
  rw [← selectedNat_ofNat d iU.2,← selectedNat_ofNat d ((Finset.range d.length)\iU.2),hv]
  have h₁ : signedWeight c ((u : ℤ)::(selectedNat d iU.2).map Int.ofNat)=
      clippedWeight c (u::selectedNat d iU.2) :=
    signedWeight_ofNat_map c (u::selectedNat d iU.2)
  have h₂ : signedWeight c (((pivot+l-2-u : ℕ) : ℤ)::(selectedNat d ((Finset.range d.length)\iU.2)).map Int.ofNat)=
      clippedWeight c ((pivot+l-2-u)::selectedNat d ((Finset.range d.length)\iU.2)) :=
    signedWeight_ofNat_map c ((pivot+l-2-u)::selectedNat d ((Finset.range d.length)\iU.2))
  rw [h₁,h₂]
  simp only [List.length_cons,List.length_map]
  ring
end WP
