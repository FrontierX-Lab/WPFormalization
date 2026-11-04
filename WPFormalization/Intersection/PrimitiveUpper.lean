import WPFormalization.Intersection.PrimitiveEndpointBounds
import WPFormalization.Intersection.PrimitiveInitialUpper
/-! The complete upper half of Appendix B, Lemma B.1. Actual positive
intersection numbers satisfy the scalar majorant by strong complexity
induction: finite initial cases, dilaton, a minimal pivot, exact normalized
DVV, genuine one/two-zero handle bounds, and the full separating estimate.
All local child-bound hypotheses are discharged by that induction. The only
deferred inputs are the registered classical one/two-point estimates used in
the finite initial branch. -/
noncomputable section
namespace WP
lemma sum_range_two_endpoints (p : ℕ) (hp : 3 ≤ p) (f : ℕ → ℝ) (B T : ℝ)
    (h₀ : f 0 ≤ T) (h₁ : f (p-2) ≤ T)
    (hmid : ∀ u ∈ Finset.range (p-1), u ≠ 0 → u ≠ p-2 → f u ≤ B) :
    (∑ u ∈ Finset.range (p-1), f u) ≤ (p-3 : ℕ)*B+2*T := by
  rw [show p-1 = (p-3)+2 by omega,Finset.sum_range_succ,Finset.sum_range_succ']
  have hsum : (∑ i ∈ Finset.range (p-3), f (i+1)) ≤ (p-3 : ℕ)*B := by
    calc
      _ ≤ ∑ i ∈ Finset.range (p-3), B := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        exact hmid (i+1) (Finset.mem_range.mpr (by omega)) (by omega) (by omega)
      _ = _ := by simp
  have hend : f (p-3+1) ≤ T := by simpa only [show p-3+1=p-2 by omega] using h₁
  linarith
lemma primitiveUpper_core_step (P : PsiTheory) (g pivot : ℕ) (d : List ℤ)
    (hg : 3 ≤ g) (hp : 2 ≤ pivot) (hd : ∀ k ∈ d, (pivot : ℤ) ≤ k)
    (hdim : ((pivot : ℤ) :: d).sum = 3*(g : ℤ)-3+(d.length+1))
    (hh : 8 ≤ complexity g (d.length+1))
    (hpositive : ∀ g' c, 1 ≤ g' → Stable g' c.length → (∀ k ∈ c, 0 < k) →
      c.sum = 3*(g' : ℤ)-3+c.length → complexity g' c.length < complexity g (d.length+1) →
      signedPureC P g' c ≤ primitiveMajorant (complexity g' c.length)) :
    signedPureC P g ((pivot : ℤ) :: d) ≤ primitiveMajorant (complexity g (d.length+1)) := by
  let h := complexity g (d.length+1)
  let B := primitiveMajorant ((h : ℝ)-1)
  have hhR : (8 : ℝ) ≤ h := by exact_mod_cast hh
  have h₁ : (0 : ℝ) < (h : ℝ)-1 := by linarith
  have h₂ : (0 : ℝ) < (h : ℝ)-2 := by linarith
  have h₃ : (0 : ℝ) < (h : ℝ)-3 := by linarith
  have h₄ : (0 : ℝ) < (h : ℝ)-4 := by linarith
  have hB₀ : 0 ≤ B := primitiveMajorant_nonneg _
  have hB₁ : B ≤ 1 := primitiveMajorant_le_one _
  have hd₂ : ∀ k ∈ d, 2 ≤ k := by
    intro k hk
    have hv := hd k hk
    omega
  have hc₀ : complexity (g-1) (d.length+2) = h-1 := by dsimp only [h]; unfold complexity; omega
  have hc₁ : complexity (g-1) (d.length+1) ≤ h-1 := by dsimp only [h]; unfold complexity; omega
  have hc₂ : complexity (g-1) d.length ≤ h-1 := by dsimp only [h]; unfold complexity; omega
  have hcast : ((h-1 : ℕ) : ℝ) = (h : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hpB : primitivePositiveBound P (g-1) (h-1) B := by
    intro c hs hc hdimc hK
    have hlt : complexity (g-1) c.length < h := by omega
    have hb := hpositive (g-1) c (by omega) hs hc hdimc hlt
    have hKR : (complexity (g-1) c.length : ℝ) ≤ (h : ℝ)-1 := by
      rw [← hcast]
      exact_mod_cast hK
    exact hb.trans (primitiveMajorant_monotone hKR)
  have hsep : (∑ u ∈ Finset.range (pivot-1), ∑ g₁ ∈ Finset.range (g+1),
      ∑ I ∈ (Finset.range d.length).powerset, primitiveSeparatingTerm P g pivot d u g₁ I) ≤
        2/(((h : ℝ)-1)*((h : ℝ)-2)) := by
    have hdall : ∀ k ∈ (pivot : ℤ) :: d, 2 ≤ k := by
      intro k hk
      rcases List.mem_cons.mp hk with hk | hk
      · subst k; omega
      · exact hd₂ k hk
    exact primitiveSeparating_bound P g pivot d (by omega) hdall hdim
      (by
        intro g' c hg' hs hc hz hdc hlt
        exact signedPrimitive_one_zero_upper_aux P h hpositive c.length g' c hg' rfl hs hc hz hdc hlt)
  have hmerge : ∀ j ∈ Finset.range d.length,
      signedPureC P g (((pivot : ℤ)+d[j]!-1) :: d.eraseIdx j) ≤ B := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    let c := ((pivot : ℤ)+d[j]!-1) :: d.eraseIdx j
    have hlen : c.length = d.length := by
      dsimp only [c]
      simp only [List.length_cons,List.length_eraseIdx_of_lt hj']
      omega
    have hc : complexity g c.length = h-1 := by rw [hlen]; dsimp only [h]; unfold complexity; omega
    have hcpos : ∀ k ∈ c, 0 < k := by
      intro k hk
      rcases List.mem_cons.mp hk with hk | hk
      · subst k
        have hv : 2 ≤ d[j]! := by
          apply hd₂
          simpa [hj'] using (List.getElem_mem (l := d) j hj')
        omega
      · have := hd₂ k (List.mem_of_mem_eraseIdx hk); omega
    have hs : Stable g c.length := by unfold Stable; omega
    have hb := hpositive g c (by omega) hs hcpos (merger_dimension g pivot d hdim j hj') (by omega)
    rw [hc,hcast] at hb
    exact hb
  let f := fun u : ℕ => signedPureC P (g-1) ((u : ℤ) :: ((pivot : ℤ)-2-u) :: d)
  by_cases hp₂ : pivot = 2
  · subst pivot
    have hdc : (0 :: 0 :: d).sum = 3*((g-1 : ℕ) : ℤ)-3+(d.length+2) := by
      simpa only [Nat.cast_zero,Nat.cast_ofNat,sub_self,sub_zero,List.length_cons,
        Nat.cast_add,Nat.cast_one,show (d.length : ℤ)+1+1=d.length+2 by omega] using contraction_dimension g (by omega) 2 d (by simpa using hdim) 0
    have hb := signedPrimitive_two_zero_upper P (g-1) (h-1) B (by omega) hB₀ d hd₂ hdc hc₂ hpB
    have hb' : f 0 ≤ doubleZeroStringFactor h * B := by
      dsimp only [f]
      norm_num only [Nat.cast_zero,Nat.cast_ofNat,sub_self,sub_zero]
      rw [hc₀,hcast] at hb
      simp only [show (h : ℝ)-1-1=h-2 by ring,show (h : ℝ)-1-3=h-4 by ring] at hb
      rw [doubleZeroStringFactor_expansion h hhR] at hb
      exact hb
    have hn : (∑ u ∈ Finset.range (2-1), f u) ≤ (2-1 : ℕ)*B+(doubleZeroStringFactor h-1)*B := by
      norm_num only [show (2-1 : ℕ)=1 by decide,Finset.sum_range_one,Nat.cast_one,one_mul]
      nlinarith [hb']
    have hu := signedPrimitive_upper_from_children P g 2 d (by omega) (by omega)
      (fun k hk => le_trans (by norm_num) (hd₂ k hk)) (by omega) hdim B
      ((doubleZeroStringFactor h-1)*B) (2/(((h : ℝ)-1)*((h : ℝ)-2))) hmerge hn hsep
    change signedPureC P g ((2 : ℤ) :: d) ≤
      B+(2/(3*((h : ℝ)-1)))*((doubleZeroStringFactor h-1)*B)+
        2/(((h : ℝ)-1)*((h : ℝ)-2)) at hu
    have hR₀ : 0 ≤ doubleZeroStringFactor h-1 := by
      rw [← doubleZeroStringFactor_expansion h hhR]
      have hq₁ : 0 ≤ (1 : ℝ)/(3*((h : ℝ)-2)) := by positivity
      have hq₂ : 0 ≤ (2 : ℝ)/(3*((h : ℝ)-4)) := by positivity
      nlinarith [mul_nonneg hq₁ hq₂]
    have he : (2/(3*((h : ℝ)-1)))*((doubleZeroStringFactor h-1)*B) ≤
        2*(doubleZeroStringFactor h-1)/(3*((h : ℝ)-1)) := by
      have hcoef : 0 ≤ (2/(3*((h : ℝ)-1)))*(doubleZeroStringFactor h-1) := by positivity
      have he := mul_le_mul_of_nonneg_left hB₁ hcoef
      nlinarith [show (2/(3*((h : ℝ)-1)))*(doubleZeroStringFactor h-1) =
        2*(doubleZeroStringFactor h-1)/(3*((h : ℝ)-1)) by ring]
    have hclosure := primitive_low_degree_closure hhR
    change _ ≤ primitiveMajorant (h : ℝ)
    change _ < primitiveMajorant (h : ℝ)-B at hclosure
    exact hu.trans (by linarith only [he,hclosure])
  · have hp₃ : 3 ≤ pivot := by omega
    let q : ℝ := 2/(3*((h : ℝ)-3))
    have hq : 0 ≤ q := by dsimp only [q]; positivity
    have hdc : (0 :: ((pivot : ℤ)-2) :: d).sum = 3*((g-1 : ℕ) : ℤ)-3+(d.length+2) := by
      simpa only [Nat.cast_zero,sub_zero,List.length_cons,Nat.cast_add,Nat.cast_one,show (d.length : ℤ)+1+1=d.length+2 by omega]
        using contraction_dimension g (by omega) pivot d (by simpa using hdim) 0
    have hb := signedPrimitive_zero_one_node_upper P (g-1) (h-1) B (by omega) hB₀
      ((pivot : ℤ)-2) (by omega) d hd₂ hdc hc₁ hpB
    have hend₀ : f 0 ≤ (1+q)*B := by
      dsimp only [f]
      simp only [Nat.cast_zero,sub_zero]
      rw [hc₀,hcast] at hb
      simpa only [q,show (h : ℝ)-1-2=h-3 by ring] using hb
    have hend₁ : f (pivot-2) ≤ (1+q)*B := by
      have hi : ((pivot-2 : ℕ) : ℤ) = (pivot : ℤ)-2 := by omega
      dsimp only [f]
      rw [hi,show (pivot : ℤ)-2-((pivot : ℤ)-2)=0 by ring,
        signedPureC_perm P (g-1) (List.Perm.swap (0 : ℤ) ((pivot : ℤ)-2) d)]
      simpa only [f,Nat.cast_zero,sub_zero] using hend₀
    have hmid : ∀ u ∈ Finset.range (pivot-1), u ≠ 0 → u ≠ pivot-2 → f u ≤ B := by
      intro u hu hu₀ hu₁
      have hu' := Finset.mem_range.mp hu
      let c := (u : ℤ) :: ((pivot : ℤ)-2-u) :: d
      have hc : complexity (g-1) c.length = h-1 := by dsimp only [c]; simpa only [List.length_cons] using hc₀
      have hcp : ∀ k ∈ c, 0 < k := by
        intro k hk
        rcases List.mem_cons.mp hk with hk | hk
        · subst k; omega
        · rcases List.mem_cons.mp hk with hk | hk
          · subst k; omega
          · have := hd₂ k hk; omega
      have hs : Stable (g-1) c.length := by unfold Stable; omega
      have hdimc := contraction_dimension g (by omega) pivot d (by simpa using hdim) u
      have hh' := hpositive (g-1) c (by omega) hs hcp hdimc (by omega)
      rw [hc,hcast] at hh'
      exact hh'
    have hs := sum_range_two_endpoints pivot hp₃ f B ((1+q)*B) hend₀ hend₁ hmid
    have hn : (∑ u ∈ Finset.range (pivot-1), f u) ≤ (pivot-1 : ℕ)*B+2*q*B := by
      have hpc : ((pivot-1 : ℕ) : ℝ) = (pivot-3 : ℕ)+2 := by exact_mod_cast (show pivot-1=pivot-3+2 by omega)
      rw [hpc]
      nlinarith [hs]
    have hu := signedPrimitive_upper_from_children P g pivot d (by omega) (by omega)
      (fun k hk => le_trans (by norm_num) (hd₂ k hk)) (by omega) hdim B
      (2*q*B) (2/(((h : ℝ)-1)*((h : ℝ)-2))) hmerge hn hsep
    have he : (2/(3*((h : ℝ)-1)))*(2*q*B) ≤ 8/(9*((h : ℝ)-1)*((h : ℝ)-3)) := by
      have he := mul_le_mul_of_nonneg_left hB₁ (show 0 ≤ (2/(3*((h : ℝ)-1)))*(2*q) by positivity)
      have heq : (2/(3*((h : ℝ)-1)))*(2*q) = 8/(9*((h : ℝ)-1)*((h : ℝ)-3)) := by
        dsimp only [q]
        field_simp
        <;> ring
      nlinarith [heq]
    have hclosure := primitive_high_degree_excess hhR
    have hincr := primitiveMajorant_increment hhR
    change _ ≤ primitiveMajorant (h : ℝ)
    change primitiveMajorant (h : ℝ)-B = _ at hincr
    linarith [hclosure.1,hclosure.2]
lemma signedPrimitive_initial_upper (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hg : 1 ≤ g) (hs : Stable g d.length) (hd : ∀ k ∈ d, 0 < k)
    (hdim : d.sum = 3*(g : ℤ)-3+d.length) (hh : complexity g d.length ≤ 7) :
    signedPureC P g d ≤ 1/3 := by
  have hdn : ∀ k ∈ d, 0 ≤ k := fun k hk => (hd k hk).le
  have hn : 1 ≤ d.length := by
    cases d with
    | nil => simp only [List.sum_nil,List.length_nil,Nat.cast_zero] at hdim; unfold Stable at hs; omega
    | cons a t => simp
  rw [signedPureC_toNat P g d hdn]
  apply primitive_initial_upper P g (d.map Int.toNat) hg
  · simpa only [List.length_map] using hn
  · intro k hk
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
    have := hd j hj
    omega
  · have he : ((d.map Int.toNat).sum : ℤ) = d.sum := by
      rw [← sum_map_int,map_ofNat_toNat d hdn]
    have hcast := dimension_cast_of_stable g d.length hs
    simp only [List.length_map]
    exact_mod_cast (show ((d.map Int.toNat).sum : ℤ) = (dimension g d.length : ℤ) by omega)
  · simpa only [List.length_map] using hh
lemma signedPrimitive_upper_aux (P : PsiTheory) (h : ℕ) :
    ∀ g : ℕ, ∀ d : List ℤ, 1 ≤ g → Stable g d.length → (∀ k ∈ d, 0 < k) →
      d.sum = 3*(g : ℤ)-3+d.length → complexity g d.length = h →
      signedPureC P g d ≤ primitiveMajorant (complexity g d.length) := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro g d hg hs hd hdim he
    by_cases hsmall : h ≤ 7
    · have hb := signedPrimitive_initial_upper P g d hg hs hd hdim (by omega)
      have hhR : (complexity g d.length : ℝ) ≤ 7 := by exact_mod_cast (show complexity g d.length ≤ 7 by omega)
      simpa only [primitiveMajorant,if_pos hhR] using hb
    · have hlarge : 8 ≤ h := by omega
      have hpositive : ∀ g' c, 1 ≤ g' → Stable g' c.length → (∀ k ∈ c, 0 < k) →
          c.sum = 3*(g' : ℤ)-3+c.length → complexity g' c.length < h →
          signedPureC P g' c ≤ primitiveMajorant (complexity g' c.length) := by
        intro g' c hg' hs' hd' hdim' hlt
        exact ih _ hlt g' c hg' hs' hd' hdim' rfl
      by_cases hone : (1 : ℤ) ∈ d
      · let t := d.erase 1
        have hp : d.Perm (1 :: t) := List.perm_cons_erase hone
        have hl : d.length = t.length+1 := by simpa using hp.length_eq
        have ht : ∀ k ∈ t, 0 < k := fun k hk => hd k (List.mem_of_mem_erase hk)
        have hdim' : t.sum = 3*(g : ℤ)-3+t.length := by
          have hh := hp.sum_eq
          simp only [List.sum_cons] at hh
          rw [hl] at hdim
          push_cast at hdim
          omega
        have hst : Stable g t.length := by
          unfold Stable
          unfold complexity at he
          rw [hl] at he
          omega
        have hlt : complexity g t.length < h := by
          unfold complexity at he ⊢
          rw [hl] at he
          omega
        have hb := hpositive g t hg hst ht hdim' hlt
        have hmono : (complexity g t.length : ℝ) ≤ complexity g d.length := by exact_mod_cast (by omega : complexity g t.length ≤ complexity g d.length)
        rw [signedPureC_perm P g hp,signedPureC_dilaton P g t hst]
        exact hb.trans (primitiveMajorant_monotone hmono)
      · have hd₂ : ∀ k ∈ d, 2 ≤ k := by
          intro k hk
          have hkpos := hd k hk
          have hk1 : k ≠ 1 := fun h => hone (h ▸ hk)
          omega
        have hg₃ : 3 ≤ g := by
          have hsum := twice_length_le_sum d hd₂
          unfold complexity at he
          omega
        have hds : d.toFinset.Nonempty := by
          cases d with
          | nil => simp only [List.sum_nil,List.length_nil,Nat.cast_zero] at hdim; omega
          | cons a t => exact ⟨a,by simp⟩
        let p : ℤ := d.toFinset.min' hds
        have hpmem : p ∈ d := by simpa only [p,List.mem_toFinset] using Finset.min'_mem d.toFinset hds
        have hp₂ : 2 ≤ p := hd₂ p hpmem
        have hpN : 2 ≤ p.toNat := by omega
        have hcast : ((p.toNat : ℕ) : ℤ) = p := Int.toNat_of_nonneg (by omega)
        let t := d.erase p
        have hp : d.Perm (p :: t) := List.perm_cons_erase hpmem
        have hl : d.length = t.length+1 := by simpa using hp.length_eq
        have ht : ∀ k ∈ t, (p.toNat : ℤ) ≤ k := by
          intro k hk
          rw [hcast]
          exact Finset.min'_le d.toFinset k (List.mem_toFinset.mpr (List.mem_of_mem_erase hk))
        have hdim' : ((p.toNat : ℤ) :: t).sum = 3*(g : ℤ)-3+(t.length+1) := by
          rw [hcast,← hp.sum_eq]
          simpa only [hl,Nat.cast_add,Nat.cast_one] using hdim
        have hparent : complexity g (t.length+1) = h := by rw [← hl]; exact he
        have hpos' : ∀ g' c, 1 ≤ g' → Stable g' c.length → (∀ k ∈ c, 0 < k) →
            c.sum = 3*(g' : ℤ)-3+c.length → complexity g' c.length < complexity g (t.length+1) →
            signedPureC P g' c ≤ primitiveMajorant (complexity g' c.length) := by
          intro g' c hg' hs' hd' hdim' hlt
          exact hpositive g' c hg' hs' hd' hdim' (by rwa [hparent] at hlt)
        rw [signedPureC_perm P g hp,hl]
        have hb := primitiveUpper_core_step P g p.toNat t hg₃ hpN ht hdim' (by omega) hpos'
        simpa only [hcast,List.length_cons] using hb
lemma pureC_primitive_upper (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hg : 1 ≤ g) (hn : 1 ≤ d.length) (hd : ∀ k ∈ d, 0 < k)
    (hdim : d.sum = dimension g d.length) : pureC P g d ≤ 1 := by
  have hs : Stable g d.length := by unfold Stable; omega
  have hd' : ∀ k ∈ d.map Int.ofNat, 0 < k := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
    change (0 : ℤ) < (j : ℤ)
    exact_mod_cast hd j hj
  rw [pureC_signed]
  apply le_trans (b := primitiveMajorant (complexity g (d.map Int.ofNat).length))
  · apply signedPrimitive_upper_aux P (complexity g (d.map Int.ofNat).length)
      g (d.map Int.ofNat) hg
    · simpa only [List.length_map] using hs
    · exact hd'
    · rw [sum_map_int,hdim,List.length_map]
      exact dimension_cast_of_stable g d.length hs
    · rfl
  · exact primitiveMajorant_le_one _
end WP
