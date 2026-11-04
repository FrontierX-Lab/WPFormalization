import WPFormalization.Intersection.ProfileMonotone
import WPFormalization.Analysis.CriticalKernelLipschitz
import WPFormalization.Marked.Positivity
/-! Homogeneous comparison of the actual positive recursion with its critical
value. Each kernel factor raises complexity by one; separating child
complexities add to the parent complexity minus one. The genuine critical
Lipschitz bound gives the short-window amplitude ratio estimate. -/
noncomputable section
namespace WP
open Set
lemma piSigned_nonneg_nonempty (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hn : 1≤d.length) (Y : ℝ) (hY : Y∈Icc 0 y₀) : 0≤piSigned P g d Y := by
  unfold piSigned
  split_ifs
  · exact normalized_nonneg_nonempty P g _ (by simpa using hn) Y hY
  · exact le_rfl
lemma normalizedChildren_homogeneous_step (P : PsiTheory) (g p h : ℕ) (d : List ℤ)
    (Y u : ℝ) (hY : Y∈Icc 0 y₀) (hu : 1≤u) (hh : 2≤h)
    (he : complexity g (d.length+1)=h) (hd : ∀k∈d,0≤k)
    (ih : ∀ g' : ℕ, ∀ c : List ℤ, 1≤c.length → complexity g' c.length<h →
      piSigned P g' c Y ≤ u^(complexity g' c.length)*piSigned P g' c y₀) :
    normalizedChildren P g p d Y ≤ u^(h-1)*normalizedChildren P g p d y₀ := by
  have hu0 : 0≤u := by linarith
  unfold normalizedChildren
  rw [mul_add,mul_add]
  apply add_le_add
  · apply add_le_add
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      let c := ((p:ℤ)+d[j]!-1)::d.eraseIdx j
      change (2*(d[j]!:ℝ)+1)*piSigned P g c Y ≤
        u^(h-1)*((2*(d[j]!:ℝ)+1)*piSigned P g c y₀)
      have hc : complexity g c.length=h-1 := by
        dsimp only [c]
        simp only [List.length_cons,List.length_eraseIdx_of_lt hj']
        unfold complexity at *
        omega
      have hi := ih g c (by simp [c]) (by omega)
      rw [hc] at hi
      have hcoef : 0≤2*(d[j]!:ℝ)+1 := by
        have hmem : d[j]!∈d := by simpa [hj'] using (List.getElem_mem (l:=d) hj')
        have hk := hd (d[j]!) hmem
        have hk' : (0:ℝ)≤(d[j]!:ℝ) := by exact_mod_cast hk
        linarith
      exact (mul_le_mul_of_nonneg_left hi hcoef).trans_eq (by ring)
    · by_cases hg : g=0
      · simp [hg]
      · simp only [hg,ite_false]
        rw [mul_left_comm (u^(h-1)) (1/2:ℝ)]
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤1/2)
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro v hv
        let c := (v:ℤ)::((p:ℤ)-2-v)::d
        change piSigned P (g-1) c Y ≤ u^(h-1)*piSigned P (g-1) c y₀
        have hc : complexity (g-1) c.length=h-1 := by
          dsimp only [c]
          simp only [List.length_cons]
          unfold complexity at *
          omega
        simpa only [hc] using ih (g-1) c (by simp [c]) (by omega)
  · rw [mul_left_comm (u^(h-1)) (1/2:ℝ)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤1/2)
    simp_rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    apply Finset.sum_le_sum
    intro g₁ hg₁
    apply Finset.sum_le_sum
    intro I hI
    let c₁ : List ℤ := (v:ℤ)::selected d I
    let c₂ : List ℤ := ((p:ℤ)-2-v)::selected d ((Finset.range d.length)\I)
    change piSigned P g₁ c₁ Y*piSigned P (g-g₁) c₂ Y ≤
      u^(h-1)*(piSigned P g₁ c₁ y₀*piSigned P (g-g₁) c₂ y₀)
    by_cases hs₁ : Stable g₁ c₁.length
    · by_cases hs₂ : Stable (g-g₁) c₂.length
      · have hgg : g₁≤g := by have := Finset.mem_range.mp hg₁;omega
        have hpart := selected_partition_length d I
        have hc₁ : complexity g₁ c₁.length<h := by
          dsimp only [c₁,c₂] at hs₁ hs₂ ⊢
          simp only [Stable,List.length_cons] at hs₁ hs₂ ⊢
          unfold complexity at *
          omega
        have hc₂ : complexity (g-g₁) c₂.length<h := by
          dsimp only [c₁,c₂] at hs₁ hs₂ ⊢
          simp only [Stable,List.length_cons] at hs₁ hs₂ ⊢
          unfold complexity at *
          omega
        have hcs : complexity g₁ c₁.length+complexity (g-g₁) c₂.length=h-1 := by
          dsimp only [c₁,c₂] at hs₁ hs₂ ⊢
          simp only [Stable,List.length_cons] at hs₁ hs₂ ⊢
          unfold complexity at *
          omega
        have hi₁ := ih g₁ c₁ (by simp [c₁]) hc₁
        have hi₂ := ih (g-g₁) c₂ (by simp [c₂]) hc₂
        have hn₂ := piSigned_nonneg_nonempty P (g-g₁) c₂ (by simp [c₂]) Y hY
        have hn₁ := mul_nonneg (pow_nonneg hu0 (complexity g₁ c₁.length)) (piSigned_critical_nonneg P g₁ c₁)
        calc _ ≤ (u^(complexity g₁ c₁.length)*piSigned P g₁ c₁ y₀)*
              (u^(complexity (g-g₁) c₂.length)*piSigned P (g-g₁) c₂ y₀) :=
                mul_le_mul hi₁ hi₂ hn₂ hn₁
             _ = u^(complexity g₁ c₁.length+complexity (g-g₁) c₂.length)*
                (piSigned P g₁ c₁ y₀*piSigned P (g-g₁) c₂ y₀) := by rw [pow_add];ring
             _ = _ := by rw [hcs]
      · rw [piSigned_unstable P _ _ Y hs₂,piSigned_unstable P _ _ y₀ hs₂]
        simp
    · rw [piSigned_unstable P _ _ Y hs₁,piSigned_unstable P _ _ y₀ hs₁]
      simp
lemma normalized_homogeneous_upper_aux (P : PsiTheory) (Y u : ℝ)
    (hY : Y∈Icc 0 y₀) (hu : 1≤u) (hθ : ∀ l,theta Y l≤u) (h : ℕ) :
    ∀ g : ℕ, ∀ d : List ℕ, 1≤d.length → complexity g d.length=h →
      normalized P g d Y ≤ u^h*normalized P g d y₀ := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro g d hn he
    have hu0 : 0≤u := by linarith
    by_cases hs : Stable g d.length
    · by_cases hd : d.sum≤dimension g d.length
      · by_cases htop : d.sum=dimension g d.length
        · have hev : normalized P g d Y=normalized P g d y₀ := by
            rw [normalized_top P g d Y hY htop,
              normalized_top P g d y₀ ⟨y₀_pos.le,le_rfl⟩ htop]
          rw [hev]
          apply le_mul_of_one_le_left (normalized_critical_nonneg P g d)
          have hp := pow_le_pow_left₀ (show (0:ℝ)≤1 by norm_num) hu h
          simpa only [one_pow] using hp
        · by_cases hsmall : h≤1
          · have hg : g=1 := by
              unfold complexity at he
              unfold Stable at hs
              unfold dimension at hd htop
              omega
            have hlen : d.length=1 := by unfold complexity at he;unfold Stable at hs;omega
            subst g
            obtain ⟨p,rfl⟩ := List.length_eq_one_iff.mp hlen
            have hp : p=0 := by
              simp only [List.sum_singleton,List.length_singleton] at hd htop
              norm_num [dimension] at hd htop
              omega
            subst p
            have hh1 : h=1 := by norm_num [complexity] at he;omega
            rw [(initial_amplitudes P Y hY).2.2,
              (initial_amplitudes P y₀ ⟨y₀_pos.le,le_rfl⟩).2.2,
              critical_kernels.2 1,hh1,pow_one]
            have ht := hθ 1
            linarith
          · have hh : 2≤h := by omega
            cases d with
            | nil => simp at hn
            | cons p d =>
              have hhc : 2≤complexity g (d.length+1) := by
                simpa only [List.length_cons] using he.symm ▸ hh
              rw [normalized_positive_convolution P g p d Y hhc hd hY,
                normalized_positive_convolution P g p d y₀ hhc hd ⟨y₀_pos.le,le_rfl⟩,
                Finset.mul_sum]
              apply Finset.sum_le_sum
              intro l hl
              have hchild := normalizedChildren_homogeneous_step P g (p+l) h (d.map Int.ofNat)
                Y u hY hu hh (by simpa only [List.length_map,List.length_cons] using he)
                (by intro k hk;obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hk;exact Int.natCast_nonneg j)
                (by
                  intro g' c hlen hc
                  unfold piSigned
                  split_ifs
                  · simpa only [List.length_map] using ih _ hc g' (c.map Int.toNat)
                      (by simpa only [List.length_map] using hlen) (by simp only [List.length_map])
                  · simp)
              have hnn := normalizedChildren_nonneg_step P g (p+l) (d.map Int.ofNat)
                (by simpa only [List.length_map] using hhc)
                (by intro k hk;obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hk;exact Int.natCast_nonneg j) Y hY
              have hp : u*u^(h-1)=u^h := by
                rw [mul_comm,←pow_succ,Nat.sub_add_cancel (by omega : 1≤h)]
              rw [critical_kernels.2 l,one_mul]
              have hb := mul_le_mul (hθ l) hchild hnn hu0
              simpa only [←mul_assoc,hp] using hb
      · have hex : dimension g d.length<d.sum := by omega
        rw [normalized_excess P g d Y hex,normalized_excess P g d y₀ hex]
        simp
    · rw [normalized_unstable P g d Y hs,normalized_unstable P g d y₀ hs]
      simp
lemma normalized_critical_homogeneous_comparison (P : PsiTheory) (g : ℕ) (d : List ℕ)
    (hn : 1≤d.length) (Y u : ℝ) (hY : Y∈Icc 0 y₀) (hu : 1≤u) (hθ : ∀ l,theta Y l≤u) :
    normalized P g d y₀≤normalized P g d Y ∧
      normalized P g d Y≤u^(complexity g d.length)*normalized P g d y₀ := by
  exact ⟨normalized_pi_le P g d hn Y hY,
    normalized_homogeneous_upper_aux P Y u hY hu hθ _ g d hn rfl⟩
lemma normalized_critical_neighborhood_comparison :
    ∃ C δ₀ : ℝ,0<C ∧ 0<δ₀ ∧ ∀ P : PsiTheory, ∀ g : ℕ, ∀ d : List ℕ,
      1≤d.length → ∀ Y∈Icc (0:ℝ) y₀,y₀-Y≤δ₀ →
      normalized P g d y₀≤normalized P g d Y ∧
      normalized P g d Y≤(1+C*(y₀-Y))^(complexity g d.length)*normalized P g d y₀ := by
  obtain ⟨C,δ,hC,hδ,hθ⟩ := Analysis.theta_critical_lipschitz
  refine ⟨C,δ,hC,hδ,?_⟩
  intro P g d hn Y hY hsmall
  apply normalized_critical_homogeneous_comparison P g d hn Y (1+C*(y₀-Y)) hY
  · have hd : 0≤y₀-Y := by linarith [hY.2]
    nlinarith
  · intro l
    exact (hθ Y hY hsmall l).2
lemma small_homogeneous_power_error (C δ : ℝ) (h : ℕ)
    (hC : 0≤C) (hδ : 0≤δ) (hh : 0<(h:ℝ)) (hCh : C≤h)
    (hsmall : δ≤1/(h:ℝ)^2) : (1+C*δ)^h-1≤2*C/(h:ℝ) := by
  let x : ℝ := (h:ℝ)*(C*δ)
  have hx0 : 0≤x := by dsimp [x];positivity
  have hx : x≤C/(h:ℝ) := by
    apply (le_div_iff₀ hh).mpr
    have hd := (le_div_iff₀ (sq_pos_of_pos hh)).mp hsmall
    dsimp only [x]
    nlinarith [mul_le_mul_of_nonneg_left hd hC]
  have hx1 : |x|≤1 := by
    rw [abs_of_nonneg hx0]
    exact hx.trans ((div_le_one hh).mpr hCh)
  have he : (1+C*δ)^h≤Real.exp x := by
    have hb : 1+C*δ≤Real.exp (C*δ) := by linarith [Real.add_one_le_exp (C*δ)]
    have hp := pow_le_pow_left₀ (show 0≤1+C*δ by positivity) hb h
    simpa only [x,Real.exp_nat_mul] using hp
  calc _ ≤ Real.exp x-1 := sub_le_sub_right he 1
       _ ≤ |Real.exp x-1| := le_abs_self _
       _ ≤ 2*|x| := Real.abs_exp_sub_one_le hx1
       _ = 2*x := by rw [abs_of_nonneg hx0]
       _ ≤ 2*(C/(h:ℝ)) := mul_le_mul_of_nonneg_left hx (by norm_num)
       _ = 2*C/(h:ℝ) := by ring
lemma normalized_zero_critical_window_error (P : PsiTheory) (p : ℕ) (hp : 1≤p) :
    ∃ C δ₀ : ℝ,0<C ∧ 0<δ₀ ∧ ∃ G : ℕ, ∀ g≥G, ∀ Y∈Icc (0:ℝ) y₀,
      y₀-Y≤δ₀ → y₀-Y≤1/(complexity g p:ℝ)^2 →
      |normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀-1|≤
        C/(complexity g p:ℝ) := by
  obtain ⟨C,δ,hC,hδ,hcomp⟩ := normalized_critical_neighborhood_comparison
  obtain ⟨N,hN⟩ := exists_nat_gt C
  refine ⟨2*C,δ,by positivity,hδ,N+2,?_⟩
  intro g hg Y hY hsmall hscale
  have hg₂ : 2≤g := by omega
  have hg₁ : 1≤g := by omega
  have hs : Stable g p := by unfold Stable;omega
  have hW := W_pos P g p hp hs y₀ ⟨y₀_pos.le,le_rfl⟩
  have hcrit : 0<normalized P g (List.replicate p 0) y₀ := by
    rw [W] at hW
    exact (mul_pos_iff_of_pos_left (pow_pos (by norm_num : (0:ℝ)<4) g)).mp hW
  have hgh : g≤complexity g p := by unfold complexity;omega
  have hh : 0<(complexity g p:ℝ) := by exact_mod_cast (show 0<complexity g p by omega)
  have hCh : C≤(complexity g p:ℝ) :=
    hN.le.trans (by exact_mod_cast (show N≤complexity g p by omega))
  have hc := hcomp P g (List.replicate p 0) (by simpa using hp) Y hY hsmall
  have hlo : 1≤normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀ :=
    (le_div_iff₀ hcrit).mpr (by simpa using hc.1)
  have hup : normalized P g (List.replicate p 0) Y/normalized P g (List.replicate p 0) y₀≤
      (1+C*(y₀-Y))^(complexity g p) := (div_le_iff₀ hcrit).mpr (by simpa only [List.length_replicate] using hc.2)
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  exact (sub_le_sub_right hup 1).trans
    (small_homogeneous_power_error C (y₀-Y) (complexity g p) hC.le (by linarith [hY.2]) hh hCh hscale)
end WP
