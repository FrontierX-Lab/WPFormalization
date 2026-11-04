import WPFormalization.Intersection.PositiveRecursion
import WPFormalization.Intersection.PrimitivePositivity
import WPFormalization.Analysis.UniformKernelMoments
/-! The genuine Painleve-I lower comparison.
The critical branch is the explicit degree-two background theory. Strong
induction in stable complexity compares the actual positive kernel recursions,
including signed invalid children, unstable separating factors, and all initial
values. No PI comparison hypothesis is introduced. -/
noncomputable section
namespace WP
open Set

def piSigned (P:PsiTheory)(g:ℕ)(d:List ℤ)(Y:ℝ):ℝ:=
  if ∀k∈d,0≤k then normalized P g (d.map Int.toNat) Y else 0
lemma normalized_critical_nonneg (P:PsiTheory)(g:ℕ)(d:List ℕ):0≤normalized P g d y₀ := by
  simp only [normalized,ite_true]
  split_ifs
  · have hp:0≤pure P g (d++List.replicate (deficit g d) 2):=psi_nonneg P _ _
    have hprod:0≤(d.map (fun k=>(oddFactorial k:ℝ))).prod:=by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨k,hk,rfl⟩:=List.mem_map.mp ha
      positivity
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) hprod) hp) (by positivity)
  · exact le_rfl
lemma piSigned_critical_nonneg (P:PsiTheory)(g:ℕ)(d:List ℤ):0≤piSigned P g d y₀ := by
  unfold piSigned
  split_ifs
  · exact normalized_critical_nonneg P _ _
  · exact le_rfl
lemma piSigned_unstable (P:PsiTheory)(g:ℕ)(d:List ℤ)(Y:ℝ)(hs:¬Stable g d.length):
    piSigned P g d Y=0 := by
  unfold piSigned
  split_ifs
  · exact normalized_unstable P g _ Y (by simpa only[List.length_map] using hs)
  · rfl
lemma piTheta_ge_one (Y:ℝ)(hY:Y∈Icc 0 y₀)(l:ℕ):1≤theta Y l := by
  obtain ⟨C,hC⟩:=uniform_kernel_moments.1
  have h0:theta Y 0=1:=(hC Y hY).1
  have hmono:Monotone (theta Y):=(hC Y hY).2.1
  rw[←h0]
  exact hmono (Nat.zero_le l)
lemma normalizedChildren_critical_nonneg (P:PsiTheory)(g p:ℕ)(d:List ℤ)
    (hd:∀k∈d,0≤k):0≤normalizedChildren P g p d y₀ := by
  unfold normalizedChildren
  apply add_nonneg
  · apply add_nonneg
    · apply Finset.sum_nonneg
      intro j hj
      have hj':=Finset.mem_range.mp hj
      have hv:0≤d[j]!:=hd _ (by simpa[hj'] using List.getElem_mem (l:=d) j hj')
      have hc:0≤2*(d[j]!:ℝ)+1:=by
        have hv':(0:ℝ)≤(d[j]!:ℝ):=by exact_mod_cast hv
        linarith
      exact mul_nonneg hc (piSigned_critical_nonneg P _ _)
    · split_ifs
      · exact le_rfl
      · apply mul_nonneg (by norm_num : (0:ℝ)≤1/2)
        apply Finset.sum_nonneg
        intro u hu
        exact piSigned_critical_nonneg P _ _
  · apply mul_nonneg (by norm_num : (0:ℝ)≤1/2)
    apply Finset.sum_nonneg
    intro u hu
    apply Finset.sum_nonneg
    intro g₁ hg₁
    apply Finset.sum_nonneg
    intro I hI
    exact mul_nonneg (piSigned_critical_nonneg P _ _) (piSigned_critical_nonneg P _ _)

lemma normalizedChildren_pi_le_step (P:PsiTheory)(g p h:ℕ)(d:List ℤ)(Y:ℝ)
    (hh:2≤h)(he:complexity g (d.length+1)=h)(hd:∀k∈d,0≤k)
    (ih:∀g':ℕ,∀c:List ℤ,1≤c.length→complexity g' c.length<h→piSigned P g' c y₀≤piSigned P g' c Y):
    normalizedChildren P g p d y₀≤normalizedChildren P g p d Y := by
  unfold normalizedChildren
  apply add_le_add
  · apply add_le_add
    · apply Finset.sum_le_sum
      intro j hj
      have hj':=Finset.mem_range.mp hj
      have hv:0≤d[j]!:=hd _ (by simpa[hj'] using List.getElem_mem (l:=d) j hj')
      have hc:0≤2*(d[j]!:ℝ)+1:=by
        have hv':(0:ℝ)≤(d[j]!:ℝ):=by exact_mod_cast hv
        linarith
      apply mul_le_mul_of_nonneg_left _ hc
      apply ih
      · simp
      · simp only[List.length_cons,List.length_eraseIdx_of_lt hj']
        unfold complexity at *
        omega
    · by_cases hg:g=0
      · simp[hg]
      · simp only[hg,ite_false]
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤1/2)
        apply Finset.sum_le_sum
        intro u hu
        apply ih
        · simp
        · simp only[List.length_cons]
          unfold complexity at *
          omega
  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤1/2)
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro g₁ hg₁
    apply Finset.sum_le_sum
    intro I hI
    let c₁:List ℤ:=(u:ℤ)::selected d I
    let c₂:List ℤ:=((p:ℤ)-2-u)::selected d ((Finset.range d.length)\I)
    change piSigned P g₁ c₁ y₀*piSigned P (g-g₁) c₂ y₀≤piSigned P g₁ c₁ Y*piSigned P (g-g₁) c₂ Y
    by_cases hs₁:Stable g₁ c₁.length
    · by_cases hs₂:Stable (g-g₁) c₂.length
      · have hgg:g₁≤g:=by have:=Finset.mem_range.mp hg₁;omega
        have hpart:=selected_partition_length d I
        have hc₁:complexity g₁ c₁.length<h:=by
          dsimp only[c₁]
          simp only[List.length_cons]
          dsimp only[c₁,c₂] at hs₁ hs₂
          simp only[Stable,List.length_cons] at hs₁ hs₂
          unfold complexity at *
          omega
        have hc₂:complexity (g-g₁) c₂.length<h:=by
          dsimp only[c₂]
          simp only[List.length_cons]
          dsimp only[c₁,c₂] at hs₁ hs₂
          simp only[Stable,List.length_cons] at hs₁ hs₂
          unfold complexity at *
          omega
        have hl₁:=ih g₁ c₁ (by simp[c₁]) hc₁
        have hl₂:=ih (g-g₁) c₂ (by simp[c₂]) hc₂
        exact mul_le_mul hl₁ hl₂ (piSigned_critical_nonneg P _ _)
          ((piSigned_critical_nonneg P _ _).trans hl₁)
      · rw[piSigned_unstable P _ _ y₀ hs₂,piSigned_unstable P _ _ Y hs₂]
        simp
    · rw[piSigned_unstable P _ _ y₀ hs₁,piSigned_unstable P _ _ Y hs₁]
      simp

lemma normalized_pi_le_aux (P:PsiTheory)(Y:ℝ)(hY:Y∈Icc 0 y₀)(h:ℕ):
    ∀g:ℕ,∀d:List ℕ,1≤d.length→complexity g d.length=h→normalized P g d y₀≤normalized P g d Y := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro g d hn he
    by_cases hs:Stable g d.length
    · by_cases hd:d.sum≤dimension g d.length
      · by_cases htop:d.sum=dimension g d.length
        · rw[normalized_top P g d Y hY htop,normalized_top P g d y₀ ⟨y₀_pos.le,le_rfl⟩ htop]
        · by_cases hsmall:h≤1
          · have hg:g=1:=by unfold complexity at he;unfold Stable at hs;unfold dimension at hd htop;omega
            have hlen:d.length=1:=by unfold complexity at he;unfold Stable at hs;omega
            subst g
            obtain ⟨p,rfl⟩:=List.length_eq_one_iff.mp hlen
            have hp:p=0:=by simp only[List.sum_singleton,List.length_singleton] at hd htop;norm_num[dimension] at hd htop;omega
            subst p
            rw[(initial_amplitudes P y₀ ⟨y₀_pos.le,le_rfl⟩).2.2,(initial_amplitudes P Y hY).2.2,critical_kernels.2 1]
            have ht:=piTheta_ge_one Y hY 1
            linarith
          · have hh:2≤h:=by omega
            cases d with
            | nil => simp at hn
            | cons p d =>
              have hhc:2≤complexity g (d.length+1):=by simpa only[List.length_cons] using he.symm ▸ hh
              rw[normalized_positive_convolution P g p d y₀ hhc hd ⟨y₀_pos.le,le_rfl⟩,
                normalized_positive_convolution P g p d Y hhc hd hY]
              apply Finset.sum_le_sum
              intro l hl
              have hchild:=normalizedChildren_pi_le_step P g (p+l) h (d.map Int.ofNat) Y hh
                (by simpa only[List.length_map,List.length_cons] using he)
                (by intro k hk;obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hk;exact Int.natCast_nonneg j)
                (by
                  intro g' c hlen hc
                  unfold piSigned
                  split_ifs
                  · exact ih _ hc g' (c.map Int.toNat) (by simpa only[List.length_map] using hlen)
                      (by simp only[List.length_map])
                  · exact le_rfl)
              rw[critical_kernels.2 l,one_mul]
              have hnn:0≤normalizedChildren P g (p+l) (d.map Int.ofNat) Y:=
                (normalizedChildren_critical_nonneg P g (p+l) (d.map Int.ofNat)
                  (by intro k hk;obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hk;exact Int.natCast_nonneg j)).trans hchild
              exact hchild.trans (by have ht:=piTheta_ge_one Y hY l;nlinarith)
      · have hex:dimension g d.length<d.sum:=by omega
        rw[normalized_excess P g d Y hex,normalized_excess P g d y₀ hex]
    · rw[normalized_unstable P g d Y hs,normalized_unstable P g d y₀ hs]
lemma normalized_pi_le (P:PsiTheory)(g:ℕ)(d:List ℕ)(hn:1≤d.length)(Y:ℝ)(hY:Y∈Icc 0 y₀):
    normalized P g d y₀≤normalized P g d Y :=normalized_pi_le_aux P Y hY _ g d hn rfl
end WP
