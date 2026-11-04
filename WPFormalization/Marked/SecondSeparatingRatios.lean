import WPFormalization.Marked.FirstDegreeProof
import WPFormalization.Marked.SeparatingLeadingRatios
import WPFormalization.Analysis.SecondOrderProfileError

/-! The real large-component W ratios times child profiles have uniform cubic errors. -/

noncomputable section
open Set

noncomputable section
open Set
namespace WP
lemma profile_quadratic_at_parent_complexity (P : PsiTheory) (p q j : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∃ Q : ℝ, 0<Q ∧ ∀ g : ℕ, j+1 ≤ g → ∀ d : List ℕ, d.length=q →
      ∀ Y∈Icc (0:ℝ) y₀,
        |1-profile P (g-j) d Y| ≤ Q*((d.sum:ℝ)+1)^2/(complexity g p:ℝ) := by
  obtain ⟨Q,hQ,hquad⟩ := quadratic_profile_all_markings_proof P q hq
  let C : ℝ := (2*j+p+2:ℕ)
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨Q*C,by positivity,?_⟩
  intro g hg d hd Y hY
  have hgp : (0:ℝ)<(g-j:ℕ) := by exact_mod_cast (show 0<g-j by omega)
  have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hsize : (complexity g p:ℝ) ≤ C*(g-j:ℕ) := by
    dsimp [C]
    have hmul : 2*j+p ≤ (2*j+p)*(g-j) := by simpa using Nat.mul_le_mul_left (2*j+p) (show 1 ≤ g-j by omega)
    exact_mod_cast (calc complexity g p ≤ 2*g+p := by unfold complexity;omega
                        _ ≤ (2*j+p+2)*(g-j) := by nlinarith [show g-j+j=g by omega])
  have hb := hquad (g-j) (by omega) d hd Y hY
  rw [abs_of_nonneg hb.1]
  calc
    _ ≤ Q*(d.sum:ℝ)*(d.sum+1)/(g-j:ℕ) := hb.2
    _ ≤ Q*((d.sum:ℝ)+1)^2/(g-j:ℕ) := by
      apply div_le_div_of_nonneg_right _ hgp.le
      have hds : (0:ℝ) ≤ d.sum := Nat.cast_nonneg _
      nlinarith [mul_nonneg hQ.le (show 0 ≤ ((d.sum:ℝ)+1)^2-(d.sum:ℝ)*(d.sum+1) by nlinarith)]
    _ ≤ _ := by
      apply (div_le_div_iff₀ hgp hhp).2
      calc
        _ ≤ (Q*((d.sum:ℝ)+1)^2)*(C*(g-j:ℕ)) := mul_le_mul_of_nonneg_left hsize (by positivity)
        _ = _ := by ring
end WP


namespace WP
lemma split_profile_ratio_leading_uniform (P : PsiTheory) (p q j : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hbase : ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y∈Icc (0:ℝ) y₀,
      |W P (g-j) q Y/W P g p Y-(A Y)^2/(complexity g p:ℝ)^2| ≤ C/(complexity g p:ℝ)^3) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ d : List ℕ,d.length=q →
      ∀ K : ℕ,d.sum ≤ K → ∀ Y∈Icc (0:ℝ) y₀,
      |(W P (g-j) q Y/W P g p Y)*profile P (g-j) d Y-(A Y)^2/(complexity g p:ℝ)^2| ≤
        C*((K:ℝ)+1)^2/(complexity g p:ℝ)^3 := by
  obtain ⟨Cr,hCr,Gr,hr⟩ := hbase
  obtain ⟨Q,hQ,hprofile⟩ := profile_quadratic_at_parent_complexity P p q j hp hq
  obtain ⟨B,hB,hA⟩ := dilaton_A_abs_uniform
  refine ⟨Cr+B^2*Q,by positivity,max Gr (j+1),?_⟩
  intro g hg d hd K hK Y hY
  have hgR : Gr ≤ g := (le_max_left _ _).trans hg
  have hgJ : j+1 ≤ g := (le_max_right _ _).trans hg
  have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hprof : 0 ≤ profile P (g-j) d Y ∧ profile P (g-j) d Y ≤ 1 := by
    simpa only [profile] using normalized_profile_bounds P (g-j) d
      (by rw [hd];unfold Stable;omega) (by rw [hd];omega) Y hY
  have hp' := hprofile g hgJ d hd Y hY
  have hK' : (d.sum:ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0:ℝ) ≤ d.sum := Nat.cast_nonneg _
  have hp'' : |1-profile P (g-j) d Y| ≤ Q*((K:ℝ)+1)^2/(complexity g p:ℝ) := by
    apply hp'.trans
    gcongr
  have hs := Analysis.second_zero_ratio_profile_error _ _ _ _ ((K:ℝ)+1) Cr Q hhp
    (by linarith [show (0:ℝ) ≤ K from Nat.cast_nonneg K]) hCr.le hQ.le hprof (hr g hgR Y hY) hp''
  have hA2 : |(A Y)^2| ≤ B^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hA Y hY) 2
  exact hs.trans (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hA2 hQ.le)) (by positivity))

lemma sphere_split_profile_leading_uniform (P : PsiTheory) (p : ℕ) (hp : 3 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ d : List ℕ,d.length=p-2 →
      ∀ K : ℕ,d.sum ≤ K → ∀ Y∈Icc (0:ℝ) y₀,
      |(W P g (p-2) Y/W P g p Y)*profile P g d Y-(A Y)^2/(complexity g p:ℝ)^2| ≤
        C*((K:ℝ)+1)^2/(complexity g p:ℝ)^3 := by
  simpa only [Nat.sub_zero] using split_profile_ratio_leading_uniform P p (p-2) 0
    (by omega) (by omega) (by simpa only [Nat.sub_zero] using W_two_cusp_leading P p hp)

lemma torus_split_profile_leading_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ d : List ℕ,d.length=p →
      ∀ K : ℕ,d.sum ≤ K → ∀ Y∈Icc (0:ℝ) y₀,
      |(W P (g-1) p Y/W P g p Y)*profile P (g-1) d Y-(A Y)^2/(complexity g p:ℝ)^2| ≤
        C*((K:ℝ)+1)^2/(complexity g p:ℝ)^3 :=
  split_profile_ratio_leading_uniform P p p 1 hp hp (W_genus_same_marking_leading P p hp)
end WP
