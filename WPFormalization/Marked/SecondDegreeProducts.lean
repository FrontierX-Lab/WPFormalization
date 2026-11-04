import WPFormalization.Marked.SecondDegreeChildren
import WPFormalization.Marked.PrefactorThirdOrder

/-! The actual merger and handle prefactors multiply the genuine child expansions with uniform cubic errors. -/

noncomputable section
open Set

noncomputable section
open Set
namespace WP
lemma second_transportBeta_eq_dilatonBeta (p : ℕ) (Y : ℝ) : transportBeta p Y=dilatonBeta p Y := rfl

lemma second_prefactor_coefficients_uniform (p : ℕ) :
    ∃ M : ℝ,1 ≤ M ∧ ∀ Y∈Icc (0:ℝ) y₀,
      |A Y| ≤ M ∧ |A Y*(1-transportBeta (p-1) Y)| ≤ M ∧
        |A Y*(1-transportBeta (p+1) Y-HigherOrder.alpha p Y)| ≤ M := by
  obtain ⟨Ba,hBa,hA⟩ := dilaton_A_abs_uniform
  obtain ⟨Bm,hBm,hm⟩ := dilaton_correction_abs_uniform (p-1)
  obtain ⟨Bh,hBh,hh⟩ := dilaton_correction_abs_uniform (p+1)
  obtain ⟨Bc,hBc,hc⟩ := genus_second_alpha_abs_uniform p
  refine ⟨1+Ba+Bm+Bh+Ba*Bc,by nlinarith [mul_nonneg hBa.le hBc.le],?_⟩
  intro Y hY
  have hAy := hA Y hY
  have hmY := hm Y hY
  have hhY := hh Y hY
  have hcY := hc Y hY
  have hprod : |A Y*HigherOrder.alpha p Y| ≤ Ba*Bc := by
    rw [abs_mul]
    exact mul_le_mul hAy hcY (abs_nonneg _) hBa.le
  refine ⟨hAy.trans (by nlinarith [mul_nonneg hBa.le hBc.le]),?_,?_⟩
  · have he : A Y*(1-transportBeta (p-1) Y)=A Y-A Y*dilatonBeta (p-1) Y := by
      rw [second_transportBeta_eq_dilatonBeta]
      ring
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add hAy hmY).trans (by nlinarith [mul_nonneg hBa.le hBc.le]))
  · have he : A Y*(1-transportBeta (p+1) Y-HigherOrder.alpha p Y)=
        A Y-A Y*dilatonBeta (p+1) Y-A Y*HigherOrder.alpha p Y := by
      rw [second_transportBeta_eq_dilatonBeta]
      ring
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add ((abs_sub _ _).trans (add_le_add hAy hhY)) hprod).trans (by nlinarith [mul_nonneg hBa.le hBc.le]))
end WP

namespace WP
lemma second_merger_product_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ t : ℕ,∀ d : List ℕ,(t::d).length=p →
      ∀ l j : ℕ,j<d.length → ∀ Y∈Icc (0:ℝ) y₀,
      |(W P g (p-1) Y/W P g p Y)*
          (if 1 ≤ t+d[j]!+l then profile P g (mergerProfile t d l j) Y else 0)-
        (A Y/(complexity g p:ℝ))*(if 1 ≤ t+d[j]!+l then 1 else 0)-
        (A Y/(complexity g p:ℝ)^2)*
          (if 1 ≤ t+d[j]!+l then 1-transportBeta (p-1) Y-degreeCorrection (mergerProfile t d l j) Y else 0)| ≤
        C*(((t::d).sum:ℝ)+l+1)^4/(complexity g p:ℝ)^3 := by
  obtain ⟨Cr,hCr,Gr,hr⟩ := W_merge_prefactor_third_order P p hp
  obtain ⟨Qc,hQc,Gc,hchild⟩ := second_merger_child_uniform P p hp
  obtain ⟨M,hM,hcoeff⟩ := second_prefactor_coefficients_uniform p
  obtain ⟨N,hN,hdelta⟩ := degreeCorrection_uniform_quadratic_bound (p-1)
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  refine ⟨Cr+2*M*Qc+M*N,by positivity,max 2 (max Gr Gc),?_⟩
  intro g hg t d hd l j hj Y hY
  have hg2 : 2 ≤ g := (le_max_left _ _).trans hg
  have hgR : Gr ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgC : Gc ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hh : (1:ℝ) ≤ complexity g p := by exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega)
  have hhp : (0:ℝ)<complexity g p := lt_of_lt_of_le zero_lt_one hh
  by_cases hn : 1 ≤ t+d[j]!+l
  · rw [if_pos hn,if_pos hn,if_pos hn,mul_one]
    have hlen : (mergerProfile t d l j).length=p-1 := by
      simp only [mergerProfile,List.length_cons,List.length_eraseIdx_of_lt hj]
      simp only [List.length_cons] at hd
      omega
    have hsum : (mergerProfile t d l j).sum ≤ (t::d).sum+l := by
      have hs : d[j]!+(d.eraseIdx j).sum=d.sum := by simpa [hj] using (List.getElem_cons_eraseIdx_perm hj).sum_eq
      simp only [mergerProfile,List.sum_cons]
      omega
    have hsumR : ((mergerProfile t d l j).sum:ℝ) ≤ ((t::d).sum:ℝ)+l := by exact_mod_cast hsum
    have hδ : |degreeCorrection (mergerProfile t d l j) Y| ≤ N*(((t::d).sum:ℝ)+l+1)^2 := by
      apply (hdelta _ hlen Y hY).trans
      gcongr
    have hc : 0 ≤ profile P g (mergerProfile t d l j) Y ∧ profile P g (mergerProfile t d l j) Y ≤ 1 := by
      simpa only [profile] using normalized_profile_bounds P g (mergerProfile t d l j)
        (by rw [hlen];simp only [List.length_cons] at hd;unfold Stable;omega)
        (by rw [hlen];simp only [List.length_cons] at hd;omega) Y hY
    have hec := hchild g hgC t d hd l j hj Y hY
    rw [if_pos hn,if_pos hn] at hec
    have her : |W P g (p-1) Y/W P g p Y-
        (A Y/(complexity g p:ℝ)+A Y*(1-transportBeta (p-1) Y)/(complexity g p:ℝ)^2)| ≤
        Cr/(complexity g p:ℝ)^3 := by
      have hraw := hr g hgR Y hY
      convert hraw using 1
      congr 1
      rw [second_transportBeta_eq_dilatonBeta]
      ring
    have he := Analysis.second_prefactor_child_error_div (A Y) (A Y*(1-transportBeta (p-1) Y))
      (degreeCorrection (mergerProfile t d l j) Y) _ _ _ (((t::d).sum:ℝ)+l+1) M N Cr Qc
      hh (by linarith [show (0:ℝ) ≤ (t::d).sum from Nat.cast_nonneg _,show (0:ℝ) ≤ l from Nat.cast_nonneg _])
      hM0 hN.le hCr.le hQc.le (hcoeff Y hY).1 (hcoeff Y hY).2.1 hδ hc her hec
    convert he using 1
    congr 1
    ring
  · rw [if_neg hn,if_neg hn,if_neg hn,mul_zero,mul_zero,mul_zero,sub_self,sub_zero,abs_zero]
    positivity
end WP

namespace WP
lemma second_handle_product_uniform (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ t : ℕ,∀ d : List ℕ,(t::d).length=p →
      ∀ l u : ℕ,u∈Finset.range (t+l-1) → ∀ Y∈Icc (0:ℝ) y₀,
      |2*(W P (g-1) (p+1) Y/W P g p Y)*profile P (g-1) (contractionProfile t d l u) Y-
        2*A Y/(complexity g p:ℝ)-
        (2*A Y/(complexity g p:ℝ)^2)*
          (1-transportBeta (p+1) Y-HigherOrder.alpha p Y-degreeCorrection (contractionProfile t d l u) Y)| ≤
        C*(((t::d).sum:ℝ)+l+1)^4/(complexity g p:ℝ)^3 := by
  obtain ⟨Cr,hCr,Gr,hr⟩ := W_handle_prefactor_third_order P p hp
  obtain ⟨Qc,hQc,Gc,hchild⟩ := second_handle_child_uniform P p hp
  obtain ⟨M,hM,hcoeff⟩ := second_prefactor_coefficients_uniform p
  obtain ⟨N,hN,hdelta⟩ := degreeCorrection_uniform_quadratic_bound (p+1)
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  refine ⟨2*(Cr+2*M*Qc+M*N),by positivity,max 2 (max Gr Gc),?_⟩
  intro g hg t d hd l u hu Y hY
  have hg2 : 2 ≤ g := (le_max_left _ _).trans hg
  have hgR : Gr ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgC : Gc ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hh : (1:ℝ) ≤ complexity g p := by exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega)
  have hhp : (0:ℝ)<complexity g p := lt_of_lt_of_le zero_lt_one hh
  have hlen : (contractionProfile t d l u).length=p+1 := by
    simp only [contractionProfile,List.length_cons]
    simp only [List.length_cons] at hd
    omega
  have hsum : (contractionProfile t d l u).sum ≤ (t::d).sum+l := by
    have hu' := Finset.mem_range.mp hu
    simp only [contractionProfile,List.sum_cons]
    omega
  have hsumR : ((contractionProfile t d l u).sum:ℝ) ≤ ((t::d).sum:ℝ)+l := by exact_mod_cast hsum
  have hδ : |degreeCorrection (contractionProfile t d l u) Y| ≤ N*(((t::d).sum:ℝ)+l+1)^2 := by
    apply (hdelta _ hlen Y hY).trans
    gcongr
  have hc : 0 ≤ profile P (g-1) (contractionProfile t d l u) Y ∧
      profile P (g-1) (contractionProfile t d l u) Y ≤ 1 := by
    simpa only [profile] using normalized_profile_bounds P (g-1) (contractionProfile t d l u)
      (by rw [hlen];unfold Stable;omega) (by rw [hlen];omega) Y hY
  have hec := hchild g hgC t d hd l u hu Y hY
  have her : |W P (g-1) (p+1) Y/W P g p Y-
      (A Y/(complexity g p:ℝ)+A Y*(1-transportBeta (p+1) Y-HigherOrder.alpha p Y)/(complexity g p:ℝ)^2)| ≤
      Cr/(complexity g p:ℝ)^3 := by
    have hraw := hr g hgR Y hY
    convert hraw using 1
    congr 1
    rw [second_transportBeta_eq_dilatonBeta]
    ring
  have he := Analysis.second_prefactor_child_error_div (A Y) (A Y*(1-transportBeta (p+1) Y-HigherOrder.alpha p Y))
    (degreeCorrection (contractionProfile t d l u) Y) _ _ _ (((t::d).sum:ℝ)+l+1) M N Cr Qc
    hh (by linarith [show (0:ℝ) ≤ (t::d).sum from Nat.cast_nonneg _,show (0:ℝ) ≤ l from Nat.cast_nonneg _])
    hM0 hN.le hCr.le hQc.le (hcoeff Y hY).1 (hcoeff Y hY).2.2 hδ hc her hec
  have hm := mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ 2 by norm_num)
  rw [←show |(2:ℝ)|=2 by norm_num,←abs_mul] at hm
  convert hm using 1
  · congr 1
    ring
  · ring
end WP
