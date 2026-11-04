import WPFormalization.Marked.GenusSecondOrderAll
import WPFormalization.Analysis.FirstOrderRatioAlgebra
/-! Third-order merging and nonseparating prefactors for the genuine W amplitudes.
The refined cusp ratio is shifted from h−1 to h, and the handle ratio is the
product of a lower-genus cusp ratio and the genuine second-order genus ratio.
The final nonseparating theorem includes the exact factor two. -/
noncomputable section
namespace WP.Analysis
lemma cusp_to_third_order_merge (x A b h c B K : ℝ) (hh : 2 ≤ h)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (hK : 0 ≤ K) (hA : |A| ≤ B) (hb : |A*b| ≤ K)
    (hx : |(h-1)*x-A*(1-b/(h-1))| ≤ c/(h-1)^2) :
    |x-A/h*(1+(1-b)/h)| ≤ (8*c+2*B+8*K)/h^3 := by
  have hp : 0<h := by linarith
  have hm : 0<h-1 := by linarith
  have h3 : 0<h^3 := pow_pos hp _
  have h2 : 0<h^2 := sq_pos_of_pos hp
  have he : x-A/h*(1+(1-b)/h)=
      ((h-1)*x-A*(1-b/(h-1)))/(h-1)+A/(h^2*(h-1))-
        (A*b)*(2*h-1)/(h^2*(h-1)^2) := by
    field_simp
    <;>ring
  have hcube : h^3 ≤ 8*(h-1)^3 := by
    calc _  ≤  (2*(h-1))^3 := pow_le_pow_left₀ hp.le (by linarith) 3
         _ = _ := by ring
  have hfirst : |((h-1)*x-A*(1-b/(h-1)))/(h-1)| ≤ 8*c/h^3 := by
    rw [abs_div,abs_of_pos hm]
    calc _  ≤  (c/(h-1)^2)/(h-1) := div_le_div_of_nonneg_right hx hm.le
         _ = c/(h-1)^3 := by field_simp <;> ring
         _  ≤  _ := by
           apply (div_le_div_iff₀ (pow_pos hm 3) h3).2
           nlinarith [mul_le_mul_of_nonneg_left hcube hc]
  have hsecond : |A/(h^2*(h-1))| ≤ 2*B/h^3 := by
    rw [abs_div,abs_of_pos (mul_pos h2 hm)]
    calc _  ≤  B/(h^2*(h-1)) := div_le_div_of_nonneg_right hA (mul_pos h2 hm).le
         _  ≤  _ := by
           apply (div_le_div_iff₀ (mul_pos h2 hm) h3).2
           have hi : h^3 ≤ 2*h^2*(h-1) := by nlinarith
           nlinarith [mul_le_mul_of_nonneg_left hi hB]
  have hthird : |(A*b)*(2*h-1)/(h^2*(h-1)^2)| ≤ 8*K/h^3 := by
    rw [abs_div,abs_of_pos (mul_pos h2 (sq_pos_of_pos hm)),abs_mul,abs_of_pos (by linarith : 0<2*h-1)]
    calc _  ≤  K*(2*h-1)/(h^2*(h-1)^2) :=
           div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb (by linarith)) (by positivity)
         _  ≤  _ := by
           apply (div_le_div_iff₀ (mul_pos h2 (sq_pos_of_pos hm)) h3).2
           have hi : (2*h-1)*h ≤ 8*(h-1)^2 := by nlinarith [sq_nonneg (h-2)]
           have hj := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi h2.le) hK
           convert hj using 1 <;> ring
  rw [he]
  calc _  ≤  |((h-1)*x-A*(1-b/(h-1)))/(h-1)+A/(h^2*(h-1))|+
          |(A*b)*(2*h-1)/(h^2*(h-1)^2)| := abs_sub _ _
       _  ≤  (|((h-1)*x-A*(1-b/(h-1)))/(h-1)|+|A/(h^2*(h-1))|)+
          |(A*b)*(2*h-1)/(h^2*(h-1)^2)| := add_le_add_left (abs_add_le _ _) _
       _  ≤  (8*c/h^3+2*B/h^3)+8*K/h^3 := add_le_add (add_le_add hfirst hsecond) hthird
       _ = _ := by ring
end WP.Analysis
namespace WP
lemma W_merge_prefactor_third_order (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g≥G,∀ Y ∈ Set.Icc (0:ℝ) y₀,
      |W P g (p-1) Y/W P g p Y-
        A Y/(complexity g p:ℝ)*(1+(1-dilatonBeta (p-1) Y)/(complexity g p:ℝ))| ≤
          C/(complexity g p:ℝ)^3 := by
  obtain ⟨c,hc,G,hcusp⟩ := refined_cusp_proof P (p-1)
  obtain ⟨B,hB,hA⟩ := dilaton_A_abs_uniform
  obtain ⟨K,hK,hβ⟩ := dilaton_correction_abs_uniform (p-1)
  refine ⟨8*c+2*B+8*K,by positivity,2+G,?_⟩
  intro g hg Y hY
  have hh : (2:ℝ) ≤ complexity g p := by
    exact_mod_cast (show 2 ≤ complexity g p by unfold complexity;omega)
  have hs : (complexity g (p-1):ℝ)=(complexity g p:ℝ)-1 := by
    have hn : complexity g p=complexity g (p-1)+1 := by unfold complexity;omega
    rw [hn,Nat.cast_add,Nat.cast_one]
    ring
  have hx := hcusp g (by omega) Y hY
  rw [show p-1+1=p by omega,hs] at hx
  apply Analysis.cusp_to_third_order_merge _ (A Y) (dilatonBeta (p-1) Y)
    (complexity g p) c B K hh hc.le hB.le hK.le (hA Y hY) (hβ Y hY)
  simpa only [mul_div_assoc] using hx
end WP
namespace WP
lemma W_handle_prefactor_third_order (P : PsiTheory) (p : ℕ) (hp : 1  ≤  p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g≥G,∀ Y ∈ Set.Icc (0:ℝ) y₀,
      |W P (g-1) (p+1) Y/W P g p Y-
        A Y/(complexity g p:ℝ)*(1+(1-dilatonBeta (p+1) Y-HigherOrder.alpha p Y)/(complexity g p:ℝ))| ≤
          C/(complexity g p:ℝ)^3 := by
  obtain ⟨cm,hcm,Gm,hmerge⟩ := W_merge_prefactor_third_order P (p+2) (by omega)
  obtain ⟨cg,hcg,Gg,hgenus⟩ := marked_genus_second_order_all P p
  obtain ⟨B,hB,hA⟩ := dilaton_A_abs_uniform
  obtain ⟨K,hK,hβ⟩ := dilaton_correction_abs_uniform (p+1)
  obtain ⟨D,hD,hα⟩ := genus_second_alpha_abs_uniform p
  let M : ℝ := 1+B+K+D
  let E : ℝ := cm+cg
  have hM : 0<M := by dsimp only [M];positivity
  have hE : 0<E := by dsimp only [E];positivity
  let C : ℝ := M^2+4*M*E+E^2
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,3+Gm+Gg,?_⟩
  intro g hg Y hY
  let h : ℝ := complexity g p
  let L : ℝ := W P (g-1) (p+1) Y/W P (g-1) (p+2) Y
  let r : ℝ := W P (g-1) (p+2) Y/W P g p Y
  have hh : (1:ℝ) ≤ h := by
    dsimp only [h]
    exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega)
  have hhp : 0<h := by linarith
  have ht : (1/h:ℝ) ∈ Set.Icc 0 1 := ⟨by positivity,(div_le_one hhp).2 hh⟩
  have hm := hmerge (g-1) (by omega) Y hY
  have hc : complexity (g-1) (p+2)=complexity g p := by unfold complexity;omega
  rw [hc,show p+2-1=p+1 by omega] at hm
  change |L-A Y/h*(1+(1-dilatonBeta (p+1) Y)/h)| ≤ cm/h^3 at hm
  have hr := hgenus g (by omega) Y hY
  change |r-(1-HigherOrder.alpha p Y/h)| ≤ cg/h^2 at hr
  have hb : |A Y*(1-dilatonBeta (p+1) Y)| ≤ B+K := by
    rw [mul_sub,mul_one]
    exact (abs_sub _ _).trans (add_le_add (hA Y hY) (hβ Y hY))
  have hx : |h*L-(A Y+(A Y*(1-dilatonBeta (p+1) Y))*(1/h))| ≤ E*(1/h)^2 := by
    have he : h*L-(A Y+(A Y*(1-dilatonBeta (p+1) Y))*(1/h))=
        h*(L-A Y/h*(1+(1-dilatonBeta (p+1) Y)/h)) := by field_simp <;> ring
    rw [he,abs_mul,abs_of_pos hhp]
    calc _  ≤  h*(cm/h^3) := mul_le_mul_of_nonneg_left hm hhp.le
         _ = cm*(1/h)^2 := by field_simp <;> ring
         _  ≤  E*(1/h)^2 := mul_le_mul_of_nonneg_right (by dsimp only [E];linarith) (sq_nonneg _)
  have hy : |r-(1+(-HigherOrder.alpha p Y)*(1/h))| ≤ E*(1/h)^2 := by
    have hi := hr.trans (div_le_div_of_nonneg_right (show cg ≤ E by dsimp only [E];linarith) (sq_nonneg h))
    convert hi using 1 <;> field_simp <;> ring
  have he := Analysis.first_order_mul_error (A Y) (A Y*(1-dilatonBeta (p+1) Y))
    1 (-HigherOrder.alpha p Y) (h*L) r M E (1/h) hM.le hE.le ht
    ((hA Y hY).trans (by dsimp only [M];linarith))
    (hb.trans (by dsimp only [M];linarith))
    (by rw [abs_one];dsimp only [M];linarith)
    (by rw [abs_neg];exact (hα Y hY).trans (by dsimp only [M];linarith)) hx hy
  have hW : W P (g-1) (p+2) Y≠0 :=
    (W_pos P (g-1) (p+2) (by omega) (by unfold Stable;omega) Y hY).ne'
  have hWg : W P g p Y≠0 :=
    (W_pos P g p hp (by unfold Stable;omega) Y hY).ne'
  have hprod : L*r=W P (g-1) (p+1) Y/W P g p Y := by
    dsimp only [L,r]
    field_simp
  let T : ℝ := A Y/h*(1+(1-dilatonBeta (p+1) Y-HigherOrder.alpha p Y)/h)
  have heq : (h*L)*r-(A Y*1+(A Y*(-HigherOrder.alpha p Y)+(A Y*(1-dilatonBeta (p+1) Y))*1)*(1/h))=
      h*(W P (g-1) (p+1) Y/W P g p Y-T) := by
    rw [←hprod]
    dsimp only [T]
    field_simp
    <;>ring
  rw [heq,abs_mul,abs_of_pos hhp] at he
  have hi : |W P (g-1) (p+1) Y/W P g p Y-T| ≤ (C*(1/h)^2)/h := by
    apply (le_div_iff₀ hhp).2
    simpa only [C,mul_comm] using he
  convert hi using 1 <;> dsimp only [T,h] <;> field_simp <;> ring
end WP

namespace WP
lemma W_nonseparating_prefactor_third_order (P : PsiTheory) (p : ℕ) (hp : 1  ≤  p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g≥G,∀ Y ∈ Set.Icc (0:ℝ) y₀,
      |2*(W P (g-1) (p+1) Y/W P g p Y)-
        (2*A Y)/(complexity g p:ℝ)*(1+(1-dilatonBeta (p+1) Y-HigherOrder.alpha p Y)/(complexity g p:ℝ))| ≤
          C/(complexity g p:ℝ)^3 := by
  obtain ⟨C,hC,G,hbound⟩ := W_handle_prefactor_third_order P p hp
  refine ⟨2*C,by positivity,G,?_⟩
  intro g hg Y hY
  have hi := hbound g hg Y hY
  calc _ = |2*(W P (g-1) (p+1) Y/W P g p Y-
          A Y/(complexity g p:ℝ)*(1+(1-dilatonBeta (p+1) Y-HigherOrder.alpha p Y)/(complexity g p:ℝ)))| := by
          congr 1
          ring
       _ = 2*|W P (g-1) (p+1) Y/W P g p Y-
          A Y/(complexity g p:ℝ)*(1+(1-dilatonBeta (p+1) Y-HigherOrder.alpha p Y)/(complexity g p:ℝ))| := by
          rw [abs_mul]
          norm_num
       _  ≤  2*(C/(complexity g p:ℝ)^3) := mul_le_mul_of_nonneg_left hi (by norm_num)
       _ = _ := by ring
end WP
