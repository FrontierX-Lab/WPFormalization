import WPFormalization.Statements.Coefficients
import WPFormalization.Marked.GenusExtensions
/-! Uniform bounds for the actual cusp/genus corrections of Appendix C.3.
The cusp bound is independent of marking count. Genus exchange controls all
p≥2, while p=1 uses the proved asymptotic ratio and continuity/positivity
on the finitely many remaining genera. The invalid g=0 numerator is zero. -/
noncomputable section
open Set
namespace WP
lemma W_continuous_parameter (P:PsiTheory) (g p:ℕ) :
    Continuous (fun Y:Icc (0:ℝ) y₀=>W P g p (Y:ℝ)):=by
  exact continuous_const.mul (normalized_continuous P g _)

lemma W_one_genus_ratio_abs_uniform (P:PsiTheory) : ∃X:ℝ,0<X ∧
    ∀g:ℕ,1 ≤ g→∀Y∈Icc (0:ℝ) y₀,
    |W P (g-1) 3 Y/W P g 1 Y| ≤ X :=by
  obtain ⟨C,hC,G,he⟩:=marked_genus_all_proof P 1
  have hfinite (i:Fin G) :∃B:ℝ,0<B ∧∀Y∈Icc (0:ℝ) y₀,
      |W P i.val 3 Y/W P (i.val+1) 1 Y| ≤ B:=by
    have hc:Continuous (fun Y:Icc (0:ℝ) y₀=>W P i.val 3 Y/W P (i.val+1) 1 Y):=by
      exact (W_continuous_parameter P _ _).div (W_continuous_parameter P _ _)
        (fun Y=>(W_pos P (i.val+1) 1 (by omega) (by unfold Stable;omega) Y Y.property).ne')
    obtain ⟨B,hB⟩:=isCompact_univ.bddAbove_image hc.norm.continuousOn
    refine ⟨max 1 B,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
    intro Y hY
    exact (hB (mem_image_of_mem _ (show (⟨Y,hY⟩:Icc (0:ℝ) y₀)∈univ from mem_univ _))).trans
      (le_max_right _ _)
  choose B hB hb using hfinite
  let X:=C+1+∑i:Fin G,B i
  have hsum:0 ≤ ∑i:Fin G,B i:=Finset.sum_nonneg (fun i hi=>(hB i).le)
  refine ⟨X,by dsimp[X];linarith,?_⟩
  intro g hg Y hY
  by_cases hgG:G ≤ g
  · have he':=he g hgG Y hY
    simp only[Nat.reduceAdd] at he'
    have hgR:(1:ℝ) ≤ g:=by exact_mod_cast hg
    have herr:|W P (g-1) 3 Y/W P g 1 Y-1| ≤ C:=he'.trans ((div_le_iff₀ (by linarith)).2 (by nlinarith))
    calc
      _=|(W P (g-1) 3 Y/W P g 1 Y-1)+1|:=by congr 1;ring
      _ ≤ |W P (g-1) 3 Y/W P g 1 Y-1|+|1|:=abs_add_le _ _
      _ ≤ X:=by norm_num only[abs_one];dsimp[X];linarith
  · let i:Fin G:=⟨g-1,by omega⟩
    have hi:i.val+1=g:=by dsimp[i];omega
    have hh:=hb i Y hY
    rw[hi] at hh
    have hBi:B i ≤ ∑j:Fin G,B j:=Finset.single_le_sum (fun j hj=>(hB j).le) (Finset.mem_univ i)
    exact hh.trans (by dsimp[X];linarith)

lemma cuspCorrection_abs_uniform : ∃X:ℝ,0<X ∧∀P:PsiTheory,∀g p:ℕ,
    1 ≤ p→Stable g p→∀Y∈Icc (0:ℝ) y₀,|cuspCorrection P g p Y| ≤ X:=by
  obtain ⟨a,ha,hA⟩:=singleMarking_A_uniform_lower
  obtain ⟨C,hC,hW⟩:=W_cusp_uniform_bound
  refine ⟨C/a,by positivity,?_⟩
  intro P g p hp hs Y hY
  have hAp:0<A Y:=ha.trans_le (hA Y hY)
  have hWp:0<W P g (p+1) Y:=W_pos P g _ (by omega) (by unfold Stable at *;omega) Y hY
  have hWg:0 ≤ W P g p Y:=W_nonneg P g p hp Y hY
  have hcor0:0 ≤ cuspCorrection P g p Y:=by unfold cuspCorrection;positivity
  rw[abs_of_nonneg hcor0]
  calc
    _=((complexity g p:ℝ)*W P g p Y/W P g (p+1) Y)/A Y:=by unfold cuspCorrection;ring
    _ ≤ C/A Y:=div_le_div_of_nonneg_right ((div_le_iff₀ hWp).2 (hW P g p hs Y hY)) hAp.le
    _ ≤ C/a:=div_le_div_of_nonneg_left hC.le ha (hA Y hY)
lemma genusCorrection_abs_uniform (P:PsiTheory) : ∃X:ℝ,0<X ∧∀g p:ℕ,
    1 ≤ p→Stable g p→∀Y∈Icc (0:ℝ) y₀,|genusCorrection P g p Y| ≤ X:=by
  obtain ⟨X,hX,hOne⟩:=W_one_genus_ratio_abs_uniform P
  refine ⟨X+1,by positivity,?_⟩
  intro g p hp hs Y hY
  by_cases hg:g=0
  · subst g
    simpa only[genusCorrection_zero,abs_zero] using (by linarith:0 ≤ X+1)
  · rw[genusCorrection_of_pos P g p Y (by omega)]
    by_cases hp1:p=1
    · subst p
      exact (hOne g (by omega) Y hY).trans (by linarith)
    · have hw:0<W P g p Y:=W_pos P g p hp hs Y hY
      have hn:0 ≤ W P (g-1) (p+2) Y:=W_nonneg P (g-1) (p+2) (by omega) Y hY
      rw[abs_of_nonneg (div_nonneg hn hw.le)]
      exact ((div_le_one hw).2 (W_genus_exchange_le P g p (by omega) (by omega) Y hY)).trans (by linarith)

lemma scalar_corrections_abs_uniform (P:PsiTheory) : ∃X:ℝ,0<X ∧∀g p:ℕ,
    1 ≤ p→Stable g p→∀Y∈Icc (0:ℝ) y₀,
    |cuspCorrection P g p Y|+|genusCorrection P g p Y| ≤ X:=by
  obtain ⟨C,hC,hc⟩:=cuspCorrection_abs_uniform
  obtain ⟨G,hG,hg⟩:=genusCorrection_abs_uniform P
  refine ⟨C+G,by positivity,?_⟩
  intro g p hp hs Y hY
  exact add_le_add (hc P g p hp hs Y hY) (hg g p hp hs Y hY)
end WP
