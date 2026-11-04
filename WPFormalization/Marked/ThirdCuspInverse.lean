import WPFormalization.Marked.ThirdCuspRefinement
import WPFormalization.Analysis.ThirdTransportInverse

/-! The true third-order cusp expansion is inverted using the compact positive lower bound for A. -/

noncomputable section
open Set

namespace WP
lemma marked_cusp_inverse_third_order_proof (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y∈Icc (0:ℝ) y₀,
      |A Y*(complexity g p:ℝ)/((complexity g p:ℝ)*W P g p Y/W P g (p+1) Y)-
        ((complexity g p:ℝ)+transportBeta p Y+
          (transportBeta p Y^2-transportBeta p Y-HigherOrder.secondDilatonMoment p Y/A Y)/(complexity g p:ℝ))| ≤
            C/(complexity g p:ℝ)^2 := by
  obtain ⟨a,ha,hAlower⟩ := singleMarking_A_uniform_lower
  obtain ⟨Ba,hBa,hA⟩ := dilaton_A_abs_uniform
  obtain ⟨D,hD,hβ⟩ := HigherOrder.transportBeta_abs_uniform p
  obtain ⟨E,hE,hMoment⟩ := HigherOrder.secondDilatonMoment_abs_uniform p
  obtain ⟨K,hK,hCorr⟩ := dilaton_correction_abs_uniform p
  obtain ⟨c,hc,Gc,hThird⟩ := marked_cusp_third_order_proof P p
  obtain ⟨c₂,hc₂,G₂,hCoarse⟩ := refined_cusp_proof P p
  let F : ℝ := D+E/a
  have hF : 0<F := by dsimp [F];positivity
  let C : ℝ := (2/a)*(Ba*D*((D^2+F)+F)+Ba*F*(D^2+F)+c*(1+D+(D^2+F)))
  have hC : 0<C := by dsimp [C];positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(K+c₂)/a+1)
  refine ⟨C,hC,2+Gc+G₂+N,?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := by omega
  have hgC : Gc ≤ g := by omega
  have hg₂ : G₂ ≤ g := by omega
  let h : ℝ := complexity g p
  let u : ℝ := h*W P g p Y/W P g (p+1) Y
  let b : ℝ := transportBeta p Y
  let e : ℝ := HigherOrder.secondDilatonMoment p Y
  let k : ℝ := b+e/A Y
  have hh : 1 ≤ h := by dsimp [h];exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega)
  have hhp : 0<h := lt_of_lt_of_le zero_lt_one hh
  have hApos : 0<A Y := ha.trans_le (hAlower Y hY)
  have hNg : (N:ℝ) ≤ h := by dsimp [h];exact_mod_cast (show N ≤ complexity g p by unfold complexity;omega)
  have hsmall : (K+c₂)/h ≤ a/2 := by
    apply (div_le_iff₀ hhp).2
    have hn : 2*(K+c₂)/a<h := by linarith [hN.trans_le hNg]
    have hi := (div_lt_iff₀ ha).mp hn
    nlinarith
  have hcoarse := hCoarse g hg₂ Y hY
  have hcenter : A Y*(1-dilatonBeta p Y/h)=A Y-A Y*b/h := by
    dsimp [b]
    change A Y*(1-transportBeta p Y/h)=A Y-A Y*transportBeta p Y/h
    ring
  change |u-A Y*(1-dilatonBeta p Y/h)| ≤ c₂/h^2 at hcoarse
  rw [hcenter] at hcoarse
  have hc₂div : c₂/h^2 ≤ c₂/h :=
    div_le_div_of_nonneg_left hc₂.le hhp (by nlinarith)
  have hab : A Y*b/h ≤ K/h := by
    have hi : |A Y*b| ≤ K := by simpa only [b,transportBeta,dilatonBeta] using hCorr Y hY
    exact div_le_div_of_nonneg_right ((le_abs_self _).trans hi) hhp.le
  have hu : a/2 ≤ u := by
    have hlo := (abs_le.mp hcoarse).1
    have hAlo := hAlower Y hY
    have hsum : K/h+c₂/h=(K+c₂)/h := by ring
    linarith
  have hk : |k| ≤ F := by
    dsimp [k,F]
    calc
      _ ≤ |b|+|e/A Y| := abs_add_le _ _
      _ ≤ D+E/a := by
        apply add_le_add (hβ Y hY)
        rw [abs_div,abs_of_pos hApos]
        exact (div_le_div_of_nonneg_right (hMoment Y hY) hApos.le).trans
          (div_le_div_of_nonneg_left hE.le ha (hAlower Y hY))
  have hraw := hThird g hgC Y hY
  have halg : A Y*(1-b/h+k/h^2)=A Y-A Y*b/h+(A Y*b+e)/h^2 := by
    dsimp [k]
    field_simp
  have herr : |u-A Y*(1-b/h+k/h^2)| ≤ c/h^3 := by rw [halg];exact hraw
  have he := Analysis.third_order_ratio_inverse u (A Y) b k h c a Ba D F hh ha hu hc.le (hA Y hY) (hβ Y hY) hk herr
  dsimp only [k,b,e,h,u] at he
  convert he using 1
  congr 2
  ring
end WP
