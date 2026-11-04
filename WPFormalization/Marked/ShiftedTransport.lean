import WPFormalization.Marked.CuspRefinement
import WPFormalization.Intersection.ShiftedStringDerivative
/-! Inversion of the genuine refined cusp ratio and the resulting logarithmic parameter transport.
All constants are uniform on the full parameter interval; denominators are bounded
away from zero using the proved positive compact lower bound for A. -/
noncomputable section
namespace WP.Analysis
lemma second_order_ratio_inverse (u A b h c a B D : ℝ) (hh : 1≤h)
    (ha : 0<a) (hu : a/2≤u) (hc : 0≤c) (hA : |A|≤B) (hb : |b|≤D) (hD : D≤h)
    (he : |u-A*(1-b/h)|≤c/h^2) :
    |A*h/u-(h+b)|≤((2/a)*(B*D^2+2*c))/h := by
  have hhp : 0<h := by linarith
  have hup : 0<u := by linarith
  have hB : 0≤B := (abs_nonneg _).trans hA
  have hD0 : 0≤D := (abs_nonneg _).trans hb
  have hb2 : b^2≤D^2 := by nlinarith [sq_nonneg b,(abs_le.mp hb).1,(abs_le.mp hb).2]
  have hsum : |h+b|≤2*h := by
    calc _ ≤ |h|+|b| := abs_add_le _ _
         _ ≤ h+D := by rw [abs_of_pos hhp];exact add_le_add_right hb _
         _ ≤ _ := by linarith
  have heq : A*h/u-(h+b)=(A*b^2/h-(h+b)*(u-A*(1-b/h)))/u := by
    field_simp
    <;>ring
  have hfirst : |A*b^2/h|≤B*D^2/h := by
    rw [abs_div,abs_of_pos hhp,abs_mul,abs_of_nonneg (sq_nonneg b)]
    exact div_le_div_of_nonneg_right (mul_le_mul hA hb2 (sq_nonneg b) hB) hhp.le
  have hsecond : |(h+b)*(u-A*(1-b/h))|≤2*c/h := by
    rw [abs_mul]
    calc _ ≤ (2*h)*(c/h^2) := mul_le_mul hsum he (abs_nonneg _) (by positivity)
         _ = _ := by field_simp <;> ring
  have hnum : |A*b^2/h-(h+b)*(u-A*(1-b/h))|≤(B*D^2+2*c)/h := by
    calc _ ≤ |A*b^2/h|+|(h+b)*(u-A*(1-b/h))| := abs_sub _ _
         _ ≤ B*D^2/h+2*c/h := add_le_add hfirst hsecond
         _ = _ := by ring
  rw [heq,abs_div,abs_of_pos hup]
  calc _ ≤ ((B*D^2+2*c)/h)/u := div_le_div_of_nonneg_right hnum hup.le
       _ ≤ ((B*D^2+2*c)/h)/(a/2) :=
         div_le_div_of_nonneg_left (by positivity) (by positivity) hu
       _ = _ := by field_simp <;> ring
end WP.Analysis
namespace WP
lemma shifted_zero_pos (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Set.Ico (0:ℝ) y₀) : 0<shifted P g (List.replicate p 0) Y := by
  have hn := normalized_pos_valid_nonempty P g (List.replicate p 0)
    (by simpa using hp) (by simpa using hs) (by simp) Y ⟨hY.1,hY.2.le⟩
  unfold normalized at hn
  rw [if_neg (ne_of_lt hY.2)] at hn
  have hf : 0<a Y^(complexity g (List.replicate p 0).length)*r Y^(deficit g (List.replicate p 0)) :=
    mul_pos (pow_pos (a_pos Y hY) _) (pow_pos (r_pos Y hY) _)
  exact (mul_pos_iff_of_pos_left hf).mp hn
lemma scaled_shifted_ratio_eq_W_inverse (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p)
    (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Set.Ico (0:ℝ) y₀) :
    A Y*r Y*(a Y*shifted P g (List.replicate (p+1) 0) Y/shifted P g (List.replicate p 0) Y)=
      A Y*(complexity g p:ℝ)/((complexity g p:ℝ)*W P g p Y/W P g (p+1) Y) := by
  have hs' : Stable g (p+1) := by unfold Stable at *;omega
  have hsp : shifted P g (List.replicate p 0) Y≠0 := (shifted_zero_pos P g p hp hs Y hY).ne'
  have hsc : shifted P g (List.replicate (p+1) 0) Y≠0 :=
    (shifted_zero_pos P g (p+1) (by omega) hs' Y hY).ne'
  have ha := (a_pos Y hY).ne'
  have hr := (r_pos Y hY).ne'
  have hh : (complexity g p:ℝ)≠0 := by
    exact_mod_cast (show complexity g p≠0 by unfold complexity Stable at *;omega)
  have h4 : (4:ℝ)^g≠0 := by positivity
  have hc : complexity g (p+1)=complexity g p+1 := by unfold complexity Stable at *;omega
  have hm : dimension g (p+1)=dimension g p+1 := by unfold dimension Stable at *;omega
  have hd (q : ℕ) : deficit g (List.replicate q 0)=dimension g q := by simp [deficit]
  unfold W normalized
  simp only [if_neg (ne_of_lt hY.2),List.length_replicate,hd,hc,hm,pow_succ]
  field_simp
  <;>ring
lemma shifted_transport_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g≥G,∀ Y ∈ Set.Ico (0:ℝ) y₀,
      |A Y*r Y*(a Y*shifted P g (List.replicate (p+1) 0) Y/shifted P g (List.replicate p 0) Y)-
        ((complexity g p:ℝ)+dilatonBeta p Y)| ≤ C/(complexity g p:ℝ) := by
  obtain ⟨a,ha,hA⟩ := singleMarking_A_uniform_lower
  obtain ⟨B,hB,hboundA⟩ := dilaton_A_abs_uniform
  obtain ⟨K,hK,hboundK⟩ := dilaton_correction_abs_uniform p
  obtain ⟨c,hc,G,hcusp⟩ := refined_cusp_proof P p
  let D : ℝ := K/a
  have hD : 0<D := div_pos hK ha
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(K+c)/a+D+1)
  let C : ℝ := (2/a)*(B*D^2+2*c)
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,2+G+N,?_⟩
  intro g hg Y hY
  have hYc : Y ∈ Set.Icc (0:ℝ) y₀ := ⟨hY.1,hY.2.le⟩
  have hstable : Stable g p := by unfold Stable;omega
  have hh : (1:ℝ) ≤ complexity g p := by exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega)
  have hhp : (0:ℝ)<complexity g p := by linarith
  have hNg : (N:ℝ) ≤ complexity g p := by
    exact_mod_cast (show N ≤ complexity g p by unfold complexity;omega)
  have hlarge : 2*(K+c)/a+D+1<(complexity g p:ℝ) := hN.trans_le hNg
  have hβ : |dilatonBeta p Y| ≤ D := by
    apply (le_div_iff₀ ha).2
    have haY := hA Y hYc
    have hAY : 0<A Y := ha.trans_le haY
    have hi := hboundK Y hYc
    rw [abs_mul,abs_of_pos hAY] at hi
    calc _  ≤  |dilatonBeta p Y| * A Y := mul_le_mul_of_nonneg_left haY (abs_nonneg _)
         _  ≤  K := by nlinarith [hi]
  let h : ℝ := complexity g p
  let u : ℝ := h*W P g p Y/W P g (p+1) Y
  have he : |u-A Y*(1-dilatonBeta p Y/h)| ≤ c/h^2 := hcusp g (by omega) Y hYc
  have hDle : D ≤ h := by dsimp only [h];have := div_pos (show 0<2*(K+c) by positivity) ha;linarith
  have hsmall : (K+c)/h ≤ a/2 := by
    apply (div_le_iff₀ hhp).2
    have hi := (div_lt_iff₀ ha).mp (show 2*(K+c)/a<h by dsimp only [h];linarith)
    nlinarith
  have hcdiv : c/h^2 ≤ c/h := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hhp) hhp).2
    have hi : h ≤ h^2 := by dsimp only [h];nlinarith
    exact mul_le_mul_of_nonneg_left hi hc.le
  have hab : A Y*dilatonBeta p Y/h ≤ K/h := by
    exact div_le_div_of_nonneg_right ((le_abs_self _).trans (hboundK Y hYc)) hhp.le
  have hu : a/2 ≤ u := by
    have hl := (abs_le.mp he).1
    have haY := hA Y hYc
    have halg : A Y*(1-dilatonBeta p Y/h)=A Y-A Y*dilatonBeta p Y/h := by ring
    rw [halg] at hl
    have hsum : K/h+c/h=(K+c)/h := by ring
    linarith
  rw [scaled_shifted_ratio_eq_W_inverse P g p hp hstable Y hY]
  exact Analysis.second_order_ratio_inverse u (A Y) (dilatonBeta p Y) h c a B D hh ha hu hc.le
    (hboundA Y hYc) hβ hDle he

lemma shifted_log_transport_proof (P : PsiTheory) (p : ℕ) (hp : 1  ≤  p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Set.Ico (0:ℝ) y₀,
      |A Y*r Y*deriv (fun t => Real.log (shifted P g (List.replicate p 0) t)) Y-
        ((complexity g p:ℝ)+dilatonBeta p Y)| ≤ C/complexity g p := by
  obtain ⟨C,hC,G,hbound⟩ := shifted_transport_proof P p hp
  refine ⟨C,hC,2+G,?_⟩
  intro g hg Y hY
  have hs : Stable g p := by unfold Stable;omega
  have hd := (shifted_zero_hasDerivAt P g p hs Y (a_pos Y hY).ne').log
    (shifted_zero_pos P g p hp hs Y hY).ne'
  rw [hd.deriv]
  exact hbound g (by omega) Y hY
end WP
