import WPFormalization.Marked.CuspAll
import WPFormalization.Statements.MarkedGenus
/-! Adding two markings transports the proved genus comparison to zero and
one marking. Four genuine cusp ratios cancel the identical complexity
factors. In the zero-marking case their positive limiting value proves
positivity of the denominator for large genus before division is used. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma four_cusp_error_bound (a b A x y u v r e : ℝ)
    (ha : 0<a) (hb : 0 ≤ b) (hA : A ∈ Icc a b) (he : e ∈ Icc 0 1)
    (hx : a/2 ≤ x) (hy : a/2 ≤ y)
    (hxa : |x-A| ≤ e) (hya : |y-A| ≤ e)
    (hua : |u-A| ≤ e) (hva : |v-A| ≤ e) (hr : |r-1| ≤ e) :
    |r*u*v/(x*y)-1| ≤ (4*((b+1)^2+4*(b+1))/a^2)*e := by
  have he0 : 0 ≤ e := he.1
  have hAp : 0 ≤ A := ha.le.trans hA.1
  have hbound (z : ℝ) (hz : |z-A| ≤ e) : |z| ≤ b+1 := by
    calc _ = |(z-A)+A| := by congr 1;ring
         _ ≤ |z-A|+|A| := abs_add_le _ _
         _ ≤ e+A := by rw [abs_of_nonneg hAp];exact add_le_add hz le_rfl
         _ ≤ _ := by linarith [hA.2,he.2]
  have hux : |u-x| ≤ 2*e := by
    calc _ = |(u-A)-(x-A)| := by congr 1;ring
         _ ≤ |u-A|+|x-A| := abs_sub _ _
         _ ≤ _ := by linarith
  have hvy : |v-y| ≤ 2*e := by
    calc _ = |(v-A)-(y-A)| := by congr 1;ring
         _ ≤ |v-A|+|y-A| := abs_sub _ _
         _ ≤ _ := by linarith
  have huv : |u*v| ≤ (b+1)^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul (hbound u hua) (hbound v hva) (abs_nonneg _) (by linarith)
  have hpair : |u*v-x*y| ≤ 4*(b+1)*e := by
    calc _ = |(u-x)*v+x*(v-y)| := by congr 1;ring
         _ ≤ |(u-x)*v|+|x*(v-y)| := abs_add_le _ _
         _ = |u-x| *|v|+|x| *|v-y| := by rw [abs_mul,abs_mul]
         _ ≤ (2*e)*(b+1)+(b+1)*(2*e) := add_le_add
           (mul_le_mul hux (hbound v hva) (abs_nonneg _) (by positivity))
           (mul_le_mul (hbound x hxa) hvy (abs_nonneg _) (by positivity))
         _ = _ := by ring
  have hnum : |r*u*v-x*y| ≤ ((b+1)^2+4*(b+1))*e := by
    calc _ = |(r-1)*(u*v)+(u*v-x*y)| := by congr 1;ring
         _ ≤ |(r-1)*(u*v)|+|u*v-x*y| := abs_add_le _ _
         _ = |r-1| *|u*v|+|u*v-x*y| := by rw [abs_mul]
         _ ≤ e*(b+1)^2+4*(b+1)*e := add_le_add
           (mul_le_mul hr huv (abs_nonneg _) he.1) hpair
         _ = _ := by ring
  have hxp : 0<x := by linarith
  have hyp : 0<y := by linarith
  have hden : a^2/4 ≤ x*y := by nlinarith [mul_le_mul hx hy (by linarith : 0≤a/2) hxp.le]
  have hdenp : 0<a^2/4 := by positivity
  have heq : r*u*v/(x*y)-1 = (r*u*v-x*y)/(x*y) := by field_simp
  rw [heq,abs_div,abs_of_pos (mul_pos hxp hyp)]
  calc _ ≤ (((b+1)^2+4*(b+1))*e)/(x*y) := div_le_div_of_nonneg_right hnum (mul_pos hxp hyp).le
       _ ≤ (((b+1)^2+4*(b+1))*e)/(a^2/4) :=
         div_le_div_of_nonneg_left (by positivity) hdenp hden
       _ = _ := by field_simp <;> ring
end WP.Analysis

namespace WP
lemma genusExtension_A_uniform_upper : ∃ b : ℝ, 0<b ∧ ∀ Y ∈ Icc (0:ℝ) y₀, A Y ≤ b := by
  have hc : Continuous (fun Y : Icc (0:ℝ) y₀ => A (Y:ℝ)) := by
    exact (Complex.continuous_re.comp (Analysis.barH_joint_continuous.comp
      (continuous_id.prodMk continuous_const))).div_const 3
  obtain ⟨M,hM⟩ := isCompact_univ.bddAbove_image hc.norm.continuousOn
  refine ⟨max 1 M,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro Y hY
  have hm := hM (mem_image_of_mem _ (show (⟨Y,hY⟩:Icc (0:ℝ) y₀) ∈ univ from mem_univ _))
  rw [Real.norm_eq_abs] at hm
  exact (le_abs_self _).trans (hm.trans (le_max_right _ _))

lemma genus_ratio_two_marking_algebra (h z₀ z₁ z₂ u₀ u₁ u₂ : ℝ)
    (hh : h≠0) (hh' : h+1≠0) (hz₀ : z₀≠0) (hz₁ : z₁≠0) (hz₂ : z₂≠0)
    (hu₁ : u₁≠0) (hu₂ : u₂≠0) :
    u₀/z₀=(u₂/z₂)*(h*u₀/u₁)*((h+1)*u₁/u₂)/((h*z₀/z₁)*((h+1)*z₁/z₂)) := by
  field_simp

lemma marked_genus_of_all_cusp (P : PsiTheory)
    (hcusp : ∀ p : ℕ, ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |(complexity g p:ℝ)*W P g p Y/W P g (p+1) Y-A Y| ≤ C/(g:ℝ))
    (p : ℕ) : ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |W P (g-1) (p+2) Y/W P g p Y-1| ≤ C/(g:ℝ) := by
  obtain ⟨a,ha,hA⟩ := singleMarking_A_uniform_lower
  obtain ⟨b,hb,hB⟩ := genusExtension_A_uniform_upper
  obtain ⟨C₀,hC₀,G₀,h₀⟩ := hcusp p
  obtain ⟨C₁,hC₁,G₁,h₁⟩ := hcusp (p+1)
  obtain ⟨C₂,hC₂,G₂,h₂⟩ := hcusp (p+2)
  obtain ⟨C₃,hC₃,G₃,h₃⟩ := hcusp (p+3)
  obtain ⟨Cr,hCr,Gr,hr⟩ := marked_genus P (p+2) (by omega)
  let E : ℝ := C₀+C₁+2*C₂+2*C₃+Cr
  have hE : 0<E := by dsimp [E];positivity
  let K : ℝ := 4*((b+1)^2+4*(b+1))/a^2
  have hK : 0<K := by dsimp [K];positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (max E (2*E/a))
  refine ⟨K*E,by positivity,2+N+G₀+G₁+G₂+G₃+Gr,?_⟩
  intro g hg Y hY
  have hg₂ : 2 ≤ g := by omega
  have hg₀ : G₀ ≤ g := by omega
  have hg₁ : G₁ ≤ g := by omega
  have hg₂' : G₂ ≤ g-1 := by omega
  have hg₃' : G₃ ≤ g-1 := by omega
  have hgr : Gr ≤ g := by omega
  have hgN : N ≤ g := by omega
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hgmp : (0:ℝ)<(g-1:ℕ) := by exact_mod_cast (show 0<g-1 by omega)
  let e : ℝ := E/(g:ℝ)
  have he₀ : 0 ≤ e := by dsimp [e];positivity
  have he₁ : e ≤ 1 := by
    dsimp [e]
    apply (div_le_iff₀ hgp).2
    have hi := (le_max_left E (2*E/a)).trans_lt hN
    have hgNR : (N:ℝ) ≤ g := by exact_mod_cast hgN
    linarith
  have hea : e ≤ a/2 := by
    dsimp [e]
    apply (div_le_iff₀ hgp).2
    have hi := (div_lt_iff₀ ha).mp ((le_max_right E (2*E/a)).trans_lt hN)
    have hgNR : (N:ℝ) ≤ g := by exact_mod_cast hgN
    nlinarith
  have hdom (D : ℝ) (hDE : D ≤ E) : D/(g:ℝ) ≤ e :=
    div_le_div_of_nonneg_right hDE hgp.le
  have hshift (D : ℝ) (hD : 0 ≤ D) (hDE : 2*D ≤ E) : D/(g-1:ℕ) ≤ e := by
    apply (div_le_div_iff₀ hgmp hgp).2
    have hgm : (g:ℝ) ≤ 2*(g-1:ℕ) := by exact_mod_cast (show g ≤ 2*(g-1) by omega)
    calc D*(g:ℝ) ≤ D*(2*(g-1:ℕ)) := mul_le_mul_of_nonneg_left hgm hD
         _ = (2*D)*(g-1:ℕ) := by ring
         _ ≤ E*(g-1:ℕ) := mul_le_mul_of_nonneg_right hDE hgmp.le
  let h : ℝ := complexity g p
  let z₀ := W P g p Y
  let z₁ := W P g (p+1) Y
  let z₂ := W P g (p+2) Y
  let u₀ := W P (g-1) (p+2) Y
  let u₁ := W P (g-1) (p+3) Y
  let u₂ := W P (g-1) (p+4) Y
  let x := h*z₀/z₁
  let y := (h+1)*z₁/z₂
  let u := h*u₀/u₁
  let v := (h+1)*u₁/u₂
  let r := u₂/z₂
  have hc₁ : complexity g (p+1)=complexity g p+1 := by unfold complexity;omega
  have hc₂ : complexity (g-1) (p+2)=complexity g p := by unfold complexity;omega
  have hc₃ : complexity (g-1) (p+3)=complexity g p+1 := by unfold complexity;omega
  have hx : |x-A Y| ≤ e := (h₀ g hg₀ Y hY).trans (hdom C₀ (by dsimp [E];linarith))
  have hy : |y-A Y| ≤ e := by
    have hi := (h₁ g hg₁ Y hY).trans (hdom C₁ (by dsimp [E];linarith))
    simpa only [hc₁,Nat.cast_add,Nat.cast_one,show p+1+1=p+2 by omega] using hi
  have hu : |u-A Y| ≤ e := by
    have hi := (h₂ (g-1) hg₂' Y hY).trans (hshift C₂ hC₂.le (by dsimp [E];linarith))
    simpa only [hc₂,show p+2+1=p+3 by omega] using hi
  have hv : |v-A Y| ≤ e := by
    have hi := (h₃ (g-1) hg₃' Y hY).trans (hshift C₃ hC₃.le (by dsimp [E];linarith))
    simpa only [hc₃,Nat.cast_add,Nat.cast_one,show p+3+1=p+4 by omega] using hi
  have hr' : |r-1| ≤ e := by
    have hi := (hr g hgr Y hY).trans (hdom Cr (by dsimp [E];linarith))
    simpa only [show p+2+2=p+4 by omega] using hi
  have hxl : a/2 ≤ x := by have := (abs_le.mp hx).1;have := hA Y hY;linarith
  have hyl : a/2 ≤ y := by have := (abs_le.mp hy).1;have := hA Y hY;linarith
  have hhp : 0<h := by dsimp [h];exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hz₁ : 0<z₁ := W_pos P g (p+1) (by omega) (by unfold Stable;omega) Y hY
  have hz₂ : 0<z₂ := W_pos P g (p+2) (by omega) (by unfold Stable;omega) Y hY
  have hu₁ : 0<u₁ := W_pos P (g-1) (p+3) (by omega) (by unfold Stable;omega) Y hY
  have hu₂ : 0<u₂ := W_pos P (g-1) (p+4) (by omega) (by unfold Stable;omega) Y hY
  have hz₀ : 0<z₀ := by
    have hxp : 0<x := by linarith
    have hmul : 0<h*z₀ := (div_pos_iff_of_pos_right hz₁).mp hxp
    by_contra hz
    have hnon := mul_nonpos_of_nonneg_of_nonpos hhp.le (le_of_not_gt hz)
    linarith
  have heq : u₀/z₀=r*u*v/(x*y) := genus_ratio_two_marking_algebra h z₀ z₁ z₂ u₀ u₁ u₂
    hhp.ne' (by linarith) hz₀.ne' hz₁.ne' hz₂.ne' hu₁.ne' hu₂.ne'
  change |u₀/z₀-1| ≤ K*E/(g:ℝ)
  rw [heq]
  have hbound := Analysis.four_cusp_error_bound a b (A Y) x y u v r e ha hb.le
    ⟨hA Y hY,hB Y hY⟩ ⟨he₀,he₁⟩ hxl hyl hx hy hu hv hr'
  calc _ ≤ K*e := hbound
       _ = _ := by dsimp [e];ring
end WP

namespace WP
lemma marked_genus_all_proof (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Set.Icc (0:ℝ) y₀,
      |W P (g-1) (p+2) Y/W P g p Y-1| ≤ C/(g:ℝ) := by
  exact marked_genus_of_all_cusp P (marked_cusp_all_proof P) p
end WP
