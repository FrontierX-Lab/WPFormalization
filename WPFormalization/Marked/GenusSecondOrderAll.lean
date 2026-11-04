import WPFormalization.Marked.GenusSecondOrder
import WPFormalization.Marked.CuspRefinement
import WPFormalization.Analysis.FirstOrderRatioAlgebra

/-! The genus-exchange expansion for every fixed marking count, including zero and one. Four actual refined cusp ratios transport the proved expansion, with exact alpha/beta compatibility and a quantitative quotient remainder. -/

noncomputable section
open Set Filter
open scoped Topology

namespace WP
lemma genus_second_alpha_abs_uniform (p : ℕ) : ∃ B : ℝ, 0<B ∧
    ∀ Y ∈ Icc (0:ℝ) y₀, |HigherOrder.alpha p Y|≤B := by
  obtain ⟨a,ha,hA⟩ := dilaton_A_abs_uniform
  obtain ⟨m,hm,hM⟩ := dilaton_weight_moments_abs_uniform
  let R := |(p:ℝ)-3| *m+2*m+|2*(p:ℝ)-3|
  have hR : 0≤R := by dsimp [R];positivity
  refine ⟨a*R+1,by positivity,?_⟩
  intro Y hY
  have hi : |((p:ℝ)-3)*Theta Y+2*moment₁ Y+2*p-3|≤R := by
    have heq : ((p:ℝ)-3)*Theta Y+2*moment₁ Y+2*p-3=
        (((p:ℝ)-3)*Theta Y+2*moment₁ Y)+(2*(p:ℝ)-3) := by ring
    rw [heq]
    calc _ ≤ |((p:ℝ)-3)*Theta Y+2*moment₁ Y|+|2*(p:ℝ)-3| := abs_add_le _ _
         _ ≤ (|((p:ℝ)-3)*Theta Y|+|2*moment₁ Y|)+|2*(p:ℝ)-3| :=
           add_le_add (abs_add_le _ _) le_rfl
         _ = (|(p:ℝ)-3| *|Theta Y|+2*|moment₁ Y|)+|2*(p:ℝ)-3| := by rw [abs_mul,abs_mul];norm_num
         _ ≤ R := add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hM Y hY).1 (abs_nonneg _))
           (mul_le_mul_of_nonneg_left (hM Y hY).2 (by norm_num))) le_rfl
  have hb : |HigherOrder.alpha p Y|≤a*R := by
    unfold HigherOrder.alpha
    rw [abs_mul]
    exact mul_le_mul (hA Y hY) hi (abs_nonneg _) ha.le
  linarith

lemma genus_alpha_beta_shift (p : ℕ) (Y : ℝ) :
    HigherOrder.alpha p Y=HigherOrder.alpha (p+2) Y+dilatonBeta (p+2) Y+dilatonBeta (p+3) Y-
      dilatonBeta p Y-dilatonBeta (p+1) Y := by
  unfold HigherOrder.alpha dilatonBeta
  push_cast
  ring

set_option maxHeartbeats 1200000 in
lemma marked_genus_second_order_all (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Icc (0:ℝ) y₀,
      |W P (g-1) (p+2) Y/W P g p Y-(1-HigherOrder.alpha p Y/(complexity g p:ℝ))| ≤ C/(complexity g p:ℝ)^2 := by
  obtain ⟨a,ha,hAmin⟩ := singleMarking_A_uniform_lower
  obtain ⟨Ba,hBa,hA⟩ := dilaton_A_abs_uniform
  obtain ⟨B₀,hB₀,hb₀⟩ := dilaton_correction_abs_uniform p
  obtain ⟨B₁,hB₁,hb₁⟩ := dilaton_correction_abs_uniform (p+1)
  obtain ⟨B₂,hB₂,hb₂⟩ := dilaton_correction_abs_uniform (p+2)
  obtain ⟨B₃,hB₃,hb₃⟩ := dilaton_correction_abs_uniform (p+3)
  obtain ⟨Bα,hBα,hbα⟩ := genus_second_alpha_abs_uniform p
  obtain ⟨Br,hBr,hbr⟩ := genus_second_alpha_abs_uniform (p+2)
  obtain ⟨C₀,hC₀,G₀,h₀⟩ := refined_cusp_proof P p
  obtain ⟨C₁,hC₁,G₁,h₁⟩ := refined_cusp_proof P (p+1)
  obtain ⟨C₂,hC₂,G₂,h₂⟩ := refined_cusp_proof P (p+2)
  obtain ⟨C₃,hC₃,G₃,h₃⟩ := refined_cusp_proof P (p+3)
  obtain ⟨Cr,hCr,Gr,hr⟩ := marked_genus_second_order P (p+2) (by omega)
  obtain ⟨Gp,hPos⟩ := W_eventually_pos_all P p
  let M := 1+Ba+B₀+B₁+B₂+B₃+Bα+Br
  let E := C₀+C₁+C₂+C₃+Cr+B₁+B₃+2*Br
  have hM : 1≤M := by dsimp [M];linarith
  have hM0 : 0≤M := by linarith
  have hE : 0<E := by dsimp [E];positivity
  let C := 48*(1+M+E+3*M^2+(M^2+4*M*E+E^2))^2/a^2
  have hC : 0<C := by dsimp [C];positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(M+E)/a)
  refine ⟨C,hC,2+N+G₀+G₁+G₂+G₃+Gr+Gp,?_⟩
  intro g hg Y hY
  have hg2 : 2≤g := by omega
  have hg₀ : G₀≤g := by omega
  have hg₁ : G₁≤g := by omega
  have hg₂ : G₂≤g-1 := by omega
  have hg₃ : G₃≤g-1 := by omega
  have hgr : Gr≤g := by omega
  have hgp : Gp≤g := by omega
  have hgN : N≤g := by omega
  let h : ℝ := complexity g p
  have hhg : (g:ℝ)≤h := by dsimp [h];exact_mod_cast (show g≤complexity g p by unfold complexity;omega)
  have hh1 : 1≤h := by
    have hgR : (2:ℝ)≤g := by exact_mod_cast hg2
    linarith
  have hhp : 0<h := by linarith
  let t := 1/h
  have ht : t∈Icc (0:ℝ) 1 := ⟨by dsimp [t];positivity,by dsimp [t];exact (div_le_one hhp).2 hh1⟩
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
  let ax := -(A Y*dilatonBeta p Y)
  let ay := -(A Y*dilatonBeta (p+1) Y)
  let au := -(A Y*dilatonBeta (p+2) Y)
  let av := -(A Y*dilatonBeta (p+3) Y)
  let ar := -(HigherOrder.alpha (p+2) Y)
  let L := -(HigherOrder.alpha p Y)
  have hc₁ : complexity g (p+1)=complexity g p+1 := by unfold complexity;omega
  have hc₂ : complexity (g-1) (p+2)=complexity g p := by unfold complexity;omega
  have hc₃ : complexity (g-1) (p+3)=complexity g p+1 := by unfold complexity;omega
  have hcr : complexity g (p+2)=complexity g p+2 := by unfold complexity;omega
  have hdom (D : ℝ) (hDE : D≤E) : D/h^2≤E/h^2 := div_le_div_of_nonneg_right hDE (sq_nonneg h)
  have hax₀ : |ax|≤B₀ := by simpa only [ax,abs_neg] using hb₀ Y hY
  have hay₀ : |ay|≤B₁ := by simpa only [ay,abs_neg] using hb₁ Y hY
  have hau₀ : |au|≤B₂ := by simpa only [au,abs_neg] using hb₂ Y hY
  have hav₀ : |av|≤B₃ := by simpa only [av,abs_neg] using hb₃ Y hY
  have har₀ : |ar|≤Br := by simpa only [ar,abs_neg] using hbr Y hY
  have hL₀ : |L|≤Bα := by simpa only [L,abs_neg] using hbα Y hY
  have hx₀ : |x-(A Y+ax/h)|≤C₀/h^2 := by
    have hi := h₀ g hg₀ Y hY
    convert hi using 1 <;> dsimp [x,ax,h,z₀,z₁] <;> ring
  have hy₀ : |y-(A Y+ay/(h+1))|≤C₁/(h+1)^2 := by
    have hi := h₁ g hg₁ Y hY
    rw [hc₁,Nat.cast_add,Nat.cast_one,show p+1+1=p+2 by omega] at hi
    convert hi using 1 <;> dsimp [y,ay,h,z₁,z₂] <;> ring
  have hu₀ : |u-(A Y+au/h)|≤C₂/h^2 := by
    have hi := h₂ (g-1) hg₂ Y hY
    rw [hc₂,show p+2+1=p+3 by omega] at hi
    convert hi using 1 <;> dsimp [u,au,h,u₀,u₁] <;> ring
  have hv₀ : |v-(A Y+av/(h+1))|≤C₃/(h+1)^2 := by
    have hi := h₃ (g-1) hg₃ Y hY
    rw [hc₃,Nat.cast_add,Nat.cast_one,show p+3+1=p+4 by omega] at hi
    convert hi using 1 <;> dsimp [v,av,h,u₁,u₂] <;> ring
  have hr₀ : |r-(1+ar/(h+2))|≤Cr/(h+2)^2 := by
    have hi := hr g hgr Y hY
    rw [hcr,Nat.cast_add,Nat.cast_ofNat,show p+2+2=p+4 by omega] at hi
    convert hi using 1 <;> dsimp [r,ar,h,u₂,z₂] <;> ring
  have hxH : |x-(A Y+ax/h)|≤E/h^2 := hx₀.trans (hdom C₀ (by dsimp [E];linarith))
  have hyH : |y-(A Y+ay/h)|≤E/h^2 := by
    have hi := Analysis.first_order_shift_error y (A Y) ay h 1 B₁ C₁ hhp (by norm_num) hB₁.le hC₁.le hay₀ hy₀
    exact hi.trans (hdom (C₁+1*B₁) (by dsimp [E];linarith))
  have huH : |u-(A Y+au/h)|≤E/h^2 := hu₀.trans (hdom C₂ (by dsimp [E];linarith))
  have hvH : |v-(A Y+av/h)|≤E/h^2 := by
    have hi := Analysis.first_order_shift_error v (A Y) av h 1 B₃ C₃ hhp (by norm_num) hB₃.le hC₃.le hav₀ hv₀
    exact hi.trans (hdom (C₃+1*B₃) (by dsimp [E];linarith))
  have hrH : |r-(1+ar/h)|≤E/h^2 := by
    have hi := Analysis.first_order_shift_error r 1 ar h 2 Br Cr hhp (by norm_num) hBr.le hCr.le har₀ hr₀
    exact hi.trans (hdom (Cr+2*Br) (by dsimp [E];linarith))
  have hax : |ax|≤M := hax₀.trans (by dsimp [M];linarith)
  have hay : |ay|≤M := hay₀.trans (by dsimp [M];linarith)
  have hau : |au|≤M := hau₀.trans (by dsimp [M];linarith)
  have hav : |av|≤M := hav₀.trans (by dsimp [M];linarith)
  have har : |ar|≤M := har₀.trans (by dsimp [M];linarith)
  have hL : |L|≤M := hL₀.trans (by dsimp [M];linarith)
  have hAM : |A Y|≤M := (hA Y hY).trans (by dsimp [M];linarith)
  have hsmall : (M+E)/h≤a/2 := by
    have hi := (div_lt_iff₀ ha).mp hN
    have hNg : (N:ℝ)≤g := by exact_mod_cast hgN
    have hNh : (N:ℝ)≤h := hNg.trans hhg
    apply (div_le_iff₀ hhp).2
    nlinarith
  have lower_bound (z b : ℝ) (hb : |b|≤M) (hz : |z-(A Y+b/h)|≤E/h^2) : a/2≤z := by
    have herr : |z-A Y|≤a/2 := by
      calc _ ≤ |z-(A Y+b/h)|+|(A Y+b/h)-A Y| := abs_sub_le _ _ _
           _ = |z-(A Y+b/h)|+|b/h| := by congr 2;ring
           _ ≤ E/h^2+M/h := add_le_add hz (by rw [abs_div,abs_of_pos hhp];exact div_le_div_of_nonneg_right hb hhp.le)
           _ ≤ E/h+M/h := add_le_add (div_le_div_of_nonneg_left hE.le hhp (by nlinarith)) le_rfl
           _ = (M+E)/h := by ring
           _ ≤ _ := hsmall
    have hi := (abs_le.mp herr).1
    have haY := hAmin Y hY
    linarith
  have hxl := lower_bound x ax hax hxH
  have hyl := lower_bound y ay hay hyH
  have hcoef : ar*A Y+au+av=L*A Y+ax+ay := by
    dsimp [ar,au,av,L,ax,ay]
    rw [genus_alpha_beta_shift p Y]
    ring
  have hxT : |x-(A Y+ax*t)|≤E*t^2 := by convert hxH using 1 <;> dsimp [t] <;> field_simp
  have hyT : |y-(A Y+ay*t)|≤E*t^2 := by convert hyH using 1 <;> dsimp [t] <;> field_simp
  have huT : |u-(A Y+au*t)|≤E*t^2 := by convert huH using 1 <;> dsimp [t] <;> field_simp
  have hvT : |v-(A Y+av*t)|≤E*t^2 := by convert hvH using 1 <;> dsimp [t] <;> field_simp
  have hrT : |r-(1+ar*t)|≤E*t^2 := by convert hrH using 1 <;> dsimp [t] <;> field_simp
  have hratio := Analysis.first_order_ratio_error (A Y) ax ay au av ar L x y u v r a M E t ha hM hE.le ht
    hAM hax hay hau hav har hL hxl hyl hxT hyT huT hvT hrT hcoef
  have hz₀ : 0<z₀ := hPos g hgp Y hY
  have hz₁ : 0<z₁ := W_pos P g (p+1) (by omega) (by unfold Stable;omega) Y hY
  have hz₂ : 0<z₂ := W_pos P g (p+2) (by omega) (by unfold Stable;omega) Y hY
  have hu₁ : 0<u₁ := W_pos P (g-1) (p+3) (by omega) (by unfold Stable;omega) Y hY
  have hu₂ : 0<u₂ := W_pos P (g-1) (p+4) (by omega) (by unfold Stable;omega) Y hY
  have hid : u₀/z₀=r*u*v/(x*y) := genus_ratio_two_marking_algebra h z₀ z₁ z₂ u₀ u₁ u₂
    hhp.ne' (by linarith) hz₀.ne' hz₁.ne' hz₂.ne' hu₁.ne' hu₂.ne'
  change |u₀/z₀-(1-HigherOrder.alpha p Y/h)|≤C/h^2
  rw [hid]
  convert hratio using 1 <;> dsimp [L,C,t] <;> field_simp <;> ring
end WP
