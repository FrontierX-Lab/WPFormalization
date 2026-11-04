import WPFormalization.Statements.MarkedExtensions
import WPFormalization.Marked.PrefactorRatios
import WPFormalization.Statements.Volumes
import WPFormalization.Analysis.ParameterInverse
import WPFormalization.Analysis.ParameterODE
import WPFormalization.Analysis.ExtractionFactorization
/-! Conversion of the genuine fixed-marking W estimates into marked-F ratios.
The shifted-flow identity is an explicit intermediate input, to be supplied by
the separately proved analytic identification of the actual Phi series. -/
noncomputable section
namespace WP
open Set
variable (P : PsiTheory)
variable (hflow : ∀ g p : ℕ, Stable g p → ∀ Y ∈ Ico 0 y₀,
  shifted P g (List.replicate p 0) Y = markedF P g p (XR Y))
include hflow
lemma W_eq_markedF_of_shift_flow (g p : ℕ) (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    W P g p Y = (4:ℝ)^g*a Y^(complexity g p)*r Y^(dimension g p)*markedF P g p (XR Y) := by
  unfold W
  rw [normalized,if_neg (ne_of_lt hY.2)]
  simp only [deficit,List.length_replicate,List.sum_replicate,nsmul_zero,Nat.sub_zero]
  rw [hflow g p hs Y hY]
  ring
lemma markedF_pos_of_shift_flow (g p : ℕ) (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Ico 0 y₀)
    (hW : 0<W P g p Y) : 0 < markedF P g p (XR Y) := by
  rw [W_eq_markedF_of_shift_flow P hflow g p hs Y hY] at hW
  exact (mul_pos_iff_of_pos_left (mul_pos (mul_pos (pow_pos (by norm_num) g)
    (pow_pos (a_pos Y hY) _)) (pow_pos (r_pos Y hY) _))).mp hW
lemma markedF_cusp_ratio_of_shift_flow (g p : ℕ) (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Ico 0 y₀)
    (hW : 0<W P g p Y) :
    markedF P g (p+1) (XR Y)/markedF P g p (XR Y) =
      (W P g (p+1) Y/W P g p Y)/(a Y*r Y) := by
  have hs' : Stable g (p+1) := by unfold Stable at *;omega
  have hc : complexity g (p+1)=complexity g p+1 := by unfold Stable at hs;unfold complexity;omega
  have hm : dimension g (p+1)=dimension g p+1 := by unfold Stable at hs;unfold dimension;omega
  have hF := (markedF_pos_of_shift_flow P hflow g p hs Y hY hW).ne'
  rw [W_eq_markedF_of_shift_flow P hflow g (p+1) hs' Y hY,
    W_eq_markedF_of_shift_flow P hflow g p hs Y hY,hc,hm,pow_succ,pow_succ]
  field_simp [(a_pos Y hY).ne',(r_pos Y hY).ne',hF]
  <;> ring
lemma markedF_genus_ratio_of_shift_flow (g p : ℕ) (hg : 2≤g) (Y : ℝ) (hY : Y ∈ Ico 0 y₀)
    (hW : 0<W P g p Y) :
    markedF P (g-1) (p+2) (XR Y)/(4*r Y*markedF P g p (XR Y)) =
      W P (g-1) (p+2) Y/W P g p Y := by
  have hs : Stable g p := by unfold Stable;omega
  have hs' : Stable (g-1) (p+2) := by unfold Stable;omega
  have hc : complexity (g-1) (p+2)=complexity g p := by unfold complexity;omega
  have hm : dimension g p=dimension (g-1) (p+2)+1 := by unfold dimension;omega
  have he : g=(g-1)+1 := by omega
  have hF := (markedF_pos_of_shift_flow P hflow g p hs Y hY hW).ne'
  rw [W_eq_markedF_of_shift_flow P hflow (g-1) (p+2) hs' Y hY,
    W_eq_markedF_of_shift_flow P hflow g p hs Y hY,hc,hm]
  conv_rhs => rw [show (4:ℝ)^g=4^(g-1)*4 by rw [←pow_succ,←he]]
  rw [pow_succ]
  field_simp [(a_pos Y hY).ne',(r_pos Y hY).ne',hF]
  <;> ring
omit hflow in
lemma Psi_XR_eq_kernel_ratio (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    Psi (XR Y)=XR Y/(A Y*a Y*r Y) := by
  have hinv := Analysis.inverseY_eq_of_root (XR Y) Y hY.2.le rfl
  have hM := Analysis.J_sub_XR_eq_Aar Y hY
  rw [J_action_identity Y hY] at hM
  have hs := (Real.sqrt_pos.mpr (Delta_pos Y hY)).ne'
  have hI : action Y=A Y*a Y*r Y*Real.sqrt (Delta Y) := by
    apply (div_eq_iff hs).mp
    linarith
  unfold Psi density
  rw [hinv,hI]
  field_simp [hs,(a_pos Y hY).ne',(r_pos Y hY).ne',
    (Analysis.marked_A_pos Y ⟨hY.1,hY.2.le⟩).ne']
  <;> ring
omit hflow in
lemma cusp_inverse_error_scalar (a c h g C b k : ℝ)
    (hh : 0≤h) (hg : 0<g) (hC : 0≤C) (hb : 0<b) (hk : 0≤k)
    (ha : b≤a) (hc : |c-a|≤C/g) (hsmall : C/g≤b/2) (hkg : h≤k*g) :
    |h*(a/c-1)|≤2*C*k/b := by
  have hcp : 0<c := by have := (abs_le.mp hc).1;linarith
  have hcl : b/2≤c := by have := (abs_le.mp hc).1;linarith
  have hab : |a-c|≤C/g := by rwa [abs_sub_comm]
  have he : a/c-1=(a-c)/c := by field_simp <;> ring
  rw [he,abs_mul,abs_of_nonneg hh,abs_div,abs_of_pos hcp,←mul_div_assoc]
  apply (div_le_iff₀ hcp).mpr
  calc h*|a-c| ≤ h*(C/g) := mul_le_mul_of_nonneg_left hab hh
       _ ≤ k*C := by
         rw [←mul_div_assoc]
         apply (div_le_iff₀ hg).mpr
         nlinarith [mul_le_mul_of_nonneg_right hkg hC]
       _ = (2*C*k/b)*(b/2) := by field_simp <;> ring
       _ ≤ (2*C*k/b)*c := mul_le_mul_of_nonneg_left hcl (by positivity)
lemma marked_cusp_ratios_of_shift_flow (p : ℕ) (hp : 1≤p) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico 0 y₀,
      |XR Y*markedF P g (p+1) (XR Y)/markedF P g p (XR Y)-
        (complexity g p:ℝ)*Psi (XR Y)|≤C*Psi (XR Y) := by
  obtain ⟨b,hb,hA⟩ := singleMarking_A_uniform_lower
  obtain ⟨C,hC,G,hcusp⟩ := marked_cusp_all_proof P p
  obtain ⟨N,hN⟩ := exists_nat_gt (2*C/b)
  refine ⟨2*C*((p:ℝ)+2)/b,by positivity,2+G+N,?_⟩
  intro g hg Y hY
  have hg₂ : 2≤g := by omega
  have hg₁ : 1≤g := by omega
  have hgp : 0<(g:ℝ) := by exact_mod_cast (show 0<g by omega)
  have hs : Stable g p := by unfold Stable;omega
  have hYc : Y∈Icc (0:ℝ) y₀ := ⟨hY.1,hY.2.le⟩
  have hW := W_pos P g p hp hs Y hYc
  have hW' := W_pos P g (p+1) (by omega) (by unfold Stable;omega) Y hYc
  have hh : 0<(complexity g p:ℝ) := by
    exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hkg : (complexity g p:ℝ)≤((p:ℝ)+2)*(g:ℝ) := by
    exact_mod_cast complexity_le_genus_multiple g p hg₁
  have hn : 2*C/b < (g:ℝ) := hN.trans_le (by exact_mod_cast (show N≤g by omega))
  have hsmall : C/(g:ℝ)≤b/2 := by
    apply (div_le_iff₀ hgp).mpr
    have := (div_lt_iff₀ hb).mp hn
    nlinarith
  let c : ℝ := (complexity g p:ℝ)*W P g p Y/W P g (p+1) Y
  have hcb := cusp_inverse_error_scalar (A Y) c (complexity g p) g C b ((p:ℝ)+2)
    hh.le hgp hC.le hb (by positivity) (hA Y hYc)
    (hcusp g (by omega) Y hYc) hsmall hkg
  have ha : 0<A Y := hb.trans_le (hA Y hYc)
  have hΨ : 0≤Psi (XR Y) := by
    rw [Psi_XR_eq_kernel_ratio Y hY]
    exact div_nonneg (XR_nonneg_interior Y hY)
      (mul_pos (mul_pos ha (a_pos Y hY)) (r_pos Y hY)).le
  have he : XR Y*markedF P g (p+1) (XR Y)/markedF P g p (XR Y)-
        (complexity g p:ℝ)*Psi (XR Y) = Psi (XR Y)*((complexity g p:ℝ)*(A Y/c-1)) := by
    rw [show XR Y*markedF P g (p+1) (XR Y)/markedF P g p (XR Y)=
      XR Y*(markedF P g (p+1) (XR Y)/markedF P g p (XR Y)) by ring,
      markedF_cusp_ratio_of_shift_flow P hflow g p hs Y hY hW,Psi_XR_eq_kernel_ratio Y hY]
    dsimp only [c]
    field_simp [ha.ne',(a_pos Y hY).ne',(r_pos Y hY).ne',hW.ne',hW'.ne',hh.ne']
    <;> ring
  rw [he,abs_mul,abs_of_nonneg hΨ]
  exact (mul_le_mul_of_nonneg_left hcb hΨ).trans_eq (by ring)
lemma marked_genus_ratios_of_shift_flow (p : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico 0 y₀,
      |markedF P (g-1) (p+2) (XR Y)/(4*r Y*markedF P g p (XR Y))-1|≤C/g := by
  obtain ⟨C,hC,G,hgenus⟩ := marked_genus_all_proof P p
  obtain ⟨Gpos,hpos⟩ := W_eventually_pos_all P p
  refine ⟨C,hC,2+G+Gpos,?_⟩
  intro g hg Y hY
  rw [markedF_genus_ratio_of_shift_flow P hflow g p (by omega) Y hY
    (hpos g (by omega) Y ⟨hY.1,hY.2.le⟩)]
  exact hgenus g (by omega) Y ⟨hY.1,hY.2.le⟩
lemma marked_ratios_of_shift_flow :
    (∀ p : ℕ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      ∀ Y ∈ Set.Ico 0 y₀,
        |XR Y*markedF P g (p+1) (XR Y)/markedF P g p (XR Y) -
          (complexity g p : ℝ)*Psi (XR Y)| ≤ C*Psi (XR Y)) ∧
    (∀ p : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Ico 0 y₀,
      |markedF P (g-1) (p+2) (XR Y)/(4*r Y*markedF P g p (XR Y))-1| ≤ C/g) := by
  exact ⟨fun p hp => marked_cusp_ratios_of_shift_flow P hflow p hp,
    fun p => marked_genus_ratios_of_shift_flow P hflow p⟩
end WP
