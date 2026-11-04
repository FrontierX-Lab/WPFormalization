import WPFormalization.Marked.ThirdCuspInverse
import WPFormalization.Volumes.StringFlowProof
import WPFormalization.Marked.ShiftedTransport
import WPFormalization.HigherOrder.SecondTransportFinite

/-! The actual second-order transport equation of Appendix C.2 with the existing finite canonical transportGamma. All marking counts, including zero, are covered. -/

noncomputable section
open Set

namespace WP
lemma shifted_zero_pos_of_W_pos (P : PsiTheory) (g p : ℕ) (Y : ℝ)
    (hY : Y∈Ico (0:ℝ) y₀) (hW : 0<W P g p Y) :
    0<shifted P g (List.replicate p 0) Y := by
  have hW' := hW
  unfold W at hW'
  have hn := (mul_pos_iff_of_pos_left (show (0:ℝ)<4^g by positivity)).mp hW'
  unfold normalized at hn
  rw [if_neg (ne_of_lt hY.2)] at hn
  have hf : 0<a Y^(complexity g (List.replicate p 0).length)*r Y^(deficit g (List.replicate p 0)) :=
    mul_pos (pow_pos (a_pos Y hY) _) (pow_pos (r_pos Y hY) _)
  exact (mul_pos_iff_of_pos_left hf).mp hn

lemma scaled_shifted_ratio_eq_W_inverse_of_pos (P : PsiTheory) (g p : ℕ)
    (hs : Stable g p) (Y : ℝ) (hY : Y∈Ico (0:ℝ) y₀)
    (hWp : 0<W P g p Y) (hWc : 0<W P g (p+1) Y) :
    A Y*r Y*(a Y*shifted P g (List.replicate (p+1) 0) Y/shifted P g (List.replicate p 0) Y)=
      A Y*(complexity g p:ℝ)/((complexity g p:ℝ)*W P g p Y/W P g (p+1) Y) := by
  have hsp := (shifted_zero_pos_of_W_pos P g p Y hY hWp).ne'
  have hsc := (shifted_zero_pos_of_W_pos P g (p+1) Y hY hWc).ne'
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
  <;> ring

lemma markedF_log_scaled_eq_inverse_of_W_pos (P : PsiTheory) (g p : ℕ)
    (hs : Stable g p) (Y : ℝ) (hY : Y∈Ico (0:ℝ) y₀)
    (hWp : 0<W P g p Y) (hWc : 0<W P g (p+1) Y) :
    A Y*r Y*deriv (fun t => Real.log (markedF P g p (XR t))) Y=
      A Y*(complexity g p:ℝ)/((complexity g p:ℝ)*W P g p Y/W P g (p+1) Y) := by
  have hs' : Stable g (p+1) := by unfold Stable at *;omega
  have hFp : 0 < markedF P g p (XR Y) := by
    rw [←string_flow_proof P g p hs Y hY]
    exact shifted_zero_pos_of_W_pos P g p Y hY hWp
  have hd := (markedF_parameter_hasDerivAt P g p Y hY).log hFp.ne'
  rw [hd.deriv,←string_flow_proof P g p hs Y hY,←string_flow_proof P g (p+1) hs' Y hY]
  exact scaled_shifted_ratio_eq_W_inverse_of_pos P g p hs Y hY hWp hWc

lemma transport_equation_second_order_moment_proof (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y∈Ico (0:ℝ) y₀,
      |A Y*r Y*deriv (fun t => Real.log (markedF P g p (XR t))) Y-
        ((complexity g p:ℝ)+transportBeta p Y+
          (transportBeta p Y^2-transportBeta p Y-HigherOrder.secondDilatonMoment p Y/A Y)/(complexity g p:ℝ))| ≤
          C/(complexity g p:ℝ)^2 := by
  obtain ⟨C,hC,G,hbound⟩ := marked_cusp_inverse_third_order_proof P p
  obtain ⟨Gp,hPos⟩ := W_eventually_pos_all P p
  refine ⟨C,hC,2+G+Gp,?_⟩
  intro g hg Y hY
  have hgG : G ≤ g := by omega
  have hgP : Gp ≤ g := by omega
  have hYc : Y∈Icc (0:ℝ) y₀ := ⟨hY.1,hY.2.le⟩
  have hWp := hPos g hgP Y hYc
  have hWc := W_pos P g (p+1) (by omega) (by unfold Stable;omega) Y hYc
  rw [markedF_log_scaled_eq_inverse_of_W_pos P g p (by unfold Stable;omega) Y hY hWp hWc]
  exact hbound g hgG Y hYc
end WP

namespace WP
lemma transport_equation_second_order_proof (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y∈Ico (0:ℝ) y₀,
      |A Y*r Y*deriv (fun t => Real.log (markedF P g p (XR t))) Y-
        ((complexity g p:ℝ)+transportBeta p Y+
          HigherOrder.transportGamma p Y/(complexity g p:ℝ))| ≤
          C/(complexity g p:ℝ)^2 := by
  obtain ⟨C,hC,G,hraw⟩ := transport_equation_second_order_moment_proof P p
  refine ⟨C,hC,G,?_⟩
  intro g hg Y hY
  rw [HigherOrder.transportGamma_eq_secondDilatonMoment p Y ⟨hY.1,hY.2.le⟩]
  exact hraw g hg Y hY
end WP
