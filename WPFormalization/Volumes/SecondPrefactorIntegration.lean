import WPFormalization.Volumes.SecondTransportProof
import WPFormalization.Volumes.PrefactorIntegration
import WPFormalization.HigherOrder.FirstCorrectionPrimitive
import WPFormalization.Analysis.SecondLogScaleIntegration

/-! The genuine corrected marked logarithm has uniform second-order variation. The finite canonical transport coefficient and the actual removable primitive are both proved upstream; the final variation and long-interval theorems have no primitive or transport premises. -/

noncomputable section
open Set Filter
open scoped Topology

namespace WP

def correctedPrefactorLogError (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  prefactorLogError P g p Y-HigherOrder.firstMarkedCorrection p Y/(complexity g p:ℝ)

lemma correctedPrefactorLogError_hasDerivAt (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p)
    (hs : Stable g p) (Y : ℝ) (hY : Y∈Ioo (0:ℝ) y₀)
    (hL : HasDerivAt (HigherOrder.firstMarkedCorrection p)
      (HigherOrder.transportGamma p Y/(A Y*r Y)) Y) :
    HasDerivAt (correctedPrefactorLogError P g p)
      ((A Y*r Y*deriv (fun t => Real.log (markedF P g p (XR t))) Y-
        ((complexity g p:ℝ)+transportBeta p Y+HigherOrder.transportGamma p Y/(complexity g p:ℝ)))/(A Y*r Y)) Y := by
  have he := (prefactorLogError_hasDerivAt P g p hp hs Y hY).sub (hL.div_const (complexity g p:ℝ))
  convert he using 1
  · rfl
  · ring

lemma corrected_prefactor_variation_of_primitive (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (hLcont : ContinuousOn (HigherOrder.firstMarkedCorrection p) (Ico (0:ℝ) y₀))
    (hLderiv : ∀ Y∈Ioo (0:ℝ) y₀,HasDerivAt (HigherOrder.firstMarkedCorrection p)
      (HigherOrder.transportGamma p Y/(A Y*r Y)) Y)
    :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y∈Ico (0:ℝ) y₀,∀ B∈Ico (0:ℝ) y₀,Y ≤ B →
      |correctedPrefactorLogError P g p Y-correctedPrefactorLogError P g p B| ≤
        C/(complexity g p:ℝ)^2*(Real.log (Z Y)-Real.log (Z B)) := by
  obtain ⟨C,hC,G,hTransport⟩ := transport_equation_second_order_proof P p
  refine ⟨C,hC,max G 2,?_⟩
  intro g hg Y hY B hB hYB
  have hgG : G ≤ g := (le_max_left _ _).trans hg
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  have hs : Stable g p := by unfold Stable;omega
  have hhp : (0:ℝ)<complexity g p := by exact_mod_cast (show 0<complexity g p by unfold complexity;omega)
  have hsub : Icc Y B⊆Ico (0:ℝ) y₀ := fun x hx => ⟨hY.1.trans hx.1,hx.2.trans_lt hB.2⟩
  have hmem (x : ℝ) (hx : x∈Ioo Y B) : x∈Ioo (0:ℝ) y₀ :=
    ⟨hY.1.trans_lt hx.1,hx.2.trans hB.2⟩
  have hf : ContinuousOn (correctedPrefactorLogError P g p) (Icc Y B) :=
    ((prefactorLogError_continuousOn_parameter P g p hp hs).sub
      (hLcont.div_const (complexity g p:ℝ))).mono hsub
  rw [abs_sub_comm]
  apply Analysis.log_scale_variation_bound (correctedPrefactorLogError P g p) (fun x => Real.log (Z x))
    Y B (C/(complexity g p:ℝ)^2) hYB hf (Analysis.logZ_continuousOn_parameter.mono hsub)
  · intro x hx
    exact (correctedPrefactorLogError_hasDerivAt P g p hp hs x (hmem x hx) (hLderiv x (hmem x hx))).differentiableAt
  · intro x hx
    exact (Analysis.logZ_hasDerivAt_open_parameter x (hmem x hx)).differentiableAt
  · intro x hx
    have hxopen := hmem x hx
    have hxi : x∈Ico (0:ℝ) y₀ := ⟨hxopen.1.le,hxopen.2⟩
    have hAr : 0<A x*r x := mul_pos (Analysis.marked_A_pos x ⟨hxopen.1.le,hxopen.2.le⟩) (r_pos x hxi)
    rw [(correctedPrefactorLogError_hasDerivAt P g p hp hs x hxopen (hLderiv x hxopen)).deriv,
      (Analysis.logZ_hasDerivAt_open_parameter x hxopen).deriv,abs_div,abs_of_pos hAr]
    have he := hTransport g hgG x hxi
    calc
      _ ≤ (C/(complexity g p:ℝ)^2)/(A x*r x) := div_le_div_of_nonneg_right he hAr.le
      _ = _ := by ring

lemma corrected_prefactor_long_interval_of_primitive (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (hLcont : ContinuousOn (HigherOrder.firstMarkedCorrection p) (Ico (0:ℝ) y₀))
    (hLderiv : ∀ Y∈Ioo (0:ℝ) y₀,HasDerivAt (HigherOrder.firstMarkedCorrection p)
      (HigherOrder.transportGamma p Y/(A Y*r Y)) Y)
    :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,
      let h : ℝ := complexity g p
      let B : ℝ := y₀-(h⁻¹)^3
      B∈Ico (0:ℝ) y₀ ∧ ∀ Y∈Ico (0:ℝ) y₀,Y ≤ B →
        |correctedPrefactorLogError P g p Y-correctedPrefactorLogError P g p B| ≤
          C*Real.log ((g:ℝ)+1)/(g:ℝ)^2 := by
  obtain ⟨C,hC,G,hvar⟩ := corrected_prefactor_variation_of_primitive P p hp hLcont hLderiv
  exact Analysis.second_order_log_scale_long_interval p (fun g => correctedPrefactorLogError P g p) C hC G hvar
end WP

namespace WP
lemma corrected_prefactorLogError_variation (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y∈Ico (0:ℝ) y₀,∀ B∈Ico (0:ℝ) y₀,Y ≤ B →
      |correctedPrefactorLogError P g p Y-correctedPrefactorLogError P g p B| ≤
        C/(complexity g p:ℝ)^2*(Real.log (Z Y)-Real.log (Z B)) := by
  exact corrected_prefactor_variation_of_primitive P p hp
    ((HigherOrder.firstMarkedCorrection_continuousOn p).mono Ico_subset_Icc_self)
    (HigherOrder.firstMarkedCorrection_hasDerivAt p)

lemma corrected_prefactorLogError_long_interval (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g ≥ G,
      let h : ℝ := complexity g p
      let B : ℝ := y₀-(h⁻¹)^3
      B∈Ico (0:ℝ) y₀ ∧ ∀ Y∈Ico (0:ℝ) y₀,Y ≤ B →
        |correctedPrefactorLogError P g p Y-correctedPrefactorLogError P g p B| ≤
          C*Real.log ((g:ℝ)+1)/(g:ℝ)^2 := by
  obtain ⟨C,hC,G,hvar⟩ := corrected_prefactorLogError_variation P p hp
  exact Analysis.second_order_log_scale_long_interval p (fun g => correctedPrefactorLogError P g p) C hC G hvar
end WP
