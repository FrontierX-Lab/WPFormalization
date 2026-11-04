import Mathlib
/-! An actual integrable Fourier transform and local model are compared using the central pointwise error, full L1 norm, outer tail and true prefactor difference. -/
noncomputable section
open Set MeasureTheory
namespace WP.Analysis
lemma integral_sub_local_model_norm (F G:ℝ→ℂ) (T E R:ℝ) (hT:0≤T)
    (hF:Integrable F) (hG:IntegrableOn G (Icc (-T) T))
    (hpoint:∀t∈Icc (-T) T,‖F t-G t‖≤E)
    (htail:(∫t:ℝ in (Icc (-T) T)ᶜ,‖F t‖)≤R) :
    ‖(∫t:ℝ,F t)-(∫t:ℝ in Icc (-T) T,G t)‖≤R+2*T*E := by
  have hsplit:(∫t:ℝ in Icc (-T) T,F t)+(∫t:ℝ in (Icc (-T) T)ᶜ,F t)=∫t:ℝ,F t:=
    integral_add_compl measurableSet_Icc hF
  have hsub:(∫t:ℝ in Icc (-T) T,F t-G t)=
      (∫t:ℝ in Icc (-T) T,F t)-(∫t:ℝ in Icc (-T) T,G t):=integral_sub hF.integrableOn hG
  have hlocal:‖∫t:ℝ in Icc (-T) T,F t-G t‖≤2*T*E := by
    rw[integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by linarith:-T≤T)]
    have hbound:=intervalIntegral.norm_integral_le_of_norm_le_const (a:= -T) (b:=T) (C:=E) (by
      intro t ht
      have ht':t∈Ioc (-T) T:=by simpa only[uIoc_of_le (by linarith:-T≤T)] using ht
      exact hpoint t ⟨ht'.1.le,ht'.2⟩)
    have he':E*|T-(-T)|=2*T*E:=by rw[sub_neg_eq_add,abs_of_nonneg (by linarith:0≤T+T)];ring
    exact hbound.trans_eq he'
  have htail':‖∫t:ℝ in (Icc (-T) T)ᶜ,F t‖≤R:=
    (norm_integral_le_integral_norm _).trans htail
  calc _ = ‖(∫t:ℝ in (Icc (-T) T)ᶜ,F t)+(∫t:ℝ in Icc (-T) T,F t-G t)‖ := by
             rw[hsplit.symm,hsub]
             congr 1
             abel
       _ ≤ _:=by have hh:=(norm_add_le _ _).trans (add_le_add htail' hlocal);exact hh

lemma coefficient_prefactor_local_model_error (F G:ℝ→ℂ) (A B:ℂ)
    (T E R L D δ:ℝ) (hT:0≤T)
    (hF:Integrable F) (hG:IntegrableOn G (Icc (-T) T))
    (hpoint:∀t∈Icc (-T) T,‖F t-G t‖≤E)
    (htail:(∫t:ℝ in (Icc (-T) T)ᶜ,‖F t‖)≤R)
    (hfull:(∫t:ℝ,‖F t‖)≤L) (hB:‖B‖≤D) (hAB:‖A-B‖≤δ) :
    ‖A*(∫t:ℝ,F t)-B*(∫t:ℝ in Icc (-T) T,G t)‖≤δ*L+D*(R+2*T*E) := by
  have hL:0≤L:=(integral_nonneg (fun t=>norm_nonneg _)).trans hfull
  have hD:0≤D:=(norm_nonneg _).trans hB
  have hδ:0≤δ:=(norm_nonneg _).trans hAB
  have hI:‖∫t:ℝ,F t‖≤L:=(norm_integral_le_integral_norm _).trans hfull
  have hR:0≤R+2*T*E:=(norm_nonneg _).trans (integral_sub_local_model_norm F G T E R hT hF hG hpoint htail)
  have he:A*(∫t:ℝ,F t)-B*(∫t:ℝ in Icc (-T) T,G t)=
      (A-B)*(∫t:ℝ,F t)+B*((∫t:ℝ,F t)-(∫t:ℝ in Icc (-T) T,G t)):=by ring
  rw[he]
  apply (norm_add_le _ _).trans
  simp only[norm_mul]
  exact add_le_add (mul_le_mul hAB hI (norm_nonneg _) hδ)
    (mul_le_mul hB (integral_sub_local_model_norm F G T E R hT hF hG hpoint htail) (norm_nonneg _) hD)
end WP.Analysis
