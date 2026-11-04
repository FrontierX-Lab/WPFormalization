import WPFormalization.HigherOrder.OriginPoissonNormalization
import WPFormalization.Volumes.CriticalLogZ
import WPFormalization.Analysis.CoefficientScaling
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma originMarkedAmplitude_zero_eq_Bc (P:PsiTheory) (p:ℕ) (Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ)
    (hL0:∀z,L 0 z=1):originMarkedAmplitude P p 0 Bc L=Bc:=by
  funext z
  simp only[originMarkedAmplitude,hL0,mul_one]
lemma origin_marked_Bc_analyticAt_zero (P:PsiTheory) (p:ℕ) (Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ)
    (hL0:∀z,L 0 z=1) (hHa:AnalyticAt ℂ (originMarkedAmplitude P p 0 Bc L) 0):
    AnalyticAt ℂ Bc 0:=by
  simpa only[originMarkedAmplitude_zero_eq_Bc P p Bc L hL0] using hHa
lemma origin_marked_Bc_real_germ (P:PsiTheory) (p:ℕ) (Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ)
    (ρ:ℝ) (hρ:0<ρ) (hL0:∀z,L 0 z=1)
    (hHr:∀t,t∈Icc (0:ℝ) ρ→ originMarkedAmplitude P p 0 Bc L (t:ℂ)=
      ((extractionB p t*markedCoefficient P p 0 (inverseY t):ℝ):ℂ)):
    ∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ):=by
  filter_upwards[eventually_lt_nhds hρ] with t ht ht0
  have he:=hHr t ⟨ht0,ht.le⟩
  simpa only[originMarkedAmplitude_zero_eq_Bc P p Bc L hL0,markedCoefficient_zero,mul_one] using he
lemma normalizedFiniteMarkedModel_common_germ_of_real_trace (P:PsiTheory) (p:ℕ)
    (S₁ S₂ Bc₁ Bc₂:ℂ→ℂ) (L:ℕ→ℂ→ℂ)
    (hS₁:AnalyticAt ℂ S₁ 0) (hS₂:AnalyticAt ℂ S₂ 0)
    (hBc₁:AnalyticAt ℂ Bc₁ 0) (hBc₂:AnalyticAt ℂ Bc₂ 0)
    (hSr₁:∀ᶠt:ℝ in 𝓝 0,0≤t→S₁ (t:ℂ)=(extractionS t:ℂ))
    (hSr₂:∀ᶠt:ℝ in 𝓝 0,0≤t→S₂ (t:ℂ)=(extractionS t:ℂ))
    (hBr₁:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc₁ (t:ℂ)=(extractionB p t:ℂ))
    (hBr₂:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc₂ (t:ℂ)=(extractionB p t:ℂ)):
    ∃δ:ℝ,0<δ∧∀z:ℂ,‖z‖<δ→S₁ z=S₂ z∧Bc₁ z=Bc₂ z∧
      ∀g J:ℕ,normalizedFiniteMarkedModel P g p S₁ Bc₁ L J z=
        normalizedFiniteMarkedModel P g p S₂ Bc₂ L J z:=by
  have hSg:S₁=ᶠ[𝓝 0] S₂:=by
    apply Analysis.complex_germ_identity_of_real_right S₁ S₂ hS₁ hS₂
    filter_upwards[hSr₁,hSr₂] with t ht1 ht2 ht
    exact (ht1 ht.le).trans (ht2 ht.le).symm
  have hBg:Bc₁=ᶠ[𝓝 0] Bc₂:=by
    apply Analysis.complex_germ_identity_of_real_right Bc₁ Bc₂ hBc₁ hBc₂
    filter_upwards[hBr₁,hBr₂] with t ht1 ht2 ht
    exact (ht1 ht.le).trans (ht2 ht.le).symm
  obtain ⟨δ,hδ,hloc⟩:=Metric.eventually_nhds_iff.mp (hSg.and hBg)
  refine ⟨δ,hδ,?_⟩
  intro z hz
  have he:=hloc (by simpa only[dist_zero_right] using hz)
  refine ⟨he.1,he.2,?_⟩
  intro g J
  simp only[normalizedFiniteMarkedModel,he.1,he.2]
lemma normalizedFiniteMarkedModel_coeff_eq_of_common_germ (P:PsiTheory) (p:ℕ)
    (S₁ S₂ Bc₁ Bc₂:ℂ→ℂ) (L:ℕ→ℂ→ℂ) (δ:ℝ) (hδ:0<δ)
    (he:∀z:ℂ,‖z‖<δ→∀g J:ℕ,normalizedFiniteMarkedModel P g p S₁ Bc₁ L J z=
      normalizedFiniteMarkedModel P g p S₂ Bc₂ L J z):
    ∀g J k:ℕ,WP.coeff (normalizedFiniteMarkedModel P g p S₁ Bc₁ L J) k=
      WP.coeff (normalizedFiniteMarkedModel P g p S₂ Bc₂ L J) k:=by
  intro g J k
  apply Analysis.coeff_congr_of_eventuallyEq
  filter_upwards[Metric.ball_mem_nhds (0:ℂ) hδ] with z hz
  exact he z (by simpa only[Metric.mem_ball,dist_zero_right] using hz) g J
end WP.HigherOrder

namespace WP.HigherOrder
open Filter
open scoped Topology
lemma originPhaseFamilyModel_coeff_eq_of_common_germ (P:PsiTheory) (p:ℕ)
    (S₁ S₂ Bc₁ Bc₂:ℂ→ℂ) (L:ℕ→ℂ→ℂ) (δ:ℝ) (hδ:0<δ)
    (he:∀z:ℂ,‖z‖<δ→S₁ z=S₂ z∧Bc₁ z=Bc₂ z):
    ∀(h:ℝ)(J k:ℕ),WP.coeff (phaseFamilyModel S₁ (fun s=>originMarkedAmplitude P p s Bc₁ L) h J) k=
      WP.coeff (phaseFamilyModel S₂ (fun s=>originMarkedAmplitude P p s Bc₂ L) h J) k:=by
  intro h J k
  apply Analysis.coeff_congr_of_eventuallyEq
  filter_upwards[Metric.ball_mem_nhds (0:ℂ) hδ] with z hz
  have ht:=he z (by simpa only[Metric.mem_ball,dist_zero_right] using hz)
  simp only[phaseFamilyModel,originMarkedAmplitude,ht.1,ht.2]
end WP.HigherOrder
