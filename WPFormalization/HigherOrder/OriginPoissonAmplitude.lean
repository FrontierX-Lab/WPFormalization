import WPFormalization.Volumes.OriginMarkedAmplitude
import WPFormalization.Analysis.PhaseAmplitudeUniform
noncomputable section
namespace WP.HigherOrder
open Set
def originPoissonAmplitude (P:PsiTheory) (p j:ℕ) (Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ)
    (Z:ℂ × ℂ → ℂ) (v:ℂ × ℂ):ℂ:=
  phaseAmplitude Z (originMarkedAmplitude P p j Bc L) v

lemma origin_poisson_amplitude_family_of_parameter_data (P:PsiTheory) (p:ℕ)
    (Ω:Set ℂ) (L:ℕ→ℂ→ℂ) (C B:ℝ)
    (hΩ:IsOpen Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C) (hB:0<B)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2)
    (Z:ℂ × ℂ → ℂ) (hZ:AnalyticAt ℂ Z 0) (hZ0:Z 0=0)
    (hU:AnalyticAt ℂ (phaseAmplitude Z (fun _:ℂ=>1)) 0):
    ∃(Bc:ℂ→ℂ)(ρ δ D:ℝ),0<ρ∧ρ<xCritical∧0<δ∧0<D∧Bc 0=1∧
      (∀x∈Ico (0:ℝ) xCritical,AnalyticAt ℂ Bc (x:ℂ)∧Bc (x:ℂ)=(extractionB p x:ℂ))∧
      (∀j,AnalyticOnNhd ℂ (originMarkedAmplitude P p j Bc L) (Metric.ball 0 ρ))∧
      (∀j,AnalyticOnNhd ℂ (originPoissonAmplitude P p j Bc L Z)
        (Metric.ball 0 δ ×ˢ Metric.ball 0 δ))∧
      (∀j v,v∈Metric.ball (0:ℂ) δ ×ˢ Metric.ball (0:ℂ) δ→
        ‖originPoissonAmplitude P p j Bc L Z v‖≤D*B^j*(j.factorial:ℝ)^2)∧
      (∀j x,x∈Icc (0:ℝ) ρ → originMarkedAmplitude P p j Bc L (x:ℂ)=
        ((extractionB p x*markedCoefficient P p j (inverseY x):ℝ):ℂ)):=by
  obtain ⟨Bc,ρ,D,hρ,hρx,hD,hBc0,hBcp,hlocal,hampA,hampB,hampR⟩:=
    origin_marked_amplitude_family_of_parameter_data P p Ω L C B hΩ hcover hC hB hLa hLr hLb
  have ha(j:ℕ) (z:ℂ) (hz:‖z‖<ρ):
      AnalyticAt ℂ (originMarkedAmplitude P p j Bc L) z∧
        ‖originMarkedAmplitude P p j Bc L z‖≤D*B^j*(j.factorial:ℝ)^2:=
    ⟨hampA j z (by simpa only[Metric.mem_ball,dist_zero_right] using hz),hampB j z hz.le⟩
  obtain ⟨δ,E,hδ,hE,hfam⟩:=Analysis.phaseAmplitude_uniform_gevrey_two_family Z hZ hZ0 hU ρ D B hρ hD
    (fun j=>originMarkedAmplitude P p j Bc L) ha
  exact ⟨Bc,ρ,δ,E,hρ,hρx,hδ,hE,hBc0,hBcp,hampA,fun j=>(hfam j).1,fun j=>(hfam j).2,hampR⟩
end WP.HigherOrder
