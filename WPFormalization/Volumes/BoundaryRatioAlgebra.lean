import WPFormalization.Volumes.MarkedGeneratingPositivity
import WPFormalization.Volumes.BoundaryFourierInversion
import WPFormalization.Volumes.BoundaryFourierDomination
import WPFormalization.Volumes.VolumeRatiosEndpoints
import WPFormalization.Marked.ExternalStringUniformError
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology

lemma boundaryG_uniform_real_axis (P:PsiTheory)(p:ℕ)(hp:1≤p)(L₀:ℝ)(hL₀:0≤L₀) :
    ∃C:ℝ,0<C ∧ ∀g:ℕ,1≤g→∀x∈Ico (0:ℝ) xCritical,
      ∀L:Fin p→ℝ,(∀i,L i∈Icc 0 L₀)→
        |(boundaryG P g p L (x:ℂ)).re/
          (markedF P g p x*∏i,boundaryFactor (inverseY x) (L i))-1|≤C/g := by
  obtain ⟨C,hC,he⟩:=stringBoundaryAmplitude_uniform_real_axis P p hp L₀ hL₀
  refine ⟨C,hC,?_⟩
  intro g hg x hx L hL
  have hs:Stable g p:=by unfold Stable;omega
  have hF:markedF P g p x=shifted P g (List.replicate p 0) (inverseY x):=by
    unfold markedF
    rw [PositiveConvolution.Phi_iteratedDeriv_ofReal P g p hs x hx,Complex.ofReal_re]
  rw [boundaryG_ofReal P g p hp hs L x hx,Complex.ofReal_re,hF]
  exact he g hg (inverseY x) (inverseY_branch x hx).1 L hL

lemma boundary_volume_ratio_mass_identity (P:PsiTheory)(g p:ℕ)(hg:2≤g)(hp:1≤p)
    (L:Fin p→ℝ)(k:ℕ)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(B:ℝ)(hB:B≠0)
    (hm:cuspMass P g p k x≠0) :
    boundaryVolumeModel P g (k+p) (Fin.append (fun _:Fin k=>0) L)/
      (volumeModel P g (k+p)*B) =
      (boundaryMass P g p L k x/cuspMass P g p k x)*
        ((boundaryG P g p L (x:ℂ)).re/(markedF P g p x*B)) := by
  have hs:Stable g p:=by unfold Stable;omega
  have hF:markedF P g p x≠0:=(markedF_positive_cusp_weight P g p hp hs x ⟨hx.1.le,hx.2⟩).ne'
  have hG:(boundaryG P g p L (x:ℂ)).re≠0:=
    (boundaryG_real_pos P g p hp hs L x ⟨hx.1.le,hx.2⟩).ne'
  have hc:realCoeff (iteratedDeriv p (Phi P g)) k≠0:=by
    intro he
    apply hm
    simp [cuspMass,he]
  have hV:volumeModel P g (k+p)≠0:=by
    intro he
    apply hc
    rw [marked_realCoeff_volume,he,zero_div]
  have hGc:realCoeff (boundaryG P g p L) k =
      boundaryVolumeModel P g (k+p) (Fin.append (fun _:Fin k=>0) L)/
        ((2*Real.pi^2)^(dimension g (k+p))*(k.factorial:ℝ)):=by
    unfold realCoeff
    rw [boundaryG_coefficient P g p hg hp L k,Complex.ofReal_re]
  unfold boundaryMass cuspMass
  rw [hGc,marked_realCoeff_volume]
  have hpw:(2*Real.pi^2:ℝ)^(dimension g (k+p))≠0:=by positivity
  have hfac:(k.factorial:ℝ)≠0:=by positivity
  have hxpw:x^k≠0:=pow_ne_zero _ hx.1.ne'
  field_simp [hB,hF,hG,hV,hpw,hfac,hxpw]
  <;>ring

end WP.BoundaryConvolution
