import WPFormalization.Volumes.OriginNormalization
noncomputable section
namespace WP
lemma volume_ratio_unmarked_product (P:PsiTheory)(g:ℕ)(hg:2≤g):
    volumeModel P g 0/leadingVolume g 0=
      Real.sqrt (1+1/(2*(g:ℝ)-1))*cuspCorrection P g 0 0*
        (volumeModel P g 1/leadingVolume g 1):=by
  have hgR:(2:ℝ)≤g:=by exact_mod_cast hg
  have hh:0<2*(g:ℝ)-2:=by linarith
  have hL0:0<leadingVolume g 0:=by
    simp only[leadingVolume,ite_true]
    have hG:=Real.Gamma_pos_of_pos hh
    positivity
  have hL1:0<leadingVolume g 1:=by
    rw[←markedModel_one_zero_leading g (by omega)]
    have hM:=markedModel_pos_parameter g 1 (by unfold Stable;omega) 0 ⟨le_rfl,y₀_pos⟩
    positivity
  have hden:4*Real.pi^2*(2*(g:ℝ)-2)≠0:=by positivity
  obtain ⟨hvol,hfac⟩:=unmarked_reduction P g hg
  change volumeModel P g 0=volumeModel P g 1*cuspCorrection P g 0 0/
    (4*Real.pi^2*(2*(g:ℝ)-2)) at hvol
  calc
    _=(volumeModel P g 1/leadingVolume g 1)*cuspCorrection P g 0 0*
      (leadingVolume g 1/(4*Real.pi^2*(2*(g:ℝ)-2)*leadingVolume g 0)):=by
        rw[hvol]
        field_simp[hden,hL0.ne',hL1.ne']
    _=_:=by rw[hfac];ring
end WP
