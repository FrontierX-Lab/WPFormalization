import WPFormalization.Volumes.BoundaryScaledFourierTail
import WPFormalization.Volumes.BoundaryRatioAlgebra
import WPFormalization.Statements.CuspLocalLimit
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter MeasureTheory
open scoped Topology

lemma boundary_real_axis_ratio_tendsto (P:PsiTheory)(p:ℕ)(hp:1≤p)(L₀:ℝ)(hL₀:0≤L₀)
    (gs:ℕ→ℕ)(xs:ℕ→ℝ)(Ls:ℕ→Fin p→ℝ)
    (hg:Tendsto gs atTop atTop)(hx:∀j,xs j∈Ioo (0:ℝ) xCritical)
    (hL:∀j i,Ls j i∈Icc 0 L₀) :
    Tendsto (fun j=>(boundaryG P (gs j) p (Ls j) (xs j:ℂ)).re/
      (markedF P (gs j) p (xs j)*∏i,boundaryFactor (inverseY (xs j)) (Ls j i))) atTop (𝓝 1) := by
  obtain ⟨C,hC,he⟩:=boundaryG_uniform_real_axis P p hp L₀ hL₀
  have hgr:Tendsto (fun j=>(gs j:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp hg
  have hr:Tendsto (fun j=>C/(gs j:ℝ)) atTop (𝓝 0):=hgr.const_div_atTop C
  have hh:∀ᶠj:ℕ in atTop,
      |(boundaryG P (gs j) p (Ls j) (xs j:ℂ)).re/
        (markedF P (gs j) p (xs j)*∏i,boundaryFactor (inverseY (xs j)) (Ls j i))-1|≤C/(gs j:ℝ):=by
    filter_upwards [hg.eventually_ge_atTop 1] with j hj
    exact he (gs j) hj (xs j) ⟨(hx j).1.le,(hx j).2⟩ (Ls j) (hL j)
  have ht:Tendsto (fun j=>(boundaryG P (gs j) p (Ls j) (xs j:ℂ)).re/
      (markedF P (gs j) p (xs j)*∏i,boundaryFactor (inverseY (xs j)) (Ls j i))-1) atTop (𝓝 0):=by
    apply squeeze_zero_norm' _ hr
    simpa only [Real.norm_eq_abs] using hh
  have ht':=ht.add_const 1
  simpa only [zero_add,sub_add_cancel] using ht'

lemma boundaryMass_scaled_tendsto_of_l1 (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (gs ks:ℕ→ℕ)(xs:ℕ→ℝ)(Ls:ℕ→Fin p→ℝ)
    (hg:Tendsto gs atTop atTop)(hx:∀j,xs j∈Ioo (0:ℝ) xCritical)
    (hcenter:∀j,(complexity (gs j) p:ℝ)*Psi (xs j)=(ks j:ℝ))
    (hl1:Tendsto (fun j=>∫t:ℝ,‖scaledBoundaryFourier P (gs j) p (Ls j) (xs j) t-
      Complex.exp (-(t:ℂ)^2/2)‖) atTop (𝓝 0)) :
    Tendsto (fun j=>Real.sqrt ((complexity (gs j) p:ℝ)*euler Psi (xs j))*
      boundaryMass P (gs j) p (Ls j) (ks j) (xs j)) atTop (𝓝 (1/Real.sqrt (2*Real.pi))) := by
  let E:ℕ→ℝ:=fun j=>∫t:ℝ,‖scaledBoundaryFourier P (gs j) p (Ls j) (xs j) t-
    Complex.exp (-(t:ℂ)^2/2)‖
  have he:∀ᶠj:ℕ in atTop,
      |Real.sqrt ((complexity (gs j) p:ℝ)*euler Psi (xs j))*
        boundaryMass P (gs j) p (Ls j) (ks j) (xs j)-1/Real.sqrt (2*Real.pi)|≤E j/(2*Real.pi):=by
    filter_upwards [hg.eventually_ge_atTop 2] with j hj
    have hs:Stable (gs j) p:=by unfold Stable;omega
    have hh:0<complexity (gs j) p:=by unfold complexity;omega
    have ht:=boundaryMass_error_of_characteristic_l1 P (gs j) p hp hs (Ls j) hh
      (xs j) (hx j) (E j) le_rfl (ks j:ℤ)
    dsimp only at ht
    simpa only [Int.natCast_nonneg,ite_true,Int.toNat_natCast,Int.cast_natCast,
      hcenter j,sub_self,zero_pow (by norm_num:2≠0),zero_div,neg_zero,Real.exp_zero] using ht
  have hlim:Tendsto (fun j=>E j/(2*Real.pi)) atTop (𝓝 0):=by
    simpa only [zero_div] using hl1.div_const (2*Real.pi)
  have ht:Tendsto (fun j=>Real.sqrt ((complexity (gs j) p:ℝ)*euler Psi (xs j))*
      boundaryMass P (gs j) p (Ls j) (ks j) (xs j)-1/Real.sqrt (2*Real.pi)) atTop (𝓝 0):=by
    apply squeeze_zero_norm' _ hlim
    simpa only [Real.norm_eq_abs] using he
  have ht':=ht.add_const (1/Real.sqrt (2*Real.pi))
  simpa only [zero_add,sub_add_cancel] using ht'

lemma boundary_volume_ratio_tendsto_of_l1 (P:PsiTheory)(p:ℕ)(hp:1≤p)(L₀:ℝ)(hL₀:0≤L₀)
    (gs ks:ℕ→ℕ)(xs:ℕ→ℝ)(Ls:ℕ→Fin p→ℝ)
    (hg:Tendsto gs atTop atTop)(hx:∀j,xs j∈Ioo (0:ℝ) xCritical)
    (hL:∀j i,Ls j i∈Icc 0 L₀)
    (hmu:Tendsto (fun j=>(complexity (gs j) p:ℝ)*Psi (xs j)) atTop atTop)
    (hcenter:∀j,(complexity (gs j) p:ℝ)*Psi (xs j)=(ks j:ℝ))
    (hl1:Tendsto (fun j=>∫t:ℝ,‖scaledBoundaryFourier P (gs j) p (Ls j) (xs j) t-
      Complex.exp (-(t:ℂ)^2/2)‖) atTop (𝓝 0)) :
    Tendsto (fun j=>boundaryVolumeModel P (gs j) (ks j+p)
      (Fin.append (fun _:Fin (ks j)=>0) (Ls j))/
      (volumeModel P (gs j) (ks j+p)*∏i,boundaryFactor (inverseY (xs j)) (Ls j i))) atTop (𝓝 1) := by
  let σ:ℕ→ℝ:=fun j=>Real.sqrt ((complexity (gs j) p:ℝ)*euler Psi (xs j))
  let c:ℝ:=1/Real.sqrt (2*Real.pi)
  have hc:0<c:=by dsimp [c];positivity
  have hGB:=boundaryMass_scaled_tendsto_of_l1 P p hp gs ks xs Ls hg hx hcenter hl1
  change Tendsto (fun j=>σ j*boundaryMass P (gs j) p (Ls j) (ks j) (xs j)) atTop (𝓝 c) at hGB
  have hu:Tendsto (fun j=>((ks j:ℝ)-(complexity (gs j) p:ℝ)*Psi (xs j))/σ j) atTop (𝓝 0):=by
    have he:(fun j=>((ks j:ℝ)-(complexity (gs j) p:ℝ)*Psi (xs j))/σ j)=(fun _:ℕ=>(0:ℝ)):=by
      funext j
      rw [hcenter j,sub_self,zero_div]
    rw [he]
    exact tendsto_const_nhds
  have hFB:Tendsto (fun j=>σ j*cuspMass P (gs j) p (ks j) (xs j)) atTop (𝓝 c):=by
    simpa only [neg_zero,zero_pow (by norm_num:2≠0),zero_div,Real.exp_zero] using
      cusp_local_limit P p hp gs xs ks 0 hg hx hmu hu
  have hmnon:∀ᶠj:ℕ in atTop,cuspMass P (gs j) p (ks j) (xs j)≠0:=by
    filter_upwards [hFB.eventually (lt_mem_nhds hc)] with j hj
    exact right_ne_zero_of_mul (ne_of_gt hj)
  have hσnon:∀ᶠj:ℕ in atTop,σ j≠0:=by
    filter_upwards [hFB.eventually (lt_mem_nhds hc)] with j hj
    exact left_ne_zero_of_mul (ne_of_gt hj)
  have hmass:Tendsto (fun j=>boundaryMass P (gs j) p (Ls j) (ks j) (xs j)/
      cuspMass P (gs j) p (ks j) (xs j)) atTop (𝓝 1):=by
    have ht:=hGB.div hFB hc.ne'
    simp only [div_self hc.ne'] at ht
    apply ht.congr'
    filter_upwards [hσnon] with j hj
    exact mul_div_mul_left _ _ hj
  have hreal:=boundary_real_axis_ratio_tendsto P p hp L₀ hL₀ gs xs Ls hg hx hL
  have ht:=hmass.mul hreal
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [hg.eventually_ge_atTop 2,hmnon] with j hj hmj
  exact (boundary_volume_ratio_mass_identity P (gs j) p hj hp (Ls j) (ks j) (xs j) (hx j)
    (∏i,boundaryFactor (inverseY (xs j)) (Ls j i))
    (Finset.prod_ne_zero_iff.mpr (fun i hi=>(boundaryFactor_pos _ _).ne')) hmj).symm

end WP.BoundaryConvolution
