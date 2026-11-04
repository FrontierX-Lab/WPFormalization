import WPFormalization.Volumes.LocalComparisonModel
/-! Fixed-order local comparison in the genuine origin chart. All orders use
one canonical coefficient family and the original finite marked model. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma local_comparison_origin_chart (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B:ℝ)
    (hΩ:IsOpen Ω)(hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C)(hB:0<B)(hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃η R D E K:ℝ,0<η ∧ η<xCritical ∧ 0<R ∧ 0<D ∧ 0<E ∧ 0<K ∧
      (∀x∈Ioo (0:ℝ) η,Psi x≤K*x) ∧
      ∀g k J:ℕ,Stable g p→0<(complexity g p:ℝ)→
      (∀z∈Ω,1/2≤‖finiteMarkedFactor L (complexity g p:ℝ) J z‖ ∧
        ‖finiteMarkedFactor L (complexity g p:ℝ) J z‖≤2)→
      ∀ε:ℝ,0<ε→ε≤1/2→
      (∀Y∈Ico (0:ℝ) y₀,
        |(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
          realFiniteMarkedFactor P p (complexity g p:ℝ) J Y-1|≤ε)→
      ∀x∈Ioo (0:ℝ) η,(k:ℝ)=(complexity g p:ℝ)*Psi x→
      ∀r:ℝ,0<r→16*r<R*Real.sqrt ((complexity g p:ℝ)*x)→
      ∃M:ℂ→ℂ,IsLocalFiniteMarkedModel P g p k J x (16*r) M ∧
        (∀w:ℂ,‖w‖≤3*r/2→
          ‖centeredMarkedGenerating P g p k x
            (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) w-M w‖≤
              4*Real.sqrt ε*(D*Real.exp (E*(16*r)^2))) ∧
        r≤Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x):=by
  obtain ⟨S,Bc,ρs,Ds,Cs,hρs,hρsx,hDs,hCs,hSa,hS0,hSd,hBc0,hphys,hlocal,hAa,hAb,hArc⟩:=
    strong_origin_source_of_parameter_data P p Ω L C B hΩ hcover hC hB hLa hLr hLb
  have hBcA:AnalyticAt ℂ Bc 0:=(hlocal 0 (by simpa using hρs.le)).2.2.1
  have hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ):=by
    filter_upwards[eventually_lt_nhds hρs] with t ht htp
    exact (hphys t ⟨htp,ht.le⟩).1
  have hBr:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ):=by
    filter_upwards[eventually_lt_nhds hρs] with t ht htp
    exact (hphys t ⟨htp,ht.le⟩).2.2
  have hmap:=fun z hz=>(hlocal z hz).2.2.2.2
  obtain ⟨ηc,Rc,D,E,Kc,hηc,hηcs,hRc,hD,hE,hKc,hmean,hcompare⟩:=
    origin_actual_centered_complex_comparison_of_source P p hp Ω L S Bc ρs hρs hρsx
      hSa hSd hBcA (by rw[hBc0];norm_num) hSr hBr hmap
  obtain ⟨ηg,Rg,Cg,Dg,Kg,hηg,hηgs,hRg,hCg,hDg,hKg,hder,hgrowth⟩:=
    origin_finite_model_growth_of_source P p Ω L S Bc ρs hρs hρsx
      hSa hSd hBcA (by rw[hBc0];norm_num) hSr hBr hmap
  let η:ℝ:=min ηc ηg
  let R:ℝ:=min Rc (min Rg Real.pi)
  have hη:0<η:=lt_min hηc hηg
  have hηc':η≤ηc:=min_le_left _ _
  have hηg':η≤ηg:=min_le_right _ _
  have hηs:η<ρs:=hηc'.trans_lt hηcs
  have hR:0<R:=lt_min hRc (lt_min hRg Real.pi_pos)
  have hRc':R≤Rc:=min_le_left _ _
  have hRg':R≤Rg:=(min_le_right _ _).trans (min_le_left _ _)
  have hRpi:R≤Real.pi:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η,R,D,E,Kc,hη,hηs.trans hρsx,hR,hD,hE,hKc,?_,?_⟩
  · intro x hx
    exact hmean x ⟨hx.1,hx.2.trans_le hηc'⟩
  · intro g k J hs hh hP ε hε hεhalf hrel x hx hk r hr h16
    let h:ℝ:=complexity g p
    let σ:ℝ:=Real.sqrt (h*euler Psi x)
    let M:ℂ→ℂ:=centeredOriginFiniteModel P g p J S Bc L x
    have hxf:x∈Ico (0:ℝ) xCritical:=⟨hx.1.le,hx.2.trans (hηs.trans hρsx)⟩
    have hfinite:∀Y∈Icc (0:ℝ) y₀,
        finiteMarkedFactor L h J (Y:ℂ)=(realFiniteMarkedFactor P p h J Y:ℂ):=by
      intro Y hY
      simp only[finiteMarkedFactor,realFiniteMarkedFactor,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_pow]
      exact Finset.sum_congr rfl (fun j hj=>by rw[hLr j Y hY])
    have hPn:∀Y∈Icc (0:ℝ) y₀,realFiniteMarkedFactor P p h J Y≠0:=by
      intro Y hY hzero
      have ht:=(hP (Y:ℂ) (hcover Y hY)).1
      rw[hfinite Y hY,hzero,Complex.ofReal_zero,norm_zero] at ht
      norm_num at ht
    have hMa:∀z:ℂ,‖z‖≤ρs→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z:=by
      intro z hz
      have hl:=hlocal z hz
      exact ((analyticAt_const.mul hl.1).cexp.mul hl.2.2.1).mul
        (((finiteMarkedFactor_analyticOnNhd Ω L h J hLa) _ hl.2.2.2.2).comp
          (PositiveConvolution.planarInverse_analyticAt P z (hz.trans_lt hρsx)))
    have hreal:∀y∈Icc (0:ℝ) ρs,
        normalizedFiniteMarkedModel P g p S Bc L J (y:ℂ)≠0 ∧
        ‖normalizedMarkedGenerating P g p (y:ℂ)/normalizedFiniteMarkedModel P g p S Bc L J (y:ℂ)-1‖≤ε:=by
      intro y hy
      have hyx:y∈Ico (0:ℝ) xCritical:=⟨hy.1,hy.2.trans_lt hρsx⟩
      have hY:=(inverseY_branch y hyx).1
      have hYc:inverseY y∈Icc (0:ℝ) y₀:=⟨hY.1,hY.2.le⟩
      have hf:=hfinite _ hYc
      have ht:=hphys y hy
      refine ⟨?_,?_⟩
      · rw[normalizedFiniteMarkedModel_real P g p hs S Bc L J y hyx ht.1 ht.2.2 hf]
        exact_mod_cast mul_ne_zero
          (div_ne_zero (markedModel_pos_parameter g p hs _ hY).ne'
            (markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne') (hPn _ hYc)
      · rw[normalized_model_real_relative_error_identity P g p hs S Bc L J y hyx ht.1 ht.2.2 hf (hPn _ hYc)]
        have he:=hrel _ hY
        rw[(inverseY_branch y hyx).2] at he
        exact he
    have hgrow:=hgrowth g J hh hP hMa x ⟨hx.1,hx.2.trans_le hηg'⟩
    have h16g:16*r<Rg*Real.sqrt (h*x):=h16.trans_le (mul_le_mul_of_nonneg_right hRg' (Real.sqrt_nonneg _))
    refine ⟨M,⟨hgrow.1.mono (Metric.ball_subset_ball h16g.le),?_⟩,?_,?_⟩
    · intro u hu
      let xt:ℝ:=x*Real.exp (u/σ)
      have hxt0:0<xt:=mul_pos hx.1 (Real.exp_pos _)
      have hu':‖(u:ℂ)‖≤Rg*Real.sqrt (h*x):=by
        simpa only[Complex.norm_real,Real.norm_eq_abs] using hu.le.trans h16g.le
      have htilt:‖(x:ℂ)*Complex.exp ((u:ℂ)/(σ:ℂ))‖≤ρs:=(hgrow.2 (u:ℂ) hu').2
      have hzt:((x:ℂ)*Complex.exp ((u:ℂ)/(σ:ℂ)))=(xt:ℂ):=by
        dsimp[xt];rw[←Complex.ofReal_div,←Complex.ofReal_exp,←Complex.ofReal_mul]
      rw[hzt,Complex.norm_of_nonneg hxt0.le] at htilt
      have hxt:xt∈Ico (0:ℝ) xCritical:=⟨hxt0.le,htilt.trans_lt hρsx⟩
      have hxρ:x∈Icc (0:ℝ) ρs:=⟨hx.1.le,hx.2.le.trans hηs.le⟩
      have hxtρ:xt∈Icc (0:ℝ) ρs:=⟨hxt0.le,htilt⟩
      have hYx:=(inverseY_branch x hxf).1
      have hYt:=(inverseY_branch xt hxt).1
      have hMx:=normalizedFiniteMarkedModel_real P g p hs S Bc L J x hxf
        (hphys x hxρ).1 (hphys x hxρ).2.2 (hfinite _ ⟨hYx.1,hYx.2.le⟩)
      have hMt:=normalizedFiniteMarkedModel_real P g p hs S Bc L J xt hxt
        (hphys xt hxtρ).1 (hphys xt hxtρ).2.2 (hfinite _ ⟨hYt.1,hYt.2.le⟩)
      refine ⟨⟨hxt0,hxt.2⟩,?_⟩
      dsimp only[M,centeredOriginFiniteModel,localFiniteMarkedTrace]
      change Complex.exp (-(h:ℂ)*(Psi x:ℂ)*((u:ℂ)/(σ:ℂ)))*
        (normalizedFiniteMarkedModel P g p S Bc L J ((x:ℂ)*Complex.exp ((u:ℂ)/(σ:ℂ)))/
          normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ))=_
      rw[hzt,hMx,hMt]
      have hkc:(k:ℂ)=(h:ℂ)*(Psi x:ℂ):=by exact_mod_cast hk
      rw[hkc]
      have hM0:(markedModel g p 0:ℂ)≠0:=by
        exact_mod_cast (markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
      push_cast
      field_simp
      rfl
    · exact hcompare g k J hs hh hP hMa ε hε hεhalf hreal x
        ⟨hx.1,hx.2.trans_le hηc'⟩ hk r hr
        (h16.trans_le (mul_le_mul_of_nonneg_right hRc' (Real.sqrt_nonneg _)))
    · have hd:1≤deriv Psi x:=(hder x ⟨hx.1,hx.2.trans_le hηg'⟩).1
      have hv:h*x≤h*euler Psi x:=by
        dsimp[euler]
        nlinarith[mul_le_mul_of_nonneg_left hd (mul_nonneg hh.le hx.1.le)]
      have hsqrt:Real.sqrt (h*x)≤Real.sqrt (h*euler Psi x):=Real.sqrt_le_sqrt hv
      have ht:=h16.le.trans ((mul_le_mul hRpi hsqrt (Real.sqrt_nonneg _) Real.pi_pos.le))
      linarith
end WP.HigherOrder
