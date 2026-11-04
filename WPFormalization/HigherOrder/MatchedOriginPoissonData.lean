import WPFormalization.HigherOrder.OriginPoissonRawMatchingCore
import WPFormalization.HigherOrder.OriginPoissonParameterFamily
import WPFormalization.HigherOrder.OriginModelGermMatching
import WPFormalization.Volumes.StrongOriginSource
/-! One actual source supplies both the original CG3 coefficient identities
and the uniform quantitative Poisson expansion of its finite model.
The canonical LC family and its Gevrey/native-budget constant B are fixed
before the density, genus, retained order and cutoff. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter MeasureTheory
open scoped Topology
lemma actual_matched_origin_poisson_data_of_parameter_data (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B:ℝ)
    (hΩ:IsOpen Ω)(hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C)(hB:0<B)(hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)(hL0:∀z,L 0 z=1)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃(S Bc:ℂ→ℂ)(Z:ℂ × ℂ→ℂ)(δ E D:ℝ),0<δ ∧ 0<E ∧ 0<D ∧
      AnalyticAt ℂ S 0 ∧ S 0=0 ∧ deriv S 0=2 ∧ Bc 0=1 ∧ AnalyticAt ℂ Bc 0 ∧
      (∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ)) ∧
      (∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ)) ∧
      (∀j,AnalyticOnNhd ℂ (normalizedPoissonFamilyCoefficient
        (fun s=>originPoissonAmplitude P p s Bc L Z) j) (Metric.ball 0 δ) ∧
        ∀z:ℂ,‖z‖<δ→‖normalizedPoissonFamilyCoefficient
          (fun s=>originPoissonAmplitude P p s Bc L Z) j z‖≤E*D^j*(j.factorial:ℝ)^2) ∧
      (∀j,normalizedPoissonFamilyCoefficient (fun s=>originPoissonAmplitude P p s Bc L Z) j 0=
        (markedCoefficient P p j 0:ℂ)) ∧
      (∀ν∈Ioo (0:ℝ) δ,∀j,normalizedPoissonFamilyCoefficient
        (fun s=>originPoissonAmplitude P p s Bc L Z) j (ν:ℂ)=
          (rawExtractedCoefficient P p j (densityY (2*ν)):ℂ)) ∧
      ∀g k K J:ℕ,0<(complexity g p:ℝ)→(k:ℝ)/(complexity g p:ℝ)≤δ→
        (K:ℝ)≤(complexity g p:ℝ)/2→K≤J→2*B*((J:ℝ)+1)^2≤(complexity g p:ℝ)→
        ‖WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k /
          ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)-
          ∑n∈Finset.range (K+1),((complexity g p:ℝ):ℂ)⁻¹^n*
            normalizedPoissonFamilyCoefficient (fun s=>originPoissonAmplitude P p s Bc L Z) n
              ((((k:ℝ)/(complexity g p:ℝ)):ℝ):ℂ)‖≤
          E*D^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1):=by
  obtain ⟨S,xco,Q,Z,Bc,R,ρ,A,hR,hρ,hρx,hA,hS,hS0,hSd,hSphys,hmatch,hxco,hQa,hZ,
    hx0,hxd,hQ0,hBc0,haxes,hphase,hfa,hfb,hHa,hHr,hterms⟩:=
      actual_origin_poisson_family_with_source_analytic P p Ω L C B hΩ hcover hC hB hLa hLr hLb
  let f:ℕ→ℂ × ℂ→ℂ:=fun s=>originPoissonAmplitude P p s Bc L Z
  have hball:Metric.ball (0:ℂ × ℂ) R⊆Metric.ball (0:ℂ) R ×ˢ Metric.ball (0:ℂ) R:=by
    intro v hv
    have hn:‖v‖<R:=by simpa only[Metric.mem_ball,dist_zero_right] using hv
    have hm:max ‖v.1‖ ‖v.2‖<R:=by simpa only[Prod.norm_def] using hn
    exact ⟨by simpa only[Metric.mem_ball,dist_zero_right] using (max_lt_iff.mp hm).1,
      by simpa only[Metric.mem_ball,dist_zero_right] using (max_lt_iff.mp hm).2⟩
  have hfa':∀j,AnalyticOnNhd ℂ (f j) (Metric.ball 0 R):=fun j=>(hfa j).mono hball
  have hfb':∀j v,v∈Metric.ball (0:ℂ × ℂ) R→‖f j v‖≤A*B^j*(j.factorial:ℝ)^2:=
    fun j v hv=>hfb j v (hball hv)
  have hZ0:Z 0=0:=(haxes 0 (by simpa only[norm_zero] using hR)).2.2.1
  have hq0:phaseQuotient Z 0 0≠0:=(hphase 0 0 (by simpa only[norm_zero] using hR)
    (by simpa only[norm_zero] using hR)).1
  have hf0j:∀j,f j (0,0)=(markedCoefficient P p j 0:ℂ):=by
    intro j
    exact originPoissonAmplitude_at_origin P p j Bc L Z hBc0
      (by simpa only[Complex.ofReal_zero] using hLr j 0 ⟨le_rfl,y₀_pos.le⟩) hZ0 hq0
  have hf0:f 0 (0,0)=1:=by rw[hf0j,markedCoefficient_zero,Complex.ofReal_one]
  obtain ⟨νe,E,D,hνe,hνeR,hE,hD,hunit,hcoefs,herror⟩:=
    normalizedPoissonFamilyOperator_uniform_expansion f R A B hR hA hB hfa' hfb' hf0
  have hEuler:∀ᶠt:ℝ in 𝓝 0,0≤t→(t:ℂ)*deriv S (t:ℂ)=(WP.Psi t:ℂ):=by
    filter_upwards[hSphys] with t ht ht0
    exact (ht ht0).2
  have hlead:=originPoissonFamily_leading_diagonal_germ P p Bc L S xco Q Z R ρ hR hρ hS
    (by rw[hSd];norm_num) (hxco 0 (by simpa only[Metric.mem_ball,dist_zero_right,norm_zero] using hR))
    hx0 hZ (fun ν hν=>⟨(haxes ν hν).1,(haxes ν hν).2.2⟩) hphase hEuler hHr
  have hgood:∀ᶠν:ℝ in 𝓝[≥] (0:ℝ),0<ν→
      S (xco (ν:ℂ))=(extractionS (XR (densityY (2*ν))):ℂ)∧
      Q (ν:ℂ)=((ν/XR (densityY (2*ν)):ℝ):ℂ)∧
      poissonFamilyCoefficient f 0 (ν:ℂ)=
        ((extractionB p (XR (densityY (2*ν)))*Real.sqrt (ν/WP.euler WP.Psi (XR (densityY (2*ν)))):ℝ):ℂ):=by
    filter_upwards[hmatch,hlead,WP.Analysis.densitySaddle_tendsto_zero_right.eventually hSphys,
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with ν hm hl hsp hνR hν
    have hn:‖(ν:ℂ)‖<R:=by simpa only[Complex.norm_real,Real.norm_eq_abs,abs_of_pos hν] using hνR
    have hx:0<XR (densityY (2*ν)):=(WP.Analysis.physicalDensitySaddle_spec ν hν).1.1
    refine ⟨by rw[hm];exact (hsp hx.le).1,?_,hl hν⟩
    rw[(haxes (ν:ℂ) hn).2.1 (by exact_mod_cast hν.ne'),hm]
    simp only[Complex.ofReal_div]
  obtain ⟨S1,Bc1,ρ1,D1,Cs,hρ1,hρ1x,hD1,hCs,hS1,hS10,hS1d,hBc10,hphys1,hlocal1,hH1a,hH1b,hcircle⟩:=
    strong_origin_source_of_parameter_data P p Ω L C B hΩ hcover hC hB hLa hLr hLb
  have hS1r:∀ᶠt:ℝ in 𝓝 0,0≤t→S1 (t:ℂ)=(extractionS t:ℂ):=by
    filter_upwards[eventually_lt_nhds hρ1] with t ht ht0
    exact (hphys1 t ⟨ht0,ht.le⟩).1
  have hB1r:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc1 (t:ℂ)=(extractionB p t:ℂ):=by
    filter_upwards[eventually_lt_nhds hρ1] with t ht ht0
    exact (hphys1 t ⟨ht0,ht.le⟩).2.2
  have hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ):=by
    filter_upwards[hSphys] with t ht ht0
    exact (ht ht0).1
  have hBc:AnalyticAt ℂ Bc 0:=origin_marked_Bc_analyticAt_zero P p Bc L hL0 (hHa 0)
  have hBcr:=origin_marked_Bc_real_germ P p Bc L ρ hρ hL0 (hHr 0)
  obtain ⟨δg,hδg,hgerm⟩:=normalizedFiniteMarkedModel_common_germ_of_real_trace P p S1 S Bc1 Bc L
    hS1 hS (by simpa only[Complex.ofReal_zero] using (hlocal1 0 (by simpa using hρ1.le)).2.2.1)
    hBc hS1r hSr hB1r hBcr
  have hceq:=originPhaseFamilyModel_coeff_eq_of_common_germ P p S1 S Bc1 Bc L δg hδg
    (fun z hz=>⟨(hgerm z hz).1,(hgerm z hz).2.1⟩)
  let Γ:ℕ→ℂ→ℂ:=fun s z=>L s (PositiveConvolution.planarInverse P z)
  have hΓa:∀s,AnalyticOnNhd ℂ (Γ s) (Metric.closedBall 0 (ρ1/2)):=by
    intro s z hz
    have hn:‖z‖≤ρ1/2:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hz
    have hloc:=hlocal1 z (by linarith)
    exact (hLa s _ hloc.2.2.2.2).comp (PositiveConvolution.planarInverse_analyticAt P z (by linarith))
  have hΓr(s:ℕ)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical):
      (fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(markedCoefficient P p s (inverseY t):ℂ)):=by
    filter_upwards[isOpen_Ioo.mem_nhds hx] with t ht
    have hy:inverseY t∈Icc (0:ℝ) y₀:=by
      have hh:=(inverseY_branch t ⟨ht.1.le,ht.2⟩).1
      exact ⟨hh.1,hh.2.le⟩
    dsimp[Γ]
    rw[PositiveConvolution.planarInverse_ofReal P t ⟨ht.1.le,ht.2⟩,hLr s _ hy]
  have hfinish:∀ᶠν:ℝ in 𝓝[≥] (0:ℝ),0<ν→∀j,
      normalizedPoissonFamilyCoefficient f j (ν:ℂ)=(rawExtractedCoefficient P p j (densityY (2*ν)):ℂ):=by
    filter_upwards[hgood,WP.Analysis.densitySaddle_tendsto_zero_right.eventually (eventually_lt_nhds (half_pos hρ1)),
      (eventually_lt_nhds hνe).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with ν hgoodν hxs hνe' hνR hν
    let x:ℝ:=XR (densityY (2*ν))
    have hx:x∈Ioo (0:ℝ) xCritical:=(WP.Analysis.physicalDensitySaddle_spec ν hν).1
    have hΨ:WP.Psi x=ν:=(WP.Analysis.physicalDensitySaddle_spec ν hν).2
    have hxρ:x<ρ1/2:=hxs
    have hxp:x∈Icc (0:ℝ) ρ1:=⟨hx.1.le,by linarith⟩
    have hSn:S1 (x:ℂ)=(extractionS x:ℂ):=(hphys1 x hxp).1
    have hBn:Bc1 (x:ℂ)=(extractionB p x:ℂ):=(hphys1 x hxp).2.2
    have htrace:(fun t:ℝ=>S1 (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)):=by
      filter_upwards[isOpen_Ioo.mem_nhds (show x∈Ioo (0:ℝ) ρ1 from ⟨hx.1,by linarith⟩)] with t ht
      exact (hphys1 t ⟨ht.1.le,ht.2.le⟩).1
    have hbtrace:(fun t:ℝ=>Bc1 (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionB p t:ℂ)):=by
      filter_upwards[isOpen_Ioo.mem_nhds (show x∈Ioo (0:ℝ) ρ1 from ⟨hx.1,by linarith⟩)] with t ht
      exact (hphys1 t ⟨ht.1.le,ht.2.le⟩).2.2
    have hS1a:AnalyticOnNhd ℂ S1 (Metric.closedBall 0 (ρ1/2)):=by
      intro z hz
      have hn:‖z‖≤ρ1/2:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hz
      exact (hlocal1 z (by linarith)).1
    have hBc1a:AnalyticOnNhd ℂ Bc1 (Metric.closedBall 0 (ρ1/2)):=by
      intro z hz
      have hn:‖z‖≤ρ1/2:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hz
      exact (hlocal1 z (by linarith)).2.2.1
    have hcoef:∀(h:ℝ)(k N:ℕ),0<h→h*WP.Psi x=(k:ℝ)→
        WP.coeff (phaseFamilyModel S1 (fun s z=>Bc1 z*Γ s z) h N) k=
          Complex.exp ((h:ℂ)*S1 (x:ℂ))*(x:ℂ)⁻¹^k*(poissonCenter k:ℂ)*poissonFamilyOperator f N h k:=by
      intro h k N hh hk
      have hkn:(k:ℝ)/h=ν:=(div_eq_iff hh.ne').mpr (by rw[←hΨ];nlinarith[hk])
      have hνc:(k:ℂ)/(h:ℂ)=(ν:ℂ):=by rw[←Complex.ofReal_natCast,←Complex.ofReal_div,hkn]
      have hn:‖(ν:ℂ)‖<R:=by rw[Complex.norm_of_nonneg hν.le];exact hνR
      have hfs(s:ℕ):AnalyticAt ℂ (fun u:ℂ=>f s (u,(((k:ℝ)/h:ℝ):ℂ))) 0:=by
        have hd:=hfa s ((0:ℂ),(ν:ℂ)) ⟨by simpa only[Metric.mem_ball,dist_zero_right,norm_zero] using hR,
          by simpa only[Metric.mem_ball,dist_zero_right] using hn⟩
        rw[hkn]
        exact AnalyticAt.comp (f:=fun u:ℂ=>(u,(ν:ℂ))) (x:=(0:ℂ)) hd (analyticAt_id.prod analyticAt_const)
      let T:ℂ:=Complex.exp ((h:ℂ)*(S (xco (ν:ℂ))-(ν:ℂ)+(ν:ℂ)*Complex.log (Q (ν:ℂ))))
      have hc:=phaseFamilyModel_coefficient_of_terms S (fun s=>originMarkedAmplitude P p s Bc L) f h hh k N T
        hS hHa hfs (by
          intro s
          have he:=hterms s (h:ℂ) k (by exact_mod_cast hh.ne') (by rw[hνc];exact hn)
          simpa only[hνc,hkn,T,f] using he)
      change WP.coeff (phaseFamilyModel S1 (fun s=>originMarkedAmplitude P p s Bc1 L) h N) k=_
      rw[hceq h N k,hc]
      have hpref:=WP.Analysis.poisson_phase_prefactor_complex h x (extractionS x) k hh hx.1
        (S (xco (ν:ℂ))) (Q (ν:ℂ)) (hgoodν hν).1 (by rw[hkn];exact (hgoodν hν).2.1)
      have hpref':T*(h:ℂ)^k/(k.factorial:ℂ)=
          Complex.exp ((h:ℂ)*S1 (x:ℂ))*(x:ℂ)⁻¹^k*(poissonCenter k:ℂ):=by
        have hknc:(((k:ℝ)/h:ℝ):ℂ)=(ν:ℂ):=by rw[hkn]
        simp only[Complex.ofReal_div,Complex.ofReal_natCast] at hknc
        rw[hknc] at hpref
        dsimp[T]
        rw[hpref,hSn]
        push_cast
        rfl
      rw[show T*(h:ℂ)^k/(k.factorial:ℂ)*poissonFamilyOperator f N h k=
        (T*(h:ℂ)^k/(k.factorial:ℂ))*poissonFamilyOperator f N h k by ring,hpref']
    intro j
    have he:=origin_poisson_raw_matching_core P p hp x hx (by rw[hΨ];exact hν) S1 Bc1 Γ (ρ1/2) B D1
      hxρ hB hD1 hS1a hBc1a hΓa htrace hbtrace (fun s=>hΓr s x hx)
      (fun s z hz=>hH1b s z (by linarith)) (hcircle x ⟨hx.1,by linarith⟩) f νe E D hE hD
      (by rw[hΨ];exact hνe'.le) (by rw[hΨ,hBn];simpa only[x,Complex.ofReal_mul] using (hgoodν hν).2.2) hcoef herror j
    rw[hΨ] at he
    exact he
  obtain ⟨r,hr,hrawr⟩:=Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hfinish)
  obtain ⟨rg,hrg,hgoodr⟩:=Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hgood)
  let δ:ℝ:=min (νe/2) (min (r/2) (rg/2))
  have hδ:0<δ:=lt_min (half_pos hνe) (lt_min (half_pos hr) (half_pos hrg))
  have hδν:δ<νe:=(min_le_left _ _).trans_lt (half_lt_self hνe)
  have hδr:δ<r:=((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hr)
  have hδrg:δ<rg:=((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hrg)
  have hexact:∀g k J:ℕ,0<(complexity g p:ℝ)→(k:ℝ)/(complexity g p:ℝ)≤δ→
      WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k /
        ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)=
        poissonFamilyOperator f J (complexity g p:ℝ) k/
          poissonFamilyCoefficient f 0 ((((k:ℝ)/(complexity g p:ℝ)):ℝ):ℂ):=by
    intro g k J hh hν
    let h:ℝ:=complexity g p
    let ν:ℝ:=(k:ℝ)/h
    have hν0:0≤ν:=by positivity
    have hνR:‖(k:ℂ)/(h:ℂ)‖<R:=by
      rw[←Complex.ofReal_natCast,←Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hν0]
      exact hν.trans_lt (hδν.trans hνeR)
    have hfs:∀j,AnalyticAt ℂ (fun u=>f j (u,(ν:ℂ))) 0:=by
      intro j
      exact (hfa j (0,(ν:ℂ)) ⟨by simpa only[Metric.mem_ball,dist_zero_right,norm_zero] using hR,
        by simpa only[Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hν0] using
          hν.trans_lt (hδν.trans hνeR)⟩).comp (f:=fun u:ℂ=>(u,(ν:ℂ)))
            (analyticAt_id.prod analyticAt_const)
    have hc:WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k=
        Complex.exp ((h:ℂ)*(S (xco ((k:ℂ)/(h:ℂ)))-(k:ℂ)/(h:ℂ)+
          ((k:ℂ)/(h:ℂ))*Complex.log (Q ((k:ℂ)/(h:ℂ)))))*(h:ℂ)^k/(k.factorial:ℂ)*
          poissonFamilyOperator f J h k:=by
      rw[normalizedFiniteMarkedModel_eq_phaseFamilyModel]
      apply phaseFamilyModel_coefficient_of_terms S _ f h hh k J _ hS hHa hfs
      intro j
      simpa only[ν,Complex.ofReal_div,Complex.ofReal_natCast] using hterms j (h:ℂ) k (by exact_mod_cast (show h≠0 from hh.ne')) hνR
    by_cases hk:k=0
    · subst k
      simp only[Nat.cast_zero,zero_div,Complex.ofReal_zero]
      exact originPoisson_exact_normalized_coefficient_zero P g p J S Bc L f xco Q hh hS0 hx0
        (by rw[poissonFamilyCoefficient_at_zero,hf0]) (by simpa only[Nat.cast_zero] using hc)
    have hνp:0<ν:=div_pos (by exact_mod_cast Nat.pos_of_ne_zero hk) hh
    have hg:=hgoodr (show dist ν 0<rg by rw[Real.dist_eq,sub_zero,abs_of_pos hνp];exact hν.trans_lt hδrg) hν0 hνp
    exact originPoisson_exact_normalized_coefficient_positive P g p k J S Bc L f xco Q hh hk hc hg.1 hg.2.1 hg.2.2
  refine ⟨S,Bc,Z,δ,E,D,hδ,hE,hD,hS,hS0,hSd,hBc0,hBc,hSr,hBcr,?_,?_,?_,?_⟩
  · intro j
    exact ⟨(hcoefs j).1.mono (Metric.ball_subset_ball hδν.le),fun z hz=>(hcoefs j).2 z (hz.trans hδν)⟩
  · intro j
    rw[normalizedPoissonFamilyCoefficient_at_zero f hf0,hf0j]
  · intro ν hν j
    have he:=hrawr (show dist ν 0<r by rw[Real.dist_eq,sub_zero,abs_of_pos hν.1];exact hν.2.trans hδr) hν.1.le
    exact he hν.1 j
  · intro g k K J hh hν hK hKJ hw
    rw[hexact g k J hh hν]
    exact herror (complexity g p:ℝ) k K J hh (hν.trans hδν.le) hK hKJ hw
end WP.HigherOrder
