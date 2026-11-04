import WPFormalization.HigherOrder.PhaseFamilyModel
import WPFormalization.HigherOrder.PoissonFamilyNormalizedExpansion
import WPFormalization.HigherOrder.OriginPoissonLeading
import WPFormalization.HigherOrder.OriginPoissonSourceAnalytic
import WPFormalization.Analysis.PoissonPhasePrefactor
import WPFormalization.Volumes.OriginFiniteModel
noncomputable section
namespace WP.HigherOrder
lemma normalizedFiniteMarkedModel_eq_phaseFamilyModel (P:PsiTheory) (g p:ℕ)
    (S Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ) (J:ℕ):
    normalizedFiniteMarkedModel P g p S Bc L J=
      phaseFamilyModel S (fun s=>originMarkedAmplitude P p s Bc L) (complexity g p:ℝ) J:=by
  funext z
  simp only[normalizedFiniteMarkedModel,phaseFamilyModel,originMarkedAmplitude,finiteMarkedFactor,
    Complex.ofReal_natCast,div_eq_mul_inv,Finset.mul_sum]
  congr 1
  funext s
  simp only[inv_pow]
  ring
lemma originPoisson_exact_normalized_coefficient_positive (P:PsiTheory) (g p k J:ℕ)
    (S Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ) (f:ℕ→ℂ × ℂ → ℂ)
    (xco Q:ℂ→ℂ) (hh:0<(complexity g p:ℝ)) (hk:k≠0)
    (hcoef:let h:ℝ:=complexity g p;let ν:ℂ:=(k:ℂ)/(h:ℂ);
      WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k=
        Complex.exp ((h:ℂ)*(S (xco ν)-ν+ν*Complex.log (Q ν)))*(h:ℂ)^k/(k.factorial:ℂ)*
          poissonFamilyOperator f J h k)
    (hS:let h:ℝ:=complexity g p;let ν:ℝ:=(k:ℝ)/h;
      S (xco (ν:ℂ))=(extractionS (XR (densityY (2*ν))):ℂ))
    (hQ:let h:ℝ:=complexity g p;let ν:ℝ:=(k:ℝ)/h;
      Q (ν:ℂ)=((ν/(XR (densityY (2*ν))):ℝ):ℂ))
    (hE:let h:ℝ:=complexity g p;let ν:ℝ:=(k:ℝ)/h;
      poissonFamilyCoefficient f 0 (ν:ℂ)=
        ((extractionB p (XR (densityY (2*ν)))*Real.sqrt (ν/WP.euler WP.Psi (XR (densityY (2*ν)))):ℝ):ℂ)):
    WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k /
      ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)=
      poissonFamilyOperator f J (complexity g p:ℝ) k /
        poissonFamilyCoefficient f 0 ((((k:ℝ)/(complexity g p:ℝ)):ℝ):ℂ):=by
  let h:ℝ:=complexity g p
  let ν:ℝ:=(k:ℝ)/h
  let x:ℝ:=XR (densityY (2*ν))
  let V:ℝ:=Real.exp (h*extractionS x)*x⁻¹^k*poissonCenter k
  have hν:0<ν:=div_pos (by exact_mod_cast Nat.pos_of_ne_zero hk) hh
  have hx:0<x:=(Analysis.physicalDensitySaddle_spec ν hν).1.1
  have he:Complex.exp ((h:ℂ)*(S (xco (ν:ℂ))-(ν:ℂ)+(ν:ℂ)*Complex.log (Q (ν:ℂ))))*(h:ℂ)^k/(k.factorial:ℂ)=(V:ℂ):=by
    simpa only[V,ν,Complex.ofReal_div,Complex.ofReal_natCast] using
      Analysis.poisson_phase_prefactor_complex h x (extractionS x) k hh hx (S (xco (ν:ℂ))) (Q (ν:ℂ)) hS hQ
  have hv:0<V:=by
    dsimp[V,poissonCenter]
    positivity
  have hm:markedModel g p 0≠0:=by
    have hs:Stable g p:=by
      have hn:0<complexity g p:=by exact_mod_cast hh
      unfold Stable complexity at *
      omega
    exact (markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  have hd:((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)=(V:ℂ)*poissonFamilyCoefficient f 0 (ν:ℂ):=by
    rw[hE,←Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    have hf:=Analysis.extractionQ_factorization_positive g p k hk hh
    change Real.pi*extractionQ g p k/markedModel g p 0=
      V*(extractionB p x*Real.sqrt (ν/WP.euler WP.Psi x))
    rw[hf]
    dsimp only[V,h,ν,x]
    field_simp
  have hc:WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k=(V:ℂ)*poissonFamilyOperator f J h k:=by
    convert! hcoef using 1
    simpa only[ν,h,Complex.ofReal_div,Complex.ofReal_natCast] using
      (congrArg (fun t:ℂ=>t*poissonFamilyOperator f J h k) he).symm
  change WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k / _=
    poissonFamilyOperator f J h k/poissonFamilyCoefficient f 0 (ν:ℂ)
  rw[hc,hd]
  have hv0:(V:ℂ)≠0:=by exact_mod_cast hv.ne'
  exact mul_div_mul_left _ _ hv0
end WP.HigherOrder

namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma originPoisson_exact_normalized_coefficient_zero (P:PsiTheory) (g p J:ℕ)
    (S Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ) (f:ℕ→ℂ × ℂ → ℂ)
    (xco Q:ℂ→ℂ) (hh:0<(complexity g p:ℝ)) (hS0:S 0=0) (hx0:xco 0=0)
    (hE:poissonFamilyCoefficient f 0 0=1)
    (hcoef:let h:ℝ:=complexity g p;let ν:ℂ:=(0:ℂ)/(h:ℂ);
      WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) 0=
        Complex.exp ((h:ℂ)*(S (xco ν)-ν+ν*Complex.log (Q ν)))*(h:ℂ)^0/((0:ℕ).factorial:ℂ)*
          poissonFamilyOperator f J h 0):
    WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) 0 /
      ((Real.pi*extractionQ g p 0/markedModel g p 0:ℝ):ℂ)=
      poissonFamilyOperator f J (complexity g p:ℝ) 0/poissonFamilyCoefficient f 0 0:=by
  have hm:markedModel g p 0≠0:=by
    have hs:Stable g p:=by
      have hn:0<complexity g p:=by exact_mod_cast hh
      unfold Stable complexity at *
      omega
    exact (markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
  have hd:((Real.pi*extractionQ g p 0/markedModel g p 0:ℝ):ℂ)=1:=by
    rw[Analysis.extractionQ_zero_exact]
    norm_cast
    field_simp
  rw[hd,hE,div_one,div_one]
  simpa only[zero_div,hx0,hS0,sub_zero,zero_mul,add_zero,mul_zero,Complex.exp_zero,
    pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul] using hcoef
lemma actual_origin_poisson_normalized_model_data_of_parameter_data (P:PsiTheory) (p:ℕ)
    (Ω:Set ℂ) (L:ℕ→ℂ→ℂ) (C B:ℝ)
    (hΩ:IsOpen Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C) (hB:0<B)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃(S Bc:ℂ→ℂ)(Z:ℂ × ℂ → ℂ)(R ν₀ ρ A E D:ℝ),
      0<R∧0<ν₀∧ν₀<R∧0<ρ∧0<A∧0<E∧0<D∧
      AnalyticAt ℂ S 0∧S 0=0∧deriv S 0=2∧Bc 0=1∧
      (∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ))∧
      (∀j,AnalyticAt ℂ (originMarkedAmplitude P p j Bc L) 0)∧
      (∀j t,t∈Icc (0:ℝ) ρ→ originMarkedAmplitude P p j Bc L (t:ℂ)=
        ((extractionB p t*markedCoefficient P p j (inverseY t):ℝ):ℂ))∧
      (∀j,AnalyticOnNhd ℂ (originPoissonAmplitude P p j Bc L Z) (Metric.ball 0 R))∧
      (∀j v,v∈Metric.ball (0:ℂ × ℂ) R→‖originPoissonAmplitude P p j Bc L Z v‖≤A*B^j*(j.factorial:ℝ)^2)∧
      (∀n,AnalyticOnNhd ℂ (normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n)
        (Metric.ball 0 ν₀)∧∀ν:ℂ,‖ν‖<ν₀→
        ‖normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n ν‖≤E*D^n*(n.factorial:ℝ)^2)∧
      (∀n,normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n 0=
        (markedCoefficient P p n 0:ℂ))∧
      ∀g k J:ℕ,0<(complexity g p:ℝ)→(k:ℝ)/(complexity g p:ℝ)≤ν₀→
        WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k /
          ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)=
          poissonFamilyOperator (fun j=>originPoissonAmplitude P p j Bc L Z) J (complexity g p:ℝ) k/
            poissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) 0 ((((k:ℝ)/(complexity g p:ℝ)):ℝ):ℂ)∧
        ∀K:ℕ,(K:ℝ)≤(complexity g p:ℝ)/2→K≤J→2*B*((J:ℝ)+1)^2≤(complexity g p:ℝ)→
          ‖WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k /
            ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)-
            ∑n∈Finset.range (K+1),((complexity g p:ℝ):ℂ)⁻¹^n*
              normalizedPoissonFamilyCoefficient (fun j=>originPoissonAmplitude P p j Bc L Z) n
                ((((k:ℝ)/(complexity g p:ℝ)):ℝ):ℂ)‖≤
            E*D^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1):=by
  obtain ⟨S,xco,Q,Z,Bc,R,ρ,A,hR,hρ,hρx,hA,hS,hS0,hSd,hSphys,hmatch,hxco,hQa,hZ,
    hx0,hxd,hQ0,hBc0,haxes,hphase,hfa,hfb,hHa,hHr,hterms⟩:=
      actual_origin_poisson_family_with_source_analytic P p Ω L C B hΩ hcover hC hB hLa hLr hLb
  let f:ℕ→ℂ × ℂ → ℂ:=fun j=>originPoissonAmplitude P p j Bc L Z
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
    filter_upwards[hmatch,hlead,Analysis.densitySaddle_tendsto_zero_right.eventually hSphys,
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with ν hm hl hsp hνR hν
    have hn:‖(ν:ℂ)‖<R:=by simpa only[Complex.norm_real,Real.norm_eq_abs,abs_of_pos hν] using hνR
    have hx:0<XR (densityY (2*ν)):=(Analysis.physicalDensitySaddle_spec ν hν).1.1
    refine ⟨by rw[hm];exact (hsp hx.le).1,?_,hl hν⟩
    rw[(haxes (ν:ℂ) hn).2.1 (by exact_mod_cast hν.ne'),hm]
    simp only[Complex.ofReal_div]
  obtain ⟨r,hr,hgoodr⟩:=Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hgood)
  let ν₀:ℝ:=min (νe/2) (r/2)
  have hν₀:0<ν₀:=lt_min (half_pos hνe) (half_pos hr)
  have hν₀e:ν₀<νe:=(min_le_left _ _).trans_lt (half_lt_self hνe)
  have hν₀r:ν₀<r:=(min_le_right _ _).trans_lt (half_lt_self hr)
  have hcoe0:∀n,normalizedPoissonFamilyCoefficient f n 0=(markedCoefficient P p n 0:ℂ):=by
    intro n
    rw[normalizedPoissonFamilyCoefficient_at_zero f hf0,hf0j]
  have hexact:∀g k J:ℕ,0<(complexity g p:ℝ)→(k:ℝ)/(complexity g p:ℝ)≤ν₀→
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
      exact hν.trans_lt (hν₀e.trans hνeR)
    have hfs:∀j,AnalyticAt ℂ (fun u=>f j (u,(ν:ℂ))) 0:=by
      intro j
      exact (hfa j (0,(ν:ℂ)) ⟨by simpa only[Metric.mem_ball,dist_zero_right,norm_zero] using hR,
        by simpa only[Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hν0] using
          hν.trans_lt (hν₀e.trans hνeR)⟩).comp (f:=fun u:ℂ=>(u,(ν:ℂ)))
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
    have hg:=hgoodr (show dist ν 0<r by rw[Real.dist_eq,sub_zero,abs_of_pos hνp];exact hν.trans_lt hν₀r) hν0 hνp
    exact originPoisson_exact_normalized_coefficient_positive P g p k J S Bc L f xco Q hh hk hc hg.1 hg.2.1 hg.2.2
  refine ⟨S,Bc,Z,R,ν₀,ρ,A,E,D,hR,hν₀,hν₀e.trans hνeR,hρ,hA,hE,hD,hS,hS0,hSd,hBc0,?_,hHa,hHr,hfa',hfb',?_,hcoe0,?_⟩
  · filter_upwards[hSphys] with t ht ht0
    exact (ht ht0).1
  · intro n
    refine ⟨(hcoefs n).1.mono (Metric.ball_subset_ball hν₀e.le),?_⟩
    intro ν hν
    exact (hcoefs n).2 ν (hν.trans hν₀e)
  · intro g k J hh hν
    refine ⟨hexact g k J hh hν,?_⟩
    intro K hK hKJ hw
    rw[hexact g k J hh hν]
    exact herror (complexity g p:ℝ) k K J hh (hν.trans hν₀e.le) hK hKJ hw
end WP.HigherOrder
