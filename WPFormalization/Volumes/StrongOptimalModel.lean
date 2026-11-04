import WPFormalization.Volumes.OriginModelCircleBound
import WPFormalization.Volumes.FixedOptimalModel
/-! A single proved actual optimal-model choice with all source data.
The canonical family, kappa, budget and order J are fixed once. The same
actual phase and amplitude supply their common analytic neighborhood,
Euler normalization, all-order amplitudes, tiny-disk true-generating-function
comparison, and full-circle FINITE-model decay. The final P-only producer
supplies every ordinary source hypothesis from existing proved results;
it does not assume any missing uniform extraction or central comparison. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma fixed_origin_models_of_strong_source
    (P:PsiTheory) (p:ℕ) (hp:1≤p)
    (Ω:Set ℂ) (L:ℕ→ℂ→ℂ) (C B κ a H₀:ℝ)
    (hΩ:IsOpen Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C) (hB:0<B) (hκ:0<κ) (ha:0<a) (hH₀:0<H₀)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hL0:∀z,L 0 z=1)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2)
    (hmodel: ∀g:ℕ,H₀≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        (∀z∈Ω,‖finiteMarkedFactor L h J z-1‖≤2*C*B/h ∧
          1/2≤‖finiteMarkedFactor L h J z‖ ∧
          ‖finiteMarkedFactor L h J z‖≤2 ∧ finiteMarkedFactor L h J z≠0) ∧
        (∀Y∈Icc (0:ℝ) y₀,
          finiteMarkedFactor L h J (Y:ℂ)=(realFiniteMarkedFactor P p h J Y:ℂ)) ∧
        (∀Y∈Ico (0:ℝ) y₀,
          |(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
            realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h)))
    (S Bc:ℂ→ℂ)(ρ Cs:ℝ)(hρ:0<ρ)(hρx:ρ<xCritical)(hCs:0<Cs)
    (hSbound:∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ S z ∧ ‖S z‖≤Cs*‖z‖)
    (hlocal:∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ Bc z ∧ ‖Bc z‖≤2 ∧ PositiveConvolution.planarInverse P z∈Ω)
    (hSphys:∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ))
    (hBphys:∀x∈Icc (0:ℝ) ρ,Bc (x:ℂ)=(extractionB p x:ℂ)):
    ∃H D E:ℝ,H₀≤H ∧ 0<H ∧ 0<D ∧ 0<E ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        (∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z ∧
          ‖normalizedFiniteMarkedModel P g p S Bc L J z‖≤D*Real.exp (D*h*‖z‖)) ∧
        (∀x∈Icc (0:ℝ) ρ,normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)≠0 ∧
          ‖normalizedMarkedGenerating P g p (x:ℂ)/normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)-1‖≤
            E*Real.exp (-a*Real.sqrt h)):=by
  let D:ℝ:=Cs+4
  let H:ℝ:=max H₀ 1
  have hD:0<D:=by dsimp[D];linarith
  have hH:0<H:=hH₀.trans_le (le_max_left _ _)
  refine ⟨H,D,2*C,le_max_left _ _,hH,hD,by positivity,?_⟩
  intro g hg
  dsimp only
  let h:ℝ:=complexity g p
  let J:=⌊κ*Real.sqrt h⌋₊
  have hh:0<h:=hH.trans_le hg
  have hg₀:H₀≤h:=(le_max_left _ _).trans hg
  have hh1:1≤h:=(le_max_right _ _).trans hg
  have hs:Stable g p:=by
    have hn:1≤complexity g p:=by exact_mod_cast (show (1:ℝ)≤(complexity g p:ℝ) from hh1)
    unfold Stable complexity at *;omega
  have hm:=hmodel g hg₀
  have hPana:=finiteMarkedFactor_analyticOnNhd Ω L h J hLa
  refine ⟨?_,?_⟩
  · intro z hz
    have hl:=hlocal z hz
    have hsbound:=hSbound z hz
    have hYca:=PositiveConvolution.planarInverse_analyticAt P z (hz.trans_lt hρx)
    have hPbound:‖finiteMarkedFactor L h J (PositiveConvolution.planarInverse P z)‖≤2:=
      (hm.1 _ hl.2.2).2.2.1
    have hAa:AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z:=
      ((analyticAt_const.mul hsbound.1).cexp.mul hl.1).mul ((hPana _ hl.2.2).comp hYca)
    refine ⟨hAa,?_⟩
    have hex:‖Complex.exp ((complexity g p:ℂ)*S z)‖≤Real.exp (D*h*‖z‖):=by
      apply (Complex.norm_exp_le_exp_norm _).trans
      apply Real.exp_le_exp.mpr
      rw[norm_mul,Complex.norm_natCast]
      have ht:=mul_le_mul_of_nonneg_left hsbound.2 (Nat.cast_nonneg (complexity g p): (0:ℝ)≤complexity g p)
      have hd:Cs≤D:=by dsimp[D];linarith
      have ht':Cs*‖z‖≤D*‖z‖:=mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      nlinarith[mul_le_mul_of_nonneg_left ht' hh.le]
    unfold normalizedFiniteMarkedModel
    rw[norm_mul,norm_mul]
    have hprod:=mul_le_mul (mul_le_mul hex hl.2.1 (norm_nonneg _) (Real.exp_pos _).le)
      hPbound (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (by norm_num:(0:ℝ)≤2))
    have hd4:(4:ℝ)≤D:=by dsimp[D];linarith
    have ht:=mul_le_mul_of_nonneg_right hd4 (Real.exp_pos (D*h*‖z‖)).le
    nlinarith
  · intro x hx
    have hxi:x∈Ico (0:ℝ) xCritical:=⟨hx.1,hx.2.trans_lt hρx⟩
    have hy:=(inverseY_branch x hxi).1
    have hyc:inverseY x∈Icc (0:ℝ) y₀:=⟨hy.1,hy.2.le⟩
    have hPL:=hm.2.1 _ hyc
    have hPne:realFiniteMarkedFactor P p h J (inverseY x)≠0:=by
      intro he
      have hnonzero:finiteMarkedFactor L h J (inverseY x:ℂ)≠0:=(hm.1 _ (hcover _ hyc)).2.2.2
      apply hnonzero
      rw[hPL,he,Complex.ofReal_zero]
    have hbval: Bc (x:ℂ)=(extractionB p x:ℂ):=hBphys x hx
    have hmreal:=normalizedFiniteMarkedModel_real P g p hs S Bc L J x hxi (hSphys x hx) hbval hPL
    have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hs 0 ⟨le_rfl,y₀_pos⟩).ne'
    have hMY:markedModel g p (inverseY x)≠0:=(markedModel_pos_parameter g p hs _ hy).ne'
    refine ⟨?_,?_⟩
    · rw[hmreal]
      exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (div_ne_zero hMY hM0) hPne)
    · rw[normalized_model_real_relative_error_identity P g p hs S Bc L J x hxi (hSphys x hx) hbval hPL hPne]
      have ht:=hm.2.2 (inverseY x) hy
      simpa only[(inverseY_branch x hxi).2] using ht
end WP.HigherOrder
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma actual_strong_optimal_origin_model_data (P:PsiTheory)(p:ℕ)(hp:1≤p):
    ∃(Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B κ a H:ℝ)(S Bc:ℂ→ℂ)(ρ D Cs d Csmall DM E:ℝ),
      IsOpen Ω ∧ (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      0<C ∧ 0<B ∧ 0<κ ∧ 0<a ∧ 0<H ∧ 0<ρ ∧ ρ<xCritical ∧
      0<D ∧ 0<Cs ∧ 0<d ∧ 0<Csmall ∧ 0<DM ∧ 0<E ∧
      (∀j,AnalyticOnNhd ℂ (L j) Ω) ∧ (∀z,L 0 z=1) ∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(markedCoefficient P p j Y:ℂ)) ∧
      (∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2) ∧
      AnalyticAt ℂ S 0 ∧ S 0=0 ∧ deriv S 0=2 ∧ Bc 0=1 ∧
      (∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ) ∧
        (x:ℂ)*deriv S (x:ℂ)=(WP.Psi x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      (∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ S z ∧ ‖S z‖≤Cs*‖z‖ ∧
        AnalyticAt ℂ Bc z ∧ ‖Bc z-1‖≤1/2 ∧ PositiveConvolution.planarInverse P z∈Ω) ∧
      (∀j,AnalyticOnNhd ℂ (originMarkedAmplitude P p j Bc L) (Metric.ball 0 ρ)) ∧
      (∀j z,‖z‖≤ρ→‖originMarkedAmplitude P p j Bc L z‖≤D*B^j*(j.factorial:ℝ)^2) ∧
      (∀x∈Ioo (0:ℝ) ρ,∀θ:ℝ,
        (S ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-S (x:ℂ)).re≤-(x/2)*(1-Real.cos θ)) ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        2*B*((J:ℝ)+1)^2≤h ∧
        (∀z∈Ω,‖finiteMarkedFactor L h J z-1‖≤2*C*B/h ∧
          1/2≤‖finiteMarkedFactor L h J z‖ ∧
          ‖finiteMarkedFactor L h J z‖≤2 ∧ finiteMarkedFactor L h J z≠0) ∧
        (∀Y∈Ico (0:ℝ) y₀,|(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
          realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h)) ∧
        (∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z ∧
          ‖normalizedFiniteMarkedModel P g p S Bc L J z‖≤DM*Real.exp (DM*h*‖z‖)) ∧
        (∀x∈Icc (0:ℝ) ρ,normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)≠0 ∧
          ‖normalizedMarkedGenerating P g p (x:ℂ)/normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)-1‖≤
            E*Real.exp (-a*Real.sqrt h)) ∧
        (∀z:ℂ,‖z‖≤d/(4*Real.sqrt h)→
          ‖normalizedMarkedGenerating P g p z-normalizedFiniteMarkedModel P g p S Bc L J z‖≤
            Csmall*Real.exp (-(a/4)*Real.sqrt h)) ∧
        (∀x∈Ioo (0:ℝ) ρ,∀θ:ℝ,
          ‖normalizedFiniteMarkedModel P g p S Bc L J ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/
            normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)‖≤
              8*D*Real.exp (-(h*x/2)*(1-Real.cos θ))):=by
  obtain ⟨Ω,L,C,B,κ,a,H0,hΩ,hcover,hC,hB,hκ,ha,hH0,hLa,hL0,hLr,hLb,hmodels⟩:=
    optimal_marked_model_real_comparison_with_budget P p hp
  have hmodel:∀g:ℕ,H0≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        (∀z∈Ω,‖finiteMarkedFactor L h J z-1‖≤2*C*B/h ∧
          1/2≤‖finiteMarkedFactor L h J z‖ ∧
          ‖finiteMarkedFactor L h J z‖≤2 ∧ finiteMarkedFactor L h J z≠0) ∧
        (∀Y∈Icc (0:ℝ) y₀,finiteMarkedFactor L h J (Y:ℂ)=(realFiniteMarkedFactor P p h J Y:ℂ)) ∧
        (∀Y∈Ico (0:ℝ) y₀,|(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
          realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h)):=by
    intro g hg
    exact (hmodels g hg).2
  obtain ⟨S,Bc,ρ,D,Cs,hρ,hρx,hD,hCs,hSa,hS0,hSd,hBc0,htrace,hlocal,hAa,hAb,hcircle⟩:=
    strong_origin_source_of_parameter_data P p Ω L C B hΩ hcover hC hB hLa hLr hLb
  have hSloc:∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ S z ∧ ‖S z‖≤Cs*‖z‖:=by
    intro z hz
    exact ⟨(hlocal z hz).1,(hlocal z hz).2.1⟩
  have hBloc:∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ Bc z ∧ ‖Bc z‖≤2 ∧ PositiveConvolution.planarInverse P z∈Ω:=by
    intro z hz
    have ht:=hlocal z hz
    exact ⟨ht.2.2.1,(Analysis.near_one_norm_bounds _ ht.2.2.2.1).2.1,ht.2.2.2.2⟩
  obtain ⟨H1,DM,E,hH01,hH1,hDM,hE,hdata⟩:=
    fixed_origin_models_of_strong_source P p hp Ω L C B κ a H0 hΩ hcover hC hB hκ ha hH0
      hLa hL0 hLr hLb hmodel S Bc ρ Cs hρ hρx hCs hSloc hBloc
      (fun x hx=>(htrace x hx).1) (fun x hx=>(htrace x hx).2.2)
  let d:ℝ:=min (ρ/18) (a/(36*DM))
  have hd:0<d:=lt_min (by positivity) (by positivity)
  have hdr:d≤ρ/18:=min_le_left _ _
  have hda:36*DM*d≤a:=by
    have ht:=(le_div_iff₀ (by positivity:0<36*DM)).mp (min_le_right (ρ/18) (a/(36*DM)))
    dsimp only[d]
    nlinarith
  let H:ℝ:=max H1 1
  have hH:0<H:=hH1.trans_le (le_max_left _ _)
  refine ⟨Ω,L,C,B,κ,a,H,S,Bc,ρ,D,Cs,d,(E+2)*DM,DM,E,hΩ,hcover,hC,hB,hκ,ha,hH,
    hρ,hρx,hD,hCs,hd,by positivity,hDM,hE,hLa,hL0,hLr,hLb,hSa,hS0,hSd,hBc0,
    htrace,hlocal,hAa,hAb,hcircle,?_⟩
  intro g hg
  let h:ℝ:=complexity g p
  let J:=⌊κ*Real.sqrt h⌋₊
  have hg1:H1≤h:=(le_max_left _ _).trans hg
  have hg0:H0≤h:=hH01.trans hg1
  have hh1:1≤h:=(le_max_right _ _).trans hg
  have hh:0<h:=lt_of_lt_of_le zero_lt_one hh1
  have hm:=hdata g hg1
  have ho:=hmodel g hg0
  have hs:Stable g p:=by
    have hn:1≤complexity g p:=by exact_mod_cast (show (1:ℝ)≤(complexity g p:ℝ) from hh1)
    unfold Stable complexity at *
    omega
  refine ⟨(hmodels g hg0).1,ho.1,ho.2.2,hm.1,hm.2,?_,?_⟩
  · intro z hz
    have hM:AnalyticOnNhd ℂ (normalizedFiniteMarkedModel P g p S Bc L J) (Metric.ball 0 ρ):=by
      intro w hw
      exact (hm.1 w (show ‖w‖≤ρ from (by simpa only[Metric.mem_ball,dist_zero_right] using hw : ‖w‖<ρ).le)).1
    exact Analysis.small_disk_comparison_of_real_relative_error
      (normalizedMarkedGenerating P g p) (normalizedFiniteMarkedModel P g p S Bc L J)
      ρ DM E a d h hρ hDM hE ha hd hdr hda hh1
      (normalizedMarkedGenerating_analytic_disk P g p ρ hρx.le) hM
      (fun w hw=>(hm.1 w hw).2)
      (fun w hw=>normalizedMarkedGenerating_disk_domination P g p hp hs ‖w‖ ⟨norm_nonneg _,hw.trans_lt hρx⟩ w le_rfl)
      hm.2 z hz
  · intro x hx θ
    have hnx:‖(x:ℂ)‖≤ρ:=by rw[Complex.norm_of_nonneg hx.1.le];exact hx.2.le
    have ht:=hlocal (x:ℂ) hnx
    have hP:=((ho.1 _ ht.2.2.2.2).2.1)
    exact (origin_model_circle_decay_at P g p J S Bc L B D ρ x hB hD hx hh
      (hmodels g hg0).1 hAb ht.2.2.2.1 hP (hcircle x hx)).2 θ
end WP.HigherOrder
