import WPFormalization.Analysis.AnalyticImplicitScalar
noncomputable section
namespace WP.Analysis
open Filter
open scoped Topology

def poissonEtaEquation (x Q:ℂ → ℂ) (D:ℂ × ℂ → ℂ) (L:ℂ → ℂ)
    (p:(ℂ × ℂ) × ℂ):ℂ:=
  D p.1-p.2+p.1.2*(p.2/Q p.1.2)^2*L ((p.1.1-x p.1.2)*p.2/Q p.1.2)
lemma exists_poisson_phase_eta (x Q:ℂ → ℂ) (D:ℂ × ℂ → ℂ) (L:ℂ → ℂ)
    (hx:AnalyticAt ℂ x 0) (hQ:AnalyticAt ℂ Q 0) (hD:AnalyticAt ℂ D 0) (hL:AnalyticAt ℂ L 0)
    (hx0:x 0=0) (hQne:Q 0≠0):
    ∃η:ℂ × ℂ → ℂ,AnalyticAt ℂ η 0∧η 0=D 0∧
      ∀ᶠv:ℂ × ℂ in 𝓝 0,
        D v-η v+v.2*(η v/Q v.2)^2*L ((v.1-x v.2)*η v/Q v.2)=0:=by
  let p0:(ℂ × ℂ) × ℂ:=(0,D 0)
  let Eqt:=poissonEtaEquation x Q D L
  let a:((ℂ × ℂ) × ℂ) → ℂ:=fun p=>p.1.2
  let z:((ℂ × ℂ) × ℂ) → ℂ:=fun p=>p.1.1
  let b:((ℂ × ℂ) × ℂ) → ℂ:=fun p=>p.2
  have ha:AnalyticAt ℂ a p0:=by
    have hh:AnalyticAt ℂ (fun q:ℂ × ℂ=>q.2) p0.1:=analyticAt_snd
    exact hh.comp (f:=fun p:(ℂ × ℂ) × ℂ=>p.1) analyticAt_fst
  have hz:AnalyticAt ℂ z p0:=by
    have hh:AnalyticAt ℂ (fun q:ℂ × ℂ=>q.1) p0.1:=analyticAt_fst
    exact hh.comp (f:=fun p:(ℂ × ℂ) × ℂ=>p.1) analyticAt_fst
  have hb:AnalyticAt ℂ b p0:=analyticAt_snd
  have hxA:AnalyticAt ℂ (fun p=>x (a p)) p0:=hx.comp (f:=a) ha
  have hQA:AnalyticAt ℂ (fun p=>Q (a p)) p0:=hQ.comp (f:=a) ha
  have hDfst:AnalyticAt ℂ (fun p:(ℂ × ℂ) × ℂ=>D p.1) p0:=
    hD.comp (f:=fun p:(ℂ × ℂ) × ℂ=>p.1) analyticAt_fst
  have hQAne:Q (a p0)≠0:=hQne
  have hratio:AnalyticAt ℂ (fun p=>b p/Q (a p)) p0:=hb.div hQA hQAne
  let arg:((ℂ × ℂ) × ℂ) → ℂ:=fun p=>(z p-x (a p))*b p/Q (a p)
  have harg:AnalyticAt ℂ arg p0:=((hz.sub hxA).mul hb).div hQA hQAne
  have harg0:arg p0=0:=by simp[arg,p0,z,a,b,hx0]
  have hLa:AnalyticAt ℂ (fun p=>L (arg p)) p0:=by
    have hh:AnalyticAt ℂ L (arg p0):=by rw[harg0];exact hL
    exact hh.comp (f:=arg) harg
  have hE:AnalyticAt ℂ Eqt p0:=by
    exact (hDfst.sub hb).add ((ha.mul (hratio.pow 2)).mul hLa)
  have hE0:Eqt p0=0:=by simp[Eqt,poissonEtaEquation,p0]
  have hslice:(fun y:ℂ=>Eqt ((0:ℂ × ℂ),y))=(fun y:ℂ=>D 0-y):=by
    funext y
    simp[Eqt,poissonEtaEquation]
  have hd:HasDerivAt (fun y:ℂ=>Eqt ((0:ℂ × ℂ),y)) (-1) (D 0):=by
    rw[hslice]
    convert! (hasDerivAt_const (D 0) (D 0)).sub (hasDerivAt_id (D 0)) using 1 <;>
      simp only[Pi.sub_apply,id_eq,zero_sub]
  have hc:HasDerivAt (fun y:ℂ=>((0:ℂ × ℂ),y)) ((0,1):(ℂ × ℂ) × ℂ) (D 0):=
    (hasDerivAt_const (D 0) (0:ℂ × ℂ)).prodMk (hasDerivAt_id (D 0))
  have hh:HasDerivAt (fun y:ℂ=>Eqt ((0:ℂ × ℂ),y))
      (fderiv ℂ Eqt p0 ((0,1):(ℂ × ℂ) × ℂ)) (D 0):=by
    simpa only[Function.comp_def] using hE.differentiableAt.hasFDerivAt.comp_hasDerivAt (D 0) hc
  have he:fderiv ℂ Eqt p0 ((0,1):(ℂ × ℂ) × ℂ)=(-1:ℂ):=hh.unique hd
  have hInv:(fderiv ℂ Eqt p0 ∘L ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ).IsInvertible:=by
    apply complex_clm_isInvertible_of_apply_one_ne_zero
    change fderiv ℂ Eqt p0 ((0,1):(ℂ × ℂ) × ℂ)≠0
    rw[he]
    norm_num
  obtain ⟨η,hη,hη0,hηE,huniq,hder⟩:=exists_analytic_implicit_scalar Eqt p0 hE hInv
  refine ⟨η,hη,hη0,?_⟩
  filter_upwards[hηE] with v hv
  rw[hE0] at hv
  exact hv
end WP.Analysis
