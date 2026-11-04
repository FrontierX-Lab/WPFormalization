import WPFormalization.Analysis.AnalyticGevreyMatching
import WPFormalization.Analysis.CoefficientScaling
import WPFormalization.HigherOrder.PureEndpoint
import Mathlib
/-! The actual finite marking insertion factor has precisely the canonical
formal endpoint Taylor series. The binomial identity is obtained from
Mathlib's convergent complex binomial series, and finite rational products
are matched by proved Taylor algebra. A fixed analytic Cauchy circle then
yields simultaneous growing-order Gevrey bounds for every fixed marking count,
as well as the remaining linear inverse factor in the exact endpoint formula.
No Painlevé coefficient interpolation or asymptotic identification is assumed. -/
noncomputable section
namespace WP.Analysis
open PowerSeries Filter Set
open scoped Topology

lemma endpointInsertion_taylor_rescale (f:ℂ→ℂ)(c:ℂ) :
    taylor (fun z=>f (c*z))=PowerSeries.rescale c (taylor f) := by
  ext n
  simp only [taylor_coeff,PowerSeries.coeff_rescale,WP.coeff,
    iteratedDeriv_comp_mul_left,mul_zero,mul_div_assoc]

lemma endpointInsertion_taylor_binomial :
    taylor (fun z:ℂ=>(1+z)^(1/2:ℂ))=
      PowerSeries.map Complex.ofRealHom (HigherOrder.binomial (1/2)) := by
  have hc := Complex.one_add_cpow_hasFPowerSeriesAt_zero (a:=(1/2:ℂ))
  have he := hc.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hc
  change FormalMultilinearSeries.ofScalars ℂ
    (fun n=>iteratedDeriv n (fun z:ℂ=>(1+z)^(1/2:ℂ)) 0/(n.factorial:ℂ))=
      FormalMultilinearSeries.ofScalars ℂ (Ring.choose (1/2:ℂ) ·) at he
  simp only [FormalMultilinearSeries.ofScalars_series_eq_iff] at he
  ext n
  have hn := congrFun he n
  simpa [taylor_coeff,WP.coeff,HigherOrder.binomial,PowerSeries.binomialSeries_coeff,
    Complex.ofReal_choose] using hn

lemma endpointInsertion_taylor_sqrt_linear (p:ℕ) :
    taylor (fun z:ℂ=>(1+(p:ℂ)*z)^(1/2:ℂ))=
      PowerSeries.map Complex.ofRealHom
        (PowerSeries.rescale (p:ℝ) (HigherOrder.binomial (1/2))) := by
  change taylor (fun z:ℂ=>(fun w:ℂ=>(1+w)^(1/2:ℂ)) ((p:ℂ)*z))=_
  rw [endpointInsertion_taylor_rescale (fun w:ℂ=>(1+w)^(1/2:ℂ)) (p:ℂ),endpointInsertion_taylor_binomial]
  ext n
  simp [PowerSeries.coeff_rescale]

lemma endpointInsertion_taylor_linear (c:ℝ) :
    taylor (fun z:ℂ=>1+(c:ℂ)*z)=1+PowerSeries.C (c:ℂ)*PowerSeries.X := by
  rw [taylor_add (f:=fun _:ℂ=>1) (g:=fun z:ℂ=>(c:ℂ)*z)
    analyticAt_const (analyticAt_const.mul analyticAt_id),taylor_const_mul]
  simp

lemma endpointInsertion_taylor_prod {ι:Type*} (S:Finset ι)(f:ι→ℂ→ℂ)
    (hf:∀i∈S,AnalyticAt ℂ (f i) 0) :
    taylor (fun z=>∏i∈S,f i z)=∏i∈S,taylor (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hs:∀j∈S,AnalyticAt ℂ (f j) 0 := by intro j hj;exact hf j (Finset.mem_insert_of_mem hj)
    simp only [Finset.prod_insert hi]
    rw [taylor_mul (hf i (Finset.mem_insert_self _ _)) (by exact S.analyticAt_fun_prod hs),ih hs]

def endpointInsertionComplex (p:ℕ)(z:ℂ):ℂ :=
  (1+(p:ℂ)*z)^(1/2:ℂ)*
    ∏i∈Finset.range p,(1+((4*(i:ℝ)/5:ℝ):ℂ)*z)*(1+(i:ℂ)*z)⁻¹

lemma endpointInsertionComplex_analytic (p:ℕ) :
    AnalyticAt ℂ (endpointInsertionComplex p) 0 := by
  have hs : AnalyticAt ℂ (fun z:ℂ=>(1+(p:ℂ)*z)^(1/2:ℂ)) 0 :=
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const (by simp)
  have hp : AnalyticAt ℂ (fun z:ℂ=>∏i∈Finset.range p,
      (1+((4*(i:ℝ)/5:ℝ):ℂ)*z)*(1+(i:ℂ)*z)⁻¹) 0 := by
    apply Finset.analyticAt_fun_prod
    intro i hi
    exact (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).mul
      ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).inv (by simp))
  exact hs.mul hp

lemma endpointInsertionComplex_taylor (p:ℕ) :
    taylor (endpointInsertionComplex p)=
      PowerSeries.map Complex.ofRealHom (HigherOrder.endpointInsertion p) := by
  have hs : AnalyticAt ℂ (fun z:ℂ=>(1+(p:ℂ)*z)^(1/2:ℂ)) 0 :=
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).cpow analyticAt_const (by simp)
  have hl (c:ℝ):AnalyticAt ℂ (fun z:ℂ=>1+(c:ℂ)*z) 0 :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hf (i:ℕ):AnalyticAt ℂ (fun z:ℂ=>(1+((4*(i:ℝ)/5:ℝ):ℂ)*z)*(1+(i:ℂ)*z)⁻¹) 0 :=
    (hl _).mul ((hl _).inv (by simp))
  unfold endpointInsertionComplex
  rw [taylor_mul hs ((Finset.range p).analyticAt_fun_prod (fun i hi=>hf i)),
    endpointInsertion_taylor_sqrt_linear,endpointInsertion_taylor_prod _ _ (fun i hi=>hf i)]
  rw [HigherOrder.endpointInsertion,map_mul,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hiLin : taylor (fun z:ℂ=>1+(i:ℂ)*z)=1+PowerSeries.C (i:ℂ)*PowerSeries.X := by
    simpa using endpointInsertion_taylor_linear (i:ℝ)
  rw [taylor_mul (f:=fun z:ℂ=>1+((4*(i:ℝ)/5:ℝ):ℂ)*z)
    (g:=fun z:ℂ=>(1+(i:ℂ)*z)⁻¹) (hl _) ((hl _).inv (by simp)),
    taylor_inv (f:=fun z:ℂ=>1+(i:ℂ)*z) (hl _) (by simp),
    endpointInsertion_taylor_linear,hiLin,map_mul,
    map_inv_ofReal _ (by simp)]
  simp

lemma endpointInsertionComplex_inverse_real (p:ℕ)(h:ℝ)(hh:0<h) :
    endpointInsertionComplex p ((1/h:ℝ):ℂ)=(HigherOrder.endpointInsertionFactor h p:ℂ) := by
  have hs:(1+(p:ℂ)*((1/h:ℝ):ℂ))^(1/2:ℂ)=
      (Real.sqrt (1+(p:ℝ)/h):ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow (by positivity)]
    congr 1 <;> push_cast <;> ring
  unfold endpointInsertionComplex HigherOrder.endpointInsertionFactor
  rw [hs]
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma linearInverseFactor_gevrey (c:ℝ) :
    GevreyOneAsymptotic (fun h:ℝ=>(1+c/h)⁻¹)
      ((1+PowerSeries.C c*PowerSeries.X)⁻¹) := by
  have ha:AnalyticAt ℂ (fun z:ℂ=>1+(c:ℂ)*z) 0 :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  apply GevreyOneAsymptotic.of_analytic_at_zero _ _ (fun z:ℂ=>(1+(c:ℂ)*z)⁻¹)
    (ha.inv (by simp))
  · rw [taylor_inv ha (by simp),endpointInsertion_taylor_linear c,map_inv_ofReal _ (by simp)]
    simp
  · intro h hh
    push_cast
    congr 1
    ring

end WP.Analysis

namespace WP.HigherOrder

lemma endpointInsertionFactor_gevrey (p:ℕ) :
    Analysis.GevreyOneAsymptotic (fun h:ℝ=>endpointInsertionFactor h p) (endpointInsertion p) := by
  exact Analysis.GevreyOneAsymptotic.of_analytic_at_zero _ _ (Analysis.endpointInsertionComplex p)
    (Analysis.endpointInsertionComplex_analytic p) (Analysis.endpointInsertionComplex_taylor p)
    (fun h hh=>Analysis.endpointInsertionComplex_inverse_real p h hh)

end WP.HigherOrder
