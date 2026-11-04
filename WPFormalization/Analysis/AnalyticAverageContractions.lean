import Mathlib
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology ENNReal
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
lemma analyticAt_interval_average_contractions (g:E→F) (hg:AnalyticAt ℂ g 0)
    (A:ℝ→E→L[ℂ]E) (hA:Continuous A) (hcon:∀t∈Icc (0:ℝ) 1,‖A t‖≤1):
    AnalyticAt ℂ (fun v:E=>∫t:ℝ in (0)..1,g (A t v)) 0:=by
  obtain ⟨p,r,hp⟩:=hg
  let q:FormalMultilinearSeries ℂ E F:=fun n=>
    ∫t:ℝ in (0)..1,(p n).compContinuousLinearMap (fun _:Fin n=>A t)
  have hc(n:ℕ):Continuous (fun t:ℝ=>(p n).compContinuousLinearMap (fun _:Fin n=>A t)):=by
    exact ((p n).compContinuousLinearMapLRight).cont.comp (continuous_pi (fun _=>hA))
  have hcomp(n:ℕ) (t:ℝ) (ht:t∈Icc (0:ℝ) 1):
      ‖(p n).compContinuousLinearMap (fun _:Fin n=>A t)‖≤‖p n‖:=by
    have hh:(∏i:Fin n,‖A t‖)≤(1:ℝ):=by
      calc
        _ ≤ ∏i:Fin n,(1:ℝ):=Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun _ _=>hcon t ht)
        _ = 1:=by simp
    exact ((p n).norm_compContinuousLinearMap_le _).trans
      ((mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_one _))
  have hdom {t:ℝ} (ht:t∈Set.uIoc (0:ℝ) 1):t∈Icc (0:ℝ) 1:=by
    have hh:t∈Ioc (0:ℝ) 1:=by simpa only[uIoc_of_le (by norm_num : (0:ℝ)≤1)] using ht
    exact ⟨hh.1.le,hh.2⟩
  have hq(n:ℕ):‖q n‖≤‖p n‖:=by
    have hh:=intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=0) (b:=1) (C:=‖p n‖) (f:=fun t:ℝ=>(p n).compContinuousLinearMap (fun _:Fin n=>A t))
      (fun t ht=>hcomp n t (hdom ht))
    simpa only[sub_zero,abs_one,mul_one,q] using hh
  have hrad:r≤q.radius:=hp.r_le.trans (FormalMultilinearSeries.radius_le_of_le hq)
  refine ⟨q,r,hrad,hp.r_pos,?_⟩
  intro v hv
  have hv':(‖v‖₊:ℝ≥0∞)<r:=by simpa only[mem_eball_zero_iff,enorm_eq_nnnorm] using hv
  have hs:Summable (fun n:ℕ=>‖p n‖*‖v‖^n):=
    p.summable_norm_mul_pow (r:=‖v‖₊) (hv'.trans_le hp.r_le)
  have hcoef(n:ℕ):(q n) (fun _:Fin n=>v)=
      ∫t:ℝ in (0)..1,(p n) (fun _:Fin n=>A t v):=by
    have hh:=(ContinuousMultilinearMap.apply ℂ (fun _:Fin n=>E) F (fun _=>v)).intervalIntegral_comp_comm (μ:=volume)
      ((hc n).intervalIntegrable 0 1)
    simpa only[ContinuousMultilinearMap.apply_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply,q] using hh.symm
  have hbound(n:ℕ) (t:ℝ) (ht:t∈Icc (0:ℝ) 1):
      ‖(p n) (fun _:Fin n=>A t v)‖≤‖p n‖*‖v‖^n:=by
    have hh:=((p n).compContinuousLinearMap (fun _:Fin n=>A t)).le_opNorm (fun _=>v)
    simp only[ContinuousMultilinearMap.compContinuousLinearMap_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hcomp n t ht) (pow_nonneg (norm_nonneg _) _))
  have hAt(t:ℝ) (ht:t∈Icc (0:ℝ) 1):A t v∈Metric.eball (0:E) r:=by
    have hn:‖A t v‖≤‖v‖:=by
      exact ((A t).le_opNorm v).trans ((mul_le_mul_of_nonneg_right (hcon t ht) (norm_nonneg _)).trans_eq (one_mul _))
    rw[mem_eball_zero_iff,enorm_eq_nnnorm]
    exact (show (‖A t v‖₊:ℝ≥0∞)≤‖v‖₊ from by exact_mod_cast hn).trans_lt hv'
  have hsum:=intervalIntegral.hasSum_integral_of_dominated_convergence (μ:=volume) (a:=0) (b:=1)
    (F:=fun n (t:ℝ)=>(p n) (fun _:Fin n=>A t v)) (f:=fun t:ℝ=>g (A t v))
    (fun n (_:ℝ)=>‖p n‖*‖v‖^n)
    (fun n=>((p n).cont.comp (continuous_pi (fun _=>hA.clm_apply continuous_const))).aestronglyMeasurable)
    (fun n=>Filter.Eventually.of_forall (fun t ht=>hbound n t
      (hdom ht)))
    (Filter.Eventually.of_forall (fun t ht=>hs)) (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun t ht=>by
      have hh:=hp.hasSum (hAt t
        (hdom ht))
      simpa only[zero_add] using hh))
  simpa only[zero_add,hcoef] using hsum
end WP.Analysis
