import WPFormalization.Analysis.HarmonicCentral
/-! Normalization, positivity, parameter continuity, and finite uniform lower
bounds for the actual harmonic sum probabilities, including the closed
parameter interval. All constants come from the analytic kernels. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology

lemma harmonicSumMass_hasSum (Y:ℝ)(hY:Y∈Icc 0 y₀)(h:ℕ):
    HasSum (harmonicSumMass Y h) 1 := by
  obtain ⟨η,hη,hzero⟩:=barH_uniform_zero_free
  have hf:=((harmonicPGF_diffOn hη hzero Y hY).mono Metric.ball_subset_closedBall).pow h
  have hs:=hasSum_coeff_on_ball (fun w=>harmonicPGF Y w^h) (1+η) hf 1 (by norm_num;linarith)
  rw[harmonicPGF_one Y hY,one_pow] at hs
  convert Complex.hasSum_re hs using 1
  · ext n
    rw[one_pow,mul_one]
    rfl

lemma harmonicSumMass_pos (Y:ℝ)(hY:Y∈Icc 0 y₀)(h m:ℕ)(hh:0<h):
    0<harmonicSumMass Y h m := by
  rw[harmonicSumMass_eq_normalized_coeff Y hY h m]
  exact mul_pos (pow_pos (barH_one_re_pos Y hY) h) (harmonicCoeff_pos Y h m hh hY)

lemma harmonicSumMass_continuous (h m:ℕ):
    Continuous (fun Y:Icc (0:ℝ) y₀=>harmonicSumMass (Y:ℝ) h m) := by
  obtain ⟨η,hη,hzero⟩:=barH_uniform_zero_free
  have hc:=parameter_coeff_continuous (fun Y:Icc (0:ℝ) y₀=>fun w:ℂ=>harmonicPGF (Y:ℝ) w^h)
    (1+η) (by linarith) (fun Y=>(harmonicPGF_diffOn hη hzero Y Y.property).pow h)
    ((harmonicPGF_joint_closed hη hzero).pow h) m
  exact Complex.continuous_re.comp hc

lemma harmonicSumMass_fixed_lower (h m:ℕ)(hh:0<h):
    ∃c:ℝ,0<c ∧∀Y∈Icc (0:ℝ) y₀,c≤harmonicSumMass Y h m := by
  let S:=Icc (0:ℝ) y₀
  have hS:(univ:Set S).Nonempty:=⟨⟨0,le_rfl,y₀_pos.le⟩,mem_univ _⟩
  obtain ⟨Ymin,_,hmin⟩:=isCompact_univ.exists_isMinOn
    (f:=fun Y:S=>harmonicSumMass (Y:ℝ) h m) hS (harmonicSumMass_continuous h m).continuousOn
  refine ⟨harmonicSumMass (Ymin:ℝ) h m,harmonicSumMass_pos Ymin Ymin.property h m hh,?_⟩
  intro Y hY
  exact (isMinOn_iff.mp hmin) (⟨Y,hY⟩:S) (mem_univ _)

lemma harmonicSumMass_finite_lower (H M:ℕ)(hH:1≤H):
    ∃c:ℝ,0<c ∧∀h:ℕ,1≤h→h≤H→∀m:ℕ,m≤M→∀Y∈Icc (0:ℝ) y₀,c≤harmonicSumMass Y h m := by
  classical
  haveI:NeZero H:=⟨by omega⟩
  have hpoint (i:Fin H × Fin (M+1)):
      ∃c:ℝ,0<c ∧∀Y∈Icc (0:ℝ) y₀,c≤harmonicSumMass Y ((i.1:ℕ)+1) i.2 :=
    harmonicSumMass_fixed_lower _ _ (by omega)
  choose c hc hcle using hpoint
  let cmin:ℝ:=Finset.univ.inf' Finset.univ_nonempty c
  have hcmin:0<cmin:=by
    dsimp[cmin]
    rw[Finset.lt_inf'_iff]
    exact fun i _=>hc i
  refine ⟨cmin,hcmin,?_⟩
  intro h hh hhle m hm Y hY
  let i:Fin H × Fin (M+1):=(⟨h-1,by omega⟩,⟨m,by omega⟩)
  have hi:(i.1:ℕ)+1=h:=by dsimp[i];omega
  have hm':(i.2:ℕ)=m:=rfl
  have hLower:=hcle i Y hY
  rw[hi,hm'] at hLower
  exact (Finset.inf'_le c (Finset.mem_univ i)).trans hLower

lemma barH_one_re_le_one (Y:ℝ)(hY:Y∈Icc 0 y₀):(barH Y 1).re≤1 := by
  have hs:=harmonicMass_hasSum Y hY
  have ht:=hs.summable.le_tsum 0 (fun n _=>(harmonicMass_pos Y hY n).le)
  rw[hs.tsum_eq] at ht
  simpa only [harmonicMass,realCoeff,WP.coeff,iteratedDeriv_zero,Nat.factorial_zero,
    Nat.cast_one,div_one,harmonicPGF,barH_zero Y hY] using ht
end WP.Analysis
