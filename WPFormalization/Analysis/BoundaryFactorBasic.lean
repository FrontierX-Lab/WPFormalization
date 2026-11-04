import WPFormalization.Statements.Parameter
noncomputable section
namespace WP.Analysis
open Set MeasureTheory
lemma I₀_continuous : Continuous I₀:=by
  have hD:Continuous (deriv X):=by
    rw[continuous_iff_continuousAt]
    intro z
    exact (X_differentiable.analyticAt z).deriv.continuousAt
  have he:I₀=(fun z:ℂ=>deriv X (-(z/2)^2)):=funext I₀_eq_derivX
  rw[he]
  exact hD.comp (by fun_prop)
lemma one_le_I₀_real (x:ℝ):1≤(I₀ (x:ℂ)).re:=by
  rw[I₀_eq_derivX]
  have he:-((x:ℂ)/2)^2=Complex.ofReal (-(x/2)^2):=by push_cast;ring
  rw[he]
  exact a_one_le_of_nonpos _ (neg_nonpos.mpr (sq_nonneg _))
end WP.Analysis
namespace WP
open Set MeasureTheory
lemma boundary_integrand_continuous (Y L:ℝ):
    Continuous (fun s:ℝ=>(I₀ (Complex.ofReal (L/Real.pi*Real.sqrt (T Y-Delta Y*s^2)))).re):=by
  apply Complex.continuous_re.comp
  apply Analysis.I₀_continuous.comp
  exact Complex.continuous_ofReal.comp (by fun_prop)
lemma one_le_boundaryFactor (Y L:ℝ):1≤boundaryFactor Y L:=by
  have hi:=intervalIntegral.integral_mono_on (μ:=volume) (by norm_num:(0:ℝ)≤1)
    (intervalIntegrable_const (c:=(1:ℝ))) ((boundary_integrand_continuous Y L).intervalIntegrable _ _)
    (fun s hs=>Analysis.one_le_I₀_real _)
  simpa only[intervalIntegral.integral_const,sub_zero,smul_eq_mul,one_mul,boundaryFactor,Complex.ofReal_mul,Complex.ofReal_div] using hi
lemma boundaryFactor_pos (Y L:ℝ):0<boundaryFactor Y L:=zero_lt_one.trans_le (one_le_boundaryFactor Y L)
end WP
namespace WP
open Set Filter MeasureTheory
open scoped Topology
lemma T_continuousOn_closed : ContinuousOn T (Icc 0 y₀):=by
  intro Y hY
  by_cases he:Y=y₀
  · subst Y
    have hT:T y₀=y₀:=by simp[T]
    have hi:ContinuousWithinAt T (Iio y₀) y₀:=by
      change Tendsto T (𝓝[<] y₀) (𝓝 (T y₀))
      rw[hT]
      exact T_tendsto_critical
    have hh:=hi.insert
    rw[Iio_insert] at hh
    exact hh.mono (fun _ h=>h.2)
  · exact (Analysis.T_analyticAt_interior Y ⟨hY.1,lt_of_le_of_ne hY.2 he⟩).continuousAt.continuousWithinAt
lemma boundaryFactor_joint_continuous :
    Continuous (fun p:(Icc (0:ℝ) y₀)×ℝ=>boundaryFactor (p.1:ℝ) p.2):=by
  have hT:Continuous (fun Y:Icc (0:ℝ) y₀=>T (Y:ℝ)):=
    continuousOn_iff_continuous_restrict.mp T_continuousOn_closed
  have hc:Continuous (fun q:((Icc (0:ℝ) y₀)×ℝ)×ℝ=>
      (I₀ (Complex.ofReal (q.1.2/Real.pi*Real.sqrt
        (T (q.1.1:ℝ)-(T (q.1.1:ℝ)-(q.1.1:ℝ))*q.2^2)))).re):=by
    apply Complex.continuous_re.comp
    apply Analysis.I₀_continuous.comp
    apply Complex.continuous_ofReal.comp
    apply Continuous.mul
    · fun_prop
    · apply Real.continuous_sqrt.comp
      apply Continuous.sub
      · exact hT.comp (continuous_fst.comp continuous_fst)
      · apply Continuous.mul
        · exact (hT.comp (continuous_fst.comp continuous_fst)).sub
            (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
        · fun_prop
  have hi:=intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ:=volume) (f:=fun (p:(Icc (0:ℝ) y₀)×ℝ) (s:ℝ)=>
      (I₀ (Complex.ofReal (p.2/Real.pi*Real.sqrt
        (T (p.1:ℝ)-(T (p.1:ℝ)-(p.1:ℝ))*s^2)))).re) hc 0 1
  simpa only[Function.uncurry_def,boundaryFactor,Delta,Complex.ofReal_mul,Complex.ofReal_div] using hi
lemma boundaryFactor_uniform_compact_bound (L0:ℝ):
    ∃B:ℝ,0<B∧∀Y∈Icc 0 y₀,∀L∈Icc 0 L0,boundaryFactor Y L≤B:=by
  have hs:IsCompact ((univ:Set (Icc (0:ℝ) y₀))×ˢIcc (0:ℝ) L0):=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨B,hB⟩:=hs.exists_bound_of_continuousOn boundaryFactor_joint_continuous.continuousOn
  refine ⟨max 1 B,zero_lt_one.trans_le (le_max_left _ _),?_⟩
  intro Y hY L hL
  exact (le_abs_self _).trans ((hB (⟨Y,hY⟩,L) ⟨mem_univ _,hL⟩).trans (le_max_right _ _))
end WP
namespace WP.Analysis
lemma I₀_zero_value:I₀ (0:ℂ)=1:=by rw[I₀_eq_derivX];simpa using derivX_zero
end WP.Analysis
namespace WP
lemma boundaryFactor_zero_length (Y:ℝ):boundaryFactor Y 0=1:=by
  simp[boundaryFactor,Analysis.I₀_zero_value]
end WP
