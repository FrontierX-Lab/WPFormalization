import WPFormalization.HigherOrder.PoissonCentralUniform
import WPFormalization.Analysis.CoefficientSubstitution
noncomputable section
namespace WP.HigherOrder
open scoped Topology
lemma poissonCentralAmplitude_const_mul (c:ℂ) (f:ℂ × ℂ → ℂ) (j:ℕ) (ν:ℂ):
    poissonCentralAmplitude (fun v=>c*f v) j ν=c*poissonCentralAmplitude f j ν:=by
  by_cases hj:j=0
  · subst j;simp
  · simp only[poissonCentralAmplitude,if_neg hj,Analysis.coeff_const_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
lemma poissonCentralAmplitude_scale_cancel (M:ℝ) (hM:0<M) (f:ℂ × ℂ → ℂ) (j:ℕ):
    poissonCentralAmplitude f j=(fun ν:ℂ=>(M:ℂ)*poissonCentralAmplitude (fun v=>(M:ℂ)⁻¹*f v) j ν):=by
  funext ν
  rw[poissonCentralAmplitude_const_mul]
  have hn:(M:ℂ)≠0:=by exact_mod_cast hM.ne'
  field_simp
lemma poissonCentralRemainder_const_mul (c:ℂ) (f:ℂ × ℂ → ℂ)
    (h:ℝ) (k K:ℕ):
    poissonCoefficientOperator h k (fun u=>c*f (u,(((k:ℝ)/h:ℝ):ℂ)))-
      ∑j∈Finset.range (K+1),poissonCentralAmplitude (fun v=>c*f v) j (((k:ℝ)/h:ℝ):ℂ)/(h:ℂ)^j=
    c*(poissonCoefficientOperator h k (fun u=>f (u,(((k:ℝ)/h:ℝ):ℂ)))-
      ∑j∈Finset.range (K+1),poissonCentralAmplitude f j (((k:ℝ)/h:ℝ):ℂ)/(h:ℂ)^j):=by
  rw[poissonCoefficientOperator_const_mul,mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw[poissonCentralAmplitude_const_mul]
  ring
lemma poisson_central_expansion_uniform_homogeneous (R:ℝ) (hR:0<R):
  ∃ν₀ C:ℝ,0<ν₀∧ν₀<R∧0<C∧∀(f:ℂ × ℂ → ℂ)(M:ℝ),0<M→
    AnalyticOnNhd ℂ f (Metric.ball 0 R)→
    (∀p∈Metric.ball (0:ℂ × ℂ) R,‖f p‖≤M)→
    (∀(h:ℝ)(k K:ℕ),0<h→(k:ℝ)/h≤ν₀→(K:ℝ)≤h/2→
      ‖poissonCoefficientOperator h k (fun u=>f (u,(((k:ℝ)/h:ℝ):ℂ)))-
        ∑j∈Finset.range (K+1),poissonCentralAmplitude f j (((k:ℝ)/h:ℝ):ℂ)/(h:ℂ)^j‖≤
      M*C^(K+1)*((K+1).factorial:ℝ)/h^(K+1))∧
    (∀j,AnalyticOnNhd ℂ (poissonCentralAmplitude f j) (Metric.ball 0 ν₀))∧
    (∀j ν,‖ν‖<ν₀→‖poissonCentralAmplitude f j ν‖≤M*C^(j+1)*(j.factorial:ℝ))∧
    (∀(h:ℝ)(k:ℕ),0<h→(k:ℝ)/h≤ν₀→
      ‖poissonCoefficientOperator h k (fun u=>f (u,(((k:ℝ)/h:ℝ):ℂ)))‖≤M*C):=by
  obtain ⟨ν₀,C,hν₀,hνR,hC,hall⟩:=poisson_central_expansion_uniform R hR
  refine ⟨ν₀,C,hν₀,hνR,hC,?_⟩
  intro f M hM hf hb
  let g:ℂ × ℂ → ℂ:=fun v=>(M:ℂ)⁻¹*f v
  have hg:AnalyticOnNhd ℂ g (Metric.ball 0 R):=fun v hv=>analyticAt_const.mul (hf v hv)
  have hgb:∀v∈Metric.ball (0:ℂ × ℂ) R,‖g v‖≤1:=by
    intro v hv
    calc
      _=‖f v‖/M:=by simp only[g,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM,div_eq_mul_inv,mul_comm]
      _≤1:=(div_le_one hM).mpr (hb v hv)
  obtain ⟨herr,hga,htb,hzero,hop⟩:=hall g hg hgb
  have hscale(j:ℕ):poissonCentralAmplitude f j=(fun ν:ℂ=>(M:ℂ)*poissonCentralAmplitude g j ν):=
    poissonCentralAmplitude_scale_cancel M hM f j
  refine ⟨?_,?_,?_,?_⟩
  · intro h k K hh hν hK
    have he:=herr h k K hh hν hK
    change ‖poissonCoefficientOperator h k (fun u=>(M:ℂ)⁻¹*f (u,(((k:ℝ)/h:ℝ):ℂ)))-
      ∑j∈Finset.range (K+1),poissonCentralAmplitude (fun v=>(M:ℂ)⁻¹*f v) j (((k:ℝ)/h:ℝ):ℂ)/(h:ℂ)^j‖≤_ at he
    rw[poissonCentralRemainder_const_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM] at he
    calc
      _=M*(M⁻¹*‖poissonCoefficientOperator h k (fun u=>f (u,(((k:ℝ)/h:ℝ):ℂ)))-
          ∑j∈Finset.range (K+1),poissonCentralAmplitude f j (((k:ℝ)/h:ℝ):ℂ)/(h:ℂ)^j‖):=by field_simp
      _≤M*(C^(K+1)*((K+1).factorial:ℝ)/h^(K+1)):=mul_le_mul_of_nonneg_left he hM.le
      _=_:=by ring
  · intro j
    rw[hscale j]
    exact fun ν hν=>analyticAt_const.mul (hga j ν hν)
  · intro j ν hν
    rw[hscale j,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
    simpa only[mul_assoc] using mul_le_mul_of_nonneg_left (htb j ν hν) hM.le
  · intro h k hh hν
    have he:=hop h k hh hν
    change ‖poissonCoefficientOperator h k (fun u=>(M:ℂ)⁻¹*f (u,(((k:ℝ)/h:ℝ):ℂ)))‖≤C at he
    rw[poissonCoefficientOperator_const_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM] at he
    calc
      _=M*(M⁻¹*‖poissonCoefficientOperator h k (fun u=>f (u,(((k:ℝ)/h:ℝ):ℂ)))‖):=by field_simp
      _≤M*C:=mul_le_mul_of_nonneg_left he hM.le
end WP.HigherOrder
