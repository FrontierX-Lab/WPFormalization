import WPFormalization.HigherOrder.PoissonCentralExpansionProof
import WPFormalization.Statements.PoissonDefinitions
noncomputable section
namespace WP.HigherOrder
open PowerSeries
lemma centralCoefficient_eq_polynomial (m j : ℕ) :
    WP.centralCoefficient m j=(poissonCentralInverseCoefficient m j:ℂ) := by
  let a : ℕ := m-j
  have hl : AnalyticAt ℂ (fun z : ℂ=>Complex.log (1+z)-z) 0 := by
    have hp : (fun z : ℂ=>1+z) 0∈Complex.slitPlane := by simp
    exact ((analyticAt_clog hp).comp (analyticAt_const.add analyticAt_id)).sub analyticAt_id
  have hc : WP.coeff (fun z : ℂ=>(Complex.log (1+z)-z)^a) m=
      ((PowerSeries.coeff m (poissonCentralLog^a):ℝ):ℂ) := by
    rw [←Analysis.taylor_coeff,Analysis.taylor_pow hl,
      poissonCentralLog_complex_taylor,←map_pow,PowerSeries.coeff_map]
    rfl
  have hformula : (poissonCentralPolynomial m).coeff a=
      if a ≤ m/2 then (m.factorial:ℝ)*PowerSeries.coeff m (poissonCentralLog^a)/(a.factorial:ℝ) else 0 := by
    simp only [poissonCentralPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
      Finset.sum_ite_eq',Finset.mem_range,Nat.lt_succ_iff]
  change (m.factorial:ℂ)*WP.coeff (fun z : ℂ=>(Complex.log (1+z)-z)^a) m/(a.factorial:ℂ)=
    ((poissonCentralPolynomial m).coeff a:ℂ)
  rw [hc,hformula]
  split_ifs with ha
  · push_cast
    rfl
  · rw [poissonCentralLog_pow_coeff_zero m a (by omega)]
    simp

lemma poissonCorrection_eq_amplitude (f : ℂ × ℂ → ℂ) (j : ℕ) (ν : ℂ) :
    WP.poissonCorrection f j ν=poissonCentralAmplitude f j ν := by
  by_cases hj : j=0
  · subst j
    simp [WP.poissonCorrection]
  · rw [WP.poissonCorrection,poissonCentralAmplitude,ite_eq_right hj,ite_eq_right hj]
    apply Finset.sum_congr rfl
    intro m hm
    rw [centralCoefficient_eq_polynomial,WP.coeff]
    have he := congrFun (iteratedDeriv_comp_const_add m (fun u : ℂ=>f (u,ν)) ν) 0
    simp only [add_zero] at he
    rw [he]
    ring

lemma poissonOperator_eq_actual (f : ℂ × ℂ → ℂ) (h k : ℕ) :
    WP.poissonOperator f h k=poissonCoefficientOperator (h:ℝ) k (fun u=>f (u,(k:ℂ)/(h:ℂ))) := by
  simp only [WP.poissonOperator,poissonCoefficientOperator,Complex.ofReal_natCast]

end WP.HigherOrder
namespace WP
open HigherOrder
lemma poisson_central_expansion_original_proof (R : ℝ) (hR : 0 < R) (f : ℂ × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R ×ˢ Metric.ball 0 R))
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) R ×ˢ Metric.ball (0 : ℂ) R, ‖f z‖ ≤ 1) :
    ∃ ν₀ ρ C : ℝ, 0 < ν₀ ∧ 0 < ρ ∧ 0 < C ∧
      (∀ h k K : ℕ, 1 ≤ h → (k : ℝ)/h ≤ ν₀ → 2*K ≤ h →
        ‖poissonOperator f h k -
          ∑ j ∈ Finset.range (K+1), (h : ℂ)⁻¹^j * poissonCorrection f j ((k : ℂ)/h)‖ ≤
          C^(K+1)*(K+1).factorial/(h : ℝ)^(K+1)) ∧
      (∀ j : ℕ, AnalyticOnNhd ℂ (poissonCorrection f j) (Metric.ball 0 ρ) ∧
        ∀ ν : ℂ, ‖ν‖ < ρ → ‖poissonCorrection f j ν‖ ≤ C^(j+1)*j.factorial) ∧
      (∀ j : ℕ, 1 ≤ j → poissonCorrection f j 0 = 0) ∧
      (∀ h k : ℕ, 1 ≤ h → (k : ℝ)/h ≤ ν₀ → ‖poissonOperator f h k‖ ≤ C) := by
  have he : Metric.ball (0:ℂ × ℂ) R=Metric.ball (0:ℂ) R ×ˢ Metric.ball (0:ℂ) R := by
    ext p
    simp only [Metric.mem_ball,dist_zero_right,Prod.norm_def,Set.mem_prod,max_lt_iff]
  obtain ⟨ν₀,C,hν₀,hνR,hC,herror,han,hcoef,hzero,hop⟩ :=
    poisson_central_expansion_proof f R hR (by rwa [he]) (by rwa [he])
  have heq (j : ℕ) : poissonCorrection f j=poissonCentralAmplitude f j := funext (poissonCorrection_eq_amplitude f j)
  refine ⟨ν₀,ν₀,C,hν₀,hν₀,hC,?_,?_,?_,?_⟩
  · intro h k K hh hν hK
    have hhp : 0 < (h:ℝ) := by exact_mod_cast (show 0<h by omega)
    have hKr : (K:ℝ) ≤ (h:ℝ)/2 := by
      have ht : (2:ℝ)*(K:ℝ) ≤ (h:ℝ) := by exact_mod_cast hK
      linarith
    have ht := herror (h:ℝ) k K hhp hν hKr
    simp only [Complex.ofReal_div,Complex.ofReal_natCast] at ht
    simpa only [poissonOperator_eq_actual,heq,div_eq_mul_inv,inv_pow,mul_comm] using ht
  · intro j
    rw [heq]
    exact ⟨han j,hcoef j⟩
  · intro j hj
    rw [heq]
    exact hzero j hj
  · intro h k hh hν
    have hhp : 0 < (h:ℝ) := by exact_mod_cast (show 0<h by omega)
    have ht := hop (h:ℝ) k hhp hν
    simpa only [poissonOperator_eq_actual,Complex.ofReal_div,Complex.ofReal_natCast] using ht
end WP
