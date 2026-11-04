import WPFormalization.Analysis.GevreyOneSequence
import WPFormalization.Analysis.GammaRatioGevrey
import WPFormalization.HigherOrder.PainleveEndpointGevrey
import WPFormalization.HigherOrder.EndpointInsertionMatching
/-! Actual fixed-marking endpoint Gevrey-one expansions. The exact endpoint
factorization is combined with the proved numerical zero-instanton expansion,
the actual Gamma-ratio expansion and genuine finite insertion factors. All
products, the complexity shift and the logarithm are propagated along the
natural-number genus sequence; no real interpolation of that sequence is
assumed. The canonical endpointSeries and endpointLogCoefficient are retained. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology
private lemma endpointBaseScale_tendsto:
    Tendsto (fun g:ℕ=>((2*g-2:ℕ):ℝ)) atTop atTop:=by
  have ht:Tendsto (fun g:ℕ=>2*g-2) atTop atTop:=by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b+2)] with g hg
    omega
  exact tendsto_natCast_atTop_atTop.comp ht

private lemma complexityScale_tendsto (p:ℕ):
    Tendsto (fun g:ℕ=>(complexity g p:ℝ)) atTop atTop:=by
  have ht:Tendsto (fun g:ℕ=>complexity g p) atTop atTop:=by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b+2)] with g hg
    dsimp[complexity]
    omega
  exact tendsto_natCast_atTop_atTop.comp ht

lemma normalizedZeroInstanton_gevrey_one_sequence:
    Analysis.GevreyOneSequence (fun g:ℕ=>((2*g-2:ℕ):ℝ)) External.normalizedZeroInstanton endpointZ:=by
  obtain ⟨C,B,hC,hB,he⟩:=normalizedZeroInstanton_endpointZ_expansion
  refine ⟨C,B,1/16,4,hC,hB,by norm_num,?_⟩
  intro g hg
  have hgR:(4:ℝ)≤g:=by exact_mod_cast hg
  have hscale:((2*g-2:ℕ):ℝ)=2*(g:ℝ)-2:=by
    rw[Nat.cast_sub (by omega:2≤2*g)]
    push_cast
    ring
  have hp:0<((2*g-2:ℕ):ℝ):=by rw[hscale];linarith
  refine ⟨hp,?_⟩
  intro K hK
  have hK':(K:ℝ)≤(g:ℝ)/8:=by
    change (K:ℝ)≤(1/16)*((2*g-2:ℕ):ℝ) at hK
    rw[hscale] at hK
    linarith
  simpa only[Analysis.inversePowerTruncation,div_eq_mul_inv,inv_pow] using he g hg K hK'

lemma exactEndpoint_gevrey_one_sequence_at_base (P:PsiTheory)(p:ℕ):
    Analysis.GevreyOneSequence (fun g:ℕ=>((2*g-2:ℕ):ℝ)) (fun g=>exactEndpoint P g p) (endpointAtH₀ p):=by
  let scale:ℕ→ℝ:=fun g=>((2*g-2:ℕ):ℝ)
  have hs:Tendsto scale atTop atTop:=endpointBaseScale_tendsto
  have hΓ:Analysis.GevreyOneAsymptotic
      (fun h:ℝ=>Real.Gamma (h+3/2)/(Real.Gamma h*h^(3/2:ℝ))) (gammaRatioSeries (3/2)):=by
    have he:((3/2:ℚ):ℝ)=(3/2:ℝ):=by norm_num
    simpa only[Analysis.GevreyOneAsymptotic,Analysis.inversePowerTruncation,he] using
      Analysis.gammaRatio_uniform_gevrey_error (3/2:ℚ) (by norm_num)
  have hΓs:=Analysis.GevreyOneSequence.of_real scale hs _ _ hΓ
  have hIs:=Analysis.GevreyOneSequence.of_real scale hs _ _ (endpointInsertionFactor_gevrey p)
  have hLs:=Analysis.GevreyOneSequence.of_real scale hs _ _ (Analysis.linearInverseFactor_gevrey (4/5:ℝ))
  have hZ:Analysis.GevreyOneSequence scale External.normalizedZeroInstanton endpointZ:=normalizedZeroInstanton_gevrey_one_sequence
  have h₁:=Analysis.GevreyOneSequence.mul scale _ _ hs _ _ hZ hΓs
  have h₂:=Analysis.GevreyOneSequence.mul scale _ _ hs _ _ h₁ hIs
  have h₃:=Analysis.GevreyOneSequence.mul scale _ _ hs _ _ h₂ hLs
  change Analysis.GevreyOneSequence scale
    (fun g=>External.normalizedZeroInstanton g*
      (Real.Gamma (scale g+3/2)/(Real.Gamma (scale g)*(scale g)^(3/2:ℝ)))*
      endpointInsertionFactor (scale g) p*(1+(4/5:ℝ)/(scale g))⁻¹) (endpointAtH₀ p) at h₃
  apply Analysis.GevreyOneSequence.congr scale _ _ (endpointAtH₀ p) h₃
  filter_upwards [eventually_ge_atTop 2] with g hg
  rw[exactEndpoint_formula P g p hg]
  dsimp[scale]
  simp only[div_eq_mul_inv,mul_inv_rev]
  ring

lemma exactEndpoint_gevrey_one_sequence (P:PsiTheory)(p:ℕ):
    Analysis.GevreyOneSequence (fun g=>(complexity g p:ℝ)) (fun g=>exactEndpoint P g p) (endpointSeries p):=by
  have he:=Analysis.GevreyOneSequence.shift (fun g:ℕ=>((2*g-2:ℕ):ℝ)) _ endpointBaseScale_tendsto
    (endpointAtH₀ p) (exactEndpoint_gevrey_one_sequence_at_base P p) (p:ℝ)
  change Analysis.GevreyOneSequence (fun g:ℕ=>((2*g-2:ℕ):ℝ)+(p:ℝ)) (fun g=>exactEndpoint P g p) (endpointSeries p) at he
  apply Analysis.GevreyOneSequence.congr_scale _ _ _ _ he
  filter_upwards [eventually_ge_atTop 2] with g hg
  have heq:2*g+p-2=(2*g-2)+p:=by omega
  rw[complexity,heq,Nat.cast_add]

lemma exactEndpointLog_gevrey_one_sequence (P:PsiTheory)(p:ℕ):
    Analysis.GevreyOneSequence (fun g=>(complexity g p:ℝ)) (fun g=>Real.log (exactEndpoint P g p))
      (finiteLog (endpointSeries p)):=by
  exact Analysis.GevreyOneSequence.log_unit _ _ (complexityScale_tendsto p) _
    (exactEndpoint_gevrey_one_sequence P p) (endpointSeries_constant p)

lemma exactEndpoint_uniform_gevrey_error (P:PsiTheory)(p:ℕ):
    ∃(C B c:ℝ)(G:ℕ),0<C ∧ 0<B ∧ 0<c ∧ ∀g:ℕ,G≤g→∀K:ℕ,
      (K:ℝ)≤c*(complexity g p:ℝ)→
      |exactEndpoint P g p-∑j∈Finset.range (K+1),PowerSeries.coeff j (endpointSeries p)/(complexity g p:ℝ)^j|≤
        C*B^(K+1)*((K+1).factorial:ℝ)/(complexity g p:ℝ)^(K+1):=by
  obtain ⟨C,B,c,G,hC,hB,hc,he⟩:=exactEndpoint_gevrey_one_sequence P p
  exact ⟨C,B,c,G,hC,hB,hc,fun g hg K hK=>(he g hg).2 K hK⟩

lemma exactEndpoint_log_uniform_gevrey_error (P:PsiTheory)(p:ℕ):
    ∃(C B c:ℝ)(G:ℕ),0<C ∧ 0<B ∧ 0<c ∧ ∀g:ℕ,G≤g→∀K:ℕ,
      (K:ℝ)≤c*(complexity g p:ℝ)→
      |Real.log (exactEndpoint P g p)-∑j∈Finset.range (K+1),endpointLogCoefficient p j/(complexity g p:ℝ)^j|≤
        C*B^(K+1)*((K+1).factorial:ℝ)/(complexity g p:ℝ)^(K+1):=by
  obtain ⟨C,B,c,G,hC,hB,hc,he⟩:=exactEndpointLog_gevrey_one_sequence P p
  exact ⟨C,B,c,G,hC,hB,hc,fun g hg K hK=>(he g hg).2 K hK⟩

end WP.HigherOrder
