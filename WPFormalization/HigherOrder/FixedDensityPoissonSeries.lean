import WPFormalization.Analysis.PoissonNormalizer
import WPFormalization.HigherOrder.FiniteRemainderAlgebra
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology
lemma rescaled_real_series_truncation (f:PowerSeries ℝ)(ν h:ℝ)(k q:ℕ)(hk:h*ν=(k:ℝ)):
    truncationValue (PowerSeries.map Complex.ofRealHom (PowerSeries.rescale ν⁻¹ f)) q ((h:ℂ)⁻¹)=
      ∑j∈Finset.range q,((PowerSeries.coeff j f:ℝ):ℂ)/(k:ℂ)^j:=by
  unfold truncationValue
  apply Finset.sum_congr rfl
  intro j hj
  simp only[PowerSeries.coeff_map,PowerSeries.coeff_rescale]
  change (((ν⁻¹^j*PowerSeries.coeff j f:ℝ):ℂ))*(h:ℂ)⁻¹^j=_
  push_cast
  calc _=((PowerSeries.coeff j f:ℝ):ℂ)*(((ν:ℂ)⁻¹*(h:ℂ)⁻¹)^j):=by rw[mul_pow];ring
       _= _:=by rw[←mul_inv_rev,←Complex.ofReal_mul,hk,Complex.ofReal_natCast];ring
lemma poissonNormalizer_fixed_density_expansion (ν:ℝ)(hν:0<ν)(N:ℕ):
    ∀K≤N,∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<(n:ℝ)/ν ∧
      ‖(WP.Analysis.poissonNormalizer n:ℂ)-
        truncationValue (PowerSeries.map Complex.ofRealHom (PowerSeries.rescale ν⁻¹ poissonStirlingSeries))
          (K+1) (((n:ℝ)/ν:ℂ)⁻¹)‖≤C/((n:ℝ)/ν)^(K+1):=by
  have ht:Tendsto (fun n:ℕ=>(n:ℝ)/ν) atTop atTop:=
    Filter.Tendsto.atTop_div_const hν tendsto_natCast_atTop_atTop
  obtain ⟨C,B,c,H,hC,hB,hc,hH,he⟩:=WP.Analysis.poissonNormalizer_uniform_error ν hν
  intro K hKN
  refine ⟨C*B^(K+1)*((K+1).factorial:ℝ),by positivity,?_⟩
  filter_upwards[ht.eventually (eventually_ge_atTop (max H ((K:ℝ)/c)))] with n hn
  have hHn:H≤(n:ℝ)/ν:=(le_max_left _ _).trans hn
  have htn:0<(n:ℝ)/ν:=hH.trans_le hHn
  have hk:(n:ℝ)/ν*ν=(n:ℝ):=by field_simp
  have hnpos:0<(n:ℝ):=by rw[←hk];positivity
  have hn1:1≤n:=by exact_mod_cast (show 0<(n:ℝ) from hnpos)
  have hK:(K:ℝ)≤c*((n:ℝ)/ν):=(div_le_iff₀ hc).mp ((le_max_right _ _).trans hn) |>.trans_eq (mul_comm _ _)
  have he0:=he n K ((n:ℝ)/ν) hHn (by rw[mul_comm,hk]) hK
  refine ⟨htn,?_⟩
  rw[←Complex.ofReal_div]
  change ‖(WP.Analysis.poissonNormalizer n:ℂ)-
    truncationValue (PowerSeries.map Complex.ofRealHom (PowerSeries.rescale ν⁻¹ poissonStirlingSeries))
      (K+1) ((((n:ℝ)/ν:ℝ):ℂ)⁻¹)‖≤_
  rw[rescaled_real_series_truncation poissonStirlingSeries ν ((n:ℝ)/ν) n (K+1) hk]
  have hec:(WP.Analysis.poissonNormalizer n:ℂ)-
      (∑j∈Finset.range (K+1),((PowerSeries.coeff j poissonStirlingSeries:ℝ):ℂ)/(n:ℂ)^j)=
      ((Real.sqrt (2*Real.pi*n)*WP.poissonCenter n-
        ∑j∈Finset.range (K+1),PowerSeries.coeff j poissonStirlingSeries/(n:ℝ)^j:ℝ):ℂ):=by
    rw[WP.Analysis.poissonNormalizer_nat n hn1]
    push_cast
    rfl
  rw[hec,Complex.norm_real,Real.norm_eq_abs]
  exact he0
end WP.HigherOrder
