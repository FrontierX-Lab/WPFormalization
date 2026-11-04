import WPFormalization.Volumes.OriginRawCircleExpansion
import WPFormalization.Analysis.PoissonGaussianNormalization
import WPFormalization.HigherOrder.FixedDensityPoissonSeries
import WPFormalization.HigherOrder.RawRecipeProduct
import WPFormalization.HigherOrder.PoissonFamilyNormalizedExpansion
/-! Fixed-density coefficient identification for a given common physical
source and its genuine D5/D6 data. The proof localizes the actual whole
Cauchy coefficient, compares both expansions along h=n/nu, and cancels the
original Poisson Stirling unit. The final common-source existence producer
must instantiate the explicitly listed D5 coefficient, leading-diagonal and
D6 bounds; this helper does not assert that producer. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter MeasureTheory
open scoped Topology
lemma origin_poisson_raw_matching_core (P:PsiTheory)(p:ℕ)(hp:1≤p)(x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical)(hν:0<WP.Psi x)
    (S Bc:ℂ→ℂ)(Γ:ℕ→ℂ→ℂ)(ρ B D:ℝ)(hxρ:x<ρ)(hB:0<B)(hD:0<D)
    (hSa:AnalyticOnNhd ℂ S (Metric.closedBall 0 ρ))
    (hBca:AnalyticOnNhd ℂ Bc (Metric.closedBall 0 ρ))
    (hΓa:∀s,AnalyticOnNhd ℂ (Γ s) (Metric.closedBall 0 ρ))
    (hSr:(fun t:ℝ=>S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionS t:ℂ)))
    (hBcr:(fun t:ℝ=>Bc (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(extractionB p t:ℂ)))
    (hΓr:∀s,(fun t:ℝ=>Γ s (t:ℂ))=ᶠ[𝓝 x]
      (fun t:ℝ=>(markedCoefficient P p s (inverseY t):ℂ)))
    (hamp:∀s z,‖z‖≤ρ→‖Bc z*Γ s z‖≤D*B^s*(s.factorial:ℝ)^2)
    (hphase:∀θ:ℝ,(S ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-S (x:ℂ)).re≤-(x/2)*(1-Real.cos θ))
    (f:ℕ→ℂ × ℂ→ℂ)(ν0 Cp Dp:ℝ)(hCp:0<Cp)(hDp:0<Dp)(hν0:WP.Psi x≤ν0)
    (hE0:poissonFamilyCoefficient f 0 (WP.Psi x:ℂ)=Bc (x:ℂ)*Real.sqrt (WP.Psi x/WP.euler WP.Psi x))
    (hcoef:∀(h:ℝ)(k N:ℕ),0<h→h*WP.Psi x=(k:ℝ)→
      WP.coeff (phaseFamilyModel S (fun s z=>Bc z*Γ s z) h N) k=
        Complex.exp ((h:ℂ)*S (x:ℂ))*(x:ℂ)⁻¹^k*(WP.poissonCenter k:ℂ)*poissonFamilyOperator f N h k)
    (hpoisson:∀(h:ℝ)(k K J:ℕ),0<h→(k:ℝ)/h≤ν0→(K:ℝ)≤h/2→K≤J→2*B*((J:ℝ)+1)^2≤h→
      ‖poissonFamilyOperator f J h k/poissonFamilyCoefficient f 0 (((k:ℝ)/h:ℝ):ℂ)-
        ∑n∈Finset.range (K+1),(h:ℂ)⁻¹^n*normalizedPoissonFamilyCoefficient f n (((k:ℝ)/h:ℝ):ℂ)‖≤
        Cp*Dp^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)):
    ∀j:ℕ,normalizedPoissonFamilyCoefficient f j (WP.Psi x:ℂ)=
      ((PowerSeries.coeff (2*j) (extractionNumerator P p x*(extractionDenominator x)⁻¹):ℝ):ℂ):=by
  let ν:ℝ:=WP.Psi x
  let t:ℕ→ℝ:=fun n=>(n:ℝ)/ν
  have ht:Tendsto t atTop atTop:=Filter.Tendsto.atTop_div_const hν tendsto_natCast_atTop_atTop
  have htk(n:ℕ):t n*ν=(n:ℝ):=by dsimp[t];exact div_mul_cancel₀ _ hν.ne'
  have htn(n:ℕ)(hn:1≤n):0<t n:=div_pos (by exact_mod_cast (show 0<n by omega)) hν
  have hratio(n:ℕ)(hn:1≤n):(n:ℝ)/t n=ν:=by dsimp[t];field_simp
  have hBcne:Bc (x:ℂ)≠0:=by
    have hh:Bc (x:ℂ)=(extractionB p x:ℂ):=hBcr.self_of_nhds
    rw[hh]
    exact_mod_cast (WP.Analysis.extractionB_pos_interior p x ⟨hx.1.le,hx.2⟩).ne'
  have hv:0<WP.euler WP.Psi x:=mul_pos hx.1 (WP.Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  intro N
  let num:PowerSeries ℂ:=PowerSeries.mk (fun j=>((PowerSeries.coeff (2*j) (extractionNumerator P p x):ℝ):ℂ))
  let ap:PowerSeries ℂ:=PowerSeries.mk (fun j=>normalizedPoissonFamilyCoefficient f j (ν:ℂ))
  let den:PowerSeries ℂ:=PowerSeries.map Complex.ofRealHom (PowerSeries.rescale ν⁻¹ poissonStirlingSeries)
  let F:ℕ→ℂ:=fun n=>Complex.exp (-((t n:ℂ)*S (x:ℂ)))*(x:ℂ)^n*
    WP.coeff (phaseFamilyModel S (fun s z=>Bc z*Γ s z) (t n) N) n*
      (Real.sqrt (2*Real.pi*t n*WP.euler WP.Psi x):ℂ)/Bc (x:ℂ)
  let G:ℕ→ℂ:=fun n=>poissonFamilyOperator f N (t n) n/poissonFamilyCoefficient f 0 (ν:ℂ)
  let R:ℕ→ℂ:=fun n=>(WP.Analysis.poissonNormalizer n:ℂ)
  have hFG:∀ᶠn:ℕ in atTop,F n=G n*R n:=by
    filter_upwards[eventually_ge_atTop 1] with n hn
    exact WP.Analysis.poisson_gaussian_coefficient_normalization S
      (phaseFamilyModel S (fun s z=>Bc z*Γ s z) (t n) N) x (t n) ν (WP.euler WP.Psi x) n
      (Bc (x:ℂ)) (poissonFamilyOperator f N (t n) n) (poissonFamilyCoefficient f 0 (ν:ℂ))
      (htn n hn) hx.1 hν hv (htk n) hBcne hE0 (hcoef (t n) n N (htn n hn) (htk n))
  have hf:∀K≤N,∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<t n ∧
      ‖F n-truncationValue num (K+1) ((t n:ℂ)⁻¹)‖≤C/(t n)^(K+1):=by
    intro K hKN
    obtain ⟨C,H,hC,hH,he⟩:=WP.Analysis.raw_numerator_whole_circle_expansion_of_physical_source P p hp x hx S Bc Γ ρ B D
      hxρ hB hD hSa hBca hΓa hSr hBcr hΓr hamp hphase N K hKN
    refine ⟨C,hC,?_⟩
    filter_upwards[ht.eventually (eventually_ge_atTop H)] with n hn
    refine ⟨hH.trans_le hn,?_⟩
    have hs:truncationValue num (K+1) ((t n:ℂ)⁻¹)=
        ∑j∈Finset.range (K+1),((PowerSeries.coeff (2*j) (extractionNumerator P p x):ℝ):ℂ)/(t n:ℂ)^j:=by
      simp only[truncationValue,num,PowerSeries.coeff_mk,inv_pow,div_eq_mul_inv]
    rw[hs]
    exact he (t n) hn n (htk n)
  have hg:∀K≤N,∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<t n ∧
      ‖G n-truncationValue ap (K+1) ((t n:ℂ)⁻¹)‖≤C/(t n)^(K+1):=by
    intro K hKN
    refine ⟨Cp*Dp^(K+1)*((K+1).factorial:ℝ)^2,by positivity,?_⟩
    filter_upwards[ht.eventually (eventually_ge_atTop (max (2*(K:ℝ)) (2*B*((N:ℝ)+1)^2))),
      eventually_ge_atTop 1] with n hn hn1
    have hh:=htn n hn1
    have hk2:(K:ℝ)≤t n/2:=by have hd:=(le_max_left _ _).trans hn;linarith
    have hbgt:2*B*((N:ℝ)+1)^2≤t n:=(le_max_right _ _).trans hn
    have he:=hpoisson (t n) n K N hh (by rw[hratio n hn1];exact hν0) hk2 hKN hbgt
    rw[hratio n hn1] at he
    refine ⟨hh,?_⟩
    convert he using 1
    simp only[truncationValue,ap,G,PowerSeries.coeff_mk,mul_comm]
  have hr:∀K≤N,∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<t n ∧
      ‖R n-truncationValue den (K+1) ((t n:ℂ)⁻¹)‖≤C/(t n)^(K+1):=by
    have he:=poissonNormalizer_fixed_density_expansion ν hν N
    simpa only[t,R,den,←Complex.ofReal_div] using he
  have hprod:=finite_sequence_inverse_power_product G R t ap den N ht hg hr
  have hprodF:∀K≤N,∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,0<t n ∧
      ‖F n-truncationValue (ap*den) (K+1) ((t n:ℂ)⁻¹)‖≤C/(t n)^(K+1):=by
    intro K hKN
    obtain ⟨C,hC,he⟩:=hprod K hKN
    refine ⟨C,hC,?_⟩
    filter_upwards[he,hFG] with n hn heq
    rwa[←heq] at hn
  have hprefix:=finite_sequence_truncation_unique F t num (ap*den) N ht hf hprodF
  simpa only[ap,PowerSeries.coeff_mk] using (raw_recipe_of_poisson_product_prefix P p hp x hx ap N
    (fun j hj=>by simpa only[num,den,ν,PowerSeries.coeff_mk] using (hprefix j hj).symm) N le_rfl)
end WP.HigherOrder
