import WPFormalization.Volumes.CriticalActualModelComparison
import WPFormalization.Volumes.CriticalRawGaussianUniform
import WPFormalization.Analysis.ExponentialToGevreyTwo
import WPFormalization.HigherOrder.OptimalMarkedBudget
/-! Actual uniform canonical extraction in the critical sector. The unchanged
raw CG3 coefficients approximate the original coefficient divided by the
original extractionQ. The common constants precede g,k,K and the physical
parameter. The final P-only theorem supplies all finite-model comparison
data from the genuine proved optimal model; no new asymptotic premise is
retained. The original extractedCoefficient interior branch is included. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
open Set Filter
open scoped Topology
set_option maxHeartbeats 2000000 in
lemma CriticalGaussianCoordinateData.actual_critical_raw_expansion_of_parameter_data
    (d:CriticalGaussianCoordinateData)(P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(f:ℕ→ℂ→ℂ)(C B κ a H0:ℝ)
    (hΩ:IsOpen Ω)(hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C)(hB:0<B)(hκ:0<κ)(ha:0<a)(hH0:0<H0)
    (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hrest:∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hbound:∀j z,z∈Ω→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2)
    (hmodels:∀g:ℕ,H0≤(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      2*B*((J:ℝ)+1)^2≤h ∧
      (∀z∈Ω,‖HigherOrder.finiteMarkedFactor f h J z-1‖≤2*C*B/h ∧
        1/2≤‖HigherOrder.finiteMarkedFactor f h J z‖ ∧
        ‖HigherOrder.finiteMarkedFactor f h J z‖≤2 ∧ HigherOrder.finiteMarkedFactor f h J z≠0) ∧
      (∀Y∈Icc (0:ℝ) y₀,HigherOrder.finiteMarkedFactor f h J (Y:ℂ)=(HigherOrder.realFiniteMarkedFactor P p h J Y:ℂ)) ∧
      (∀Y∈Ico (0:ℝ) y₀,|(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
        HigherOrder.realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h))) :
    ∃R Ce Be c H:ℝ,0<R ∧ R<y₀ ∧ 0<Ce ∧ 0<Be ∧ 0<c ∧ 0<H ∧
      ∀g k K:ℕ,H≤(complexity g p:ℝ)→(K:ℝ)≤c*Real.sqrt (complexity g p:ℝ)→
      ∀δ∈Ioo (0:ℝ) R,(k:ℝ)=(complexity g p:ℝ)*WP.Psi (XR (y₀-δ))→
      |realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k-
        ∑j∈Finset.range (K+1),HigherOrder.rawExtractedCoefficient P p j (y₀-δ)/(complexity g p:ℝ)^j|≤
      Ce*Be^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1) := by
  obtain ⟨Q,hQ,hQ0,hQphys,hcaps⟩:=d.actual_critical_coefficient_model_comparison P p hp Ω f C B κ a H0
    hΩ hcover hC hB hκ ha hH0 hf hrest hbound hmodels
  obtain ⟨Rr,ρ,Ar,Er,hRr,hRry,hρ,hAr,hEr,hraw⟩:=
    d.original_raw_uniform_gaussian_gevrey_two_all_cutoffs P p hp Q Ω f C B
      hQ hQ0 hQphys hΩ hcover hC hB hf hrest hbound
  obtain ⟨R,τ,Cm,bm,Hm,hR,hRRr,hRy,hτ,hτρ,hCm,hbm,hHm,hactual⟩:=hcaps Rr ρ hRr hρ
  obtain ⟨cr,br,Hr,hcr,hbr,hHr,hrawerr⟩:=hraw τ ⟨hτ,hτρ⟩
  let b:ℝ:=min bm br
  let Be:ℝ:=Er+4/b^2
  let Ce:ℝ:=2*Ar+Cm
  let c:ℝ:=min cr κ
  let H:ℝ:=Hm+Hr+H0+1
  have hb:0<b:=lt_min hbm hbr
  have hBe:0<Be:=by dsimp[Be];positivity
  have hCe:0<Ce:=by dsimp[Ce];positivity
  have hc:0<c:=lt_min hcr hκ
  have hH:0<H:=by dsimp[H];positivity
  refine ⟨R,Ce,Be,c,H,hR,hRy,hCe,hBe,hc,hH,?_⟩
  intro g k K hg hK δ hδ hroot
  let h:ℝ:=complexity g p
  let J:ℕ:=⌊κ*Real.sqrt h⌋₊
  have hhM:Hm≤h:=by dsimp[H] at hg;linarith
  have hhR:Hr≤h:=by dsimp[H] at hg;linarith
  have hh0:H0≤h:=by dsimp[H] at hg;linarith
  have hh1:1≤h:=by dsimp[H] at hg;linarith
  have hh:0<h:=by linarith
  have hKκ:(K:ℝ)≤κ*Real.sqrt h:=hK.trans
    (mul_le_mul_of_nonneg_right (min_le_right cr κ) (Real.sqrt_nonneg h))
  have hKJ:K≤J:=Nat.le_floor hKκ
  have hKcr:(K:ℝ)≤cr*Real.sqrt h:=hK.trans
    (mul_le_mul_of_nonneg_right (min_le_left cr κ) (Real.sqrt_nonneg h))
  have hδr:δ∈Ioo (0:ℝ) Rr:=⟨hδ.1,hδ.2.trans_le hRRr⟩
  have heRaw:=hrawerr δ hδr h hhR J K hKJ (hmodels g hh0).1 hKcr
  rw[←hroot] at heRaw
  have heActual:=hactual g hhM δ hδ k hroot
  have hsum:(∑j∈Finset.range (K+1),(HigherOrder.rawExtractedCoefficient P p j (y₀-δ):ℂ)/(h:ℂ)^j)=
      ((∑j∈Finset.range (K+1),HigherOrder.rawExtractedCoefficient P p j (y₀-δ)/h^j:ℝ):ℂ) := by
    push_cast
    rfl
  have htri:= (norm_sub_le_norm_sub_add_norm_sub
      (((realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k:ℝ):ℂ))
      ((finiteMorseSourceIntegral (fun u:ℂ=>d.kernel.centeredPhase d.L d.q ((δ:ℂ),u))
          (fun s u=>d.preMorseAmplitude Q p f s ((δ:ℂ),u)) h (τ/Real.sqrt (Real.sqrt h)) J/
          (Real.sqrt (2*Real.pi):ℂ))*(((poissonNormalizer k)⁻¹:ℝ):ℂ))
      (∑j∈Finset.range (K+1),(HigherOrder.rawExtractedCoefficient P p j (y₀-δ):ℂ)/(h:ℂ)^j)).trans
      (add_le_add heActual heRaw)
  rw[hsum,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at htri
  have hexp (v:ℝ)(hv:b≤v):Real.exp (-v*Real.sqrt h)≤Real.exp (-b*Real.sqrt h):=
    Real.exp_le_exp.mpr (by nlinarith[Real.sqrt_nonneg h])
  have hexpM:=hexp bm (min_le_left _ _)
  have hexpR:=hexp br (min_le_right _ _)
  have hA:0≤Ar:=hAr.le
  have hM:0≤Cm:=hCm.le
  have hExp:=exp_neg_sqrt_gevrey_two_bound b h hb hh (K+1)
  have hErBe:Er≤Be:=by
    dsimp[Be]
    have ht:0≤4/b^2:=by positivity
    linarith
  have hExpB:4/b^2≤Be:=by dsimp[Be];linarith
  have hpow1:Er^(K+1)≤Be^(K+1):=pow_le_pow_left₀ hEr.le hErBe _
  have hpow2:(4/b^2)^(K+1)≤Be^(K+1):=pow_le_pow_left₀ (by positivity) hExpB _
  calc _ ≤ Cm*Real.exp (-bm*Real.sqrt h)+
        (Ar*Er^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+Ar*Real.exp (-br*Real.sqrt h)):=htri
       _ ≤ Ar*Er^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+(Cm+Ar)*Real.exp (-b*Real.sqrt h) := by
         have hm0:=mul_le_mul_of_nonneg_left hexpM hM
         have hr0:=mul_le_mul_of_nonneg_left hexpR hA
         nlinarith
       _ ≤ Ar*Er^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+
            (Cm+Ar)*((4/b^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)) :=
         add_le_add le_rfl (mul_le_mul_of_nonneg_left hExp (by positivity))
       _ ≤ Ar*Be^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+
            (Cm+Ar)*(Be^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)) := by gcongr
       _ = _:=by dsimp only[Ce];ring
end WP.Analysis

namespace WP.Analysis
lemma actual_critical_canonical_expansion (P:PsiTheory)(p:ℕ)(hp:1≤p) :
    ∃R C B c H:ℝ,0<R ∧ R<y₀ ∧ 0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧
      ∀g k K:ℕ,H≤(complexity g p:ℝ)→(K:ℝ)≤c*Real.sqrt (complexity g p:ℝ)→
      ∀δ∈Ioo (0:ℝ) R,(k:ℝ)=(complexity g p:ℝ)*WP.Psi (XR (y₀-δ))→
      |realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k-
        ∑j∈Finset.range (K+1),HigherOrder.rawExtractedCoefficient P p j (y₀-δ)/(complexity g p:ℝ)^j|≤
      C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1) := by
  obtain ⟨d⟩:=exists_criticalGaussianCoordinateData
  obtain ⟨Ω,f,C,B,κ,a,H0,hΩ,hcover,hC,hB,hκ,ha,hH0,hf,hf0,hrest,hbound,hmodels⟩:=
    HigherOrder.optimal_marked_model_real_comparison_with_budget P p hp
  exact d.actual_critical_raw_expansion_of_parameter_data P p hp Ω f C B κ a H0 hΩ hcover
    hC hB hκ ha hH0 hf hrest hbound hmodels
end WP.Analysis

namespace WP.Analysis
lemma actual_critical_extracted_expansion (P:PsiTheory)(p:ℕ)(hp:1≤p) :
    ∃R C B c H:ℝ,0<R ∧ R<y₀ ∧ 0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧
      ∀g k K:ℕ,H≤(complexity g p:ℝ)→(K:ℝ)≤c*Real.sqrt (complexity g p:ℝ)→
      ∀δ∈Ioo (0:ℝ) R,(k:ℝ)=(complexity g p:ℝ)*WP.Psi (XR (y₀-δ))→
      |realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k-
        ∑j∈Finset.range (K+1),HigherOrder.extractedCoefficient P p j (y₀-δ)/(complexity g p:ℝ)^j|≤
      C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1) := by
  obtain ⟨R,C,B,c,H,hR,hRy,hC,hB,hc,hH,herror⟩:=actual_critical_canonical_expansion P p hp
  refine ⟨R,C,B,c,H,hR,hRy,hC,hB,hc,hH,?_⟩
  intro g k K hg hK δ hδ hroot
  have hY0:y₀-δ≠0:=(show 0<y₀-δ by linarith[hδ.2]).ne'
  have hYcrit:y₀-δ≠y₀:=by linarith[hδ.1]
  simpa only[HigherOrder.extractedCoefficient,if_neg hY0,if_neg hYcrit] using herror g k K hg hK δ hδ hroot
end WP.Analysis
