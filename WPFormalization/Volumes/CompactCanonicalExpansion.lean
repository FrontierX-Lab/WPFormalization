import WPFormalization.Volumes.CompactActualModelComparison
import WPFormalization.Volumes.CompactRawGaussianUniform
import WPFormalization.Analysis.ExponentialToGevreyTwo
import WPFormalization.HigherOrder.OptimalMarkedBudget
/-! Actual uniform canonical extraction on each compact physical interval. Original Phi coefficients divided by the original extractionQ have the ORIGINAL raw CG3 expansion with a pure Gevrey-two remainder. The parameter client preserves the same canonical f/B/kappa/J and actual S/l/Bc throughout comparison and Gaussian integration. The P-only producers supply the true optimal source data and retain no paper-specific approximation premise; the actual extractedCoefficient interior branch is included. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
open Set Filter
open scoped Topology
set_option maxHeartbeats 2000000 in
lemma actual_compact_raw_expansion_of_parameter_data
    (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (α β:ℝ)(hα:0<α)(hαβ:α≤β)(hβc:β<xCritical)
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
    ∃Ce Be c H:ℝ,0<Ce ∧ 0<Be ∧ 0<c ∧ 0<H ∧
      ∀g k K:ℕ,H≤(complexity g p:ℝ)→(K:ℝ)≤c*Real.sqrt (complexity g p:ℝ)→
      ∀x∈Icc α β,(k:ℝ)=(complexity g p:ℝ)*WP.Psi x→
      |realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k-
        ∑j∈Finset.range (K+1),HigherOrder.rawExtractedCoefficient P p j (inverseY x)/(complexity g p:ℝ)^j|≤
      Ce*Be^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1) := by
  obtain ⟨S,l,Bc,hData,hBc,hcaps⟩ := actual_compact_coefficient_model_comparison P p hp α β hα hαβ hβc
    Ω f C B κ a H0 hΩ hcover hC hB hκ ha hH0 hf hrest hbound hmodels
  obtain ⟨ρ,Ar,Er,hρ,hAr,hEr,hraw⟩ :=
    compact_original_raw_uniform_gaussian_gevrey_two_all_cutoffs P p hp α β hα hαβ hβc
      S l Bc Ω f C B hΩ hcover hC hB hf hrest hbound (by
        intro x hx
        have hd := hData x hx
        exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.2.2.1,hd.2.2.2.2.2.2⟩) hBc
  obtain ⟨τ,Cm,bm,Hm,hτ,hτρ,hCm,hbm,hHm,hactual⟩ := hcaps ρ hρ
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
  refine ⟨Ce,Be,c,H,hCe,hBe,hc,hH,?_⟩
  intro g k K hg hK x hx hroot
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
  have heRaw:=hrawerr x hx h hhR J K hKJ (hmodels g hh0).1 hKcr
  rw[←hroot] at heRaw
  have heActual:=hactual g hhM x hx k hroot
  have hsum:(∑j∈Finset.range (K+1),(HigherOrder.rawExtractedCoefficient P p j (inverseY x):ℂ)/(h:ℂ)^j)=
      ((∑j∈Finset.range (K+1),HigherOrder.rawExtractedCoefficient P p j (inverseY x)/h^j:ℝ):ℂ) := by
    push_cast
    rfl
  have htri:= (norm_sub_le_norm_sub_add_norm_sub
      (((realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k:ℝ):ℂ))
      ((finiteMorseSourceIntegral (fun u:ℂ=>centeredExponentialPhase S l ((x:ℂ),u))
          (fun s u=>compactPremorseAmplitude P Bc l f s ((x:ℂ),u)) h (τ/Real.sqrt (Real.sqrt h)) J/
          (Real.sqrt (2*Real.pi):ℂ))*(((poissonNormalizer k)⁻¹:ℝ):ℂ))
      (∑j∈Finset.range (K+1),(HigherOrder.rawExtractedCoefficient P p j (inverseY x):ℂ)/(h:ℂ)^j)).trans
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
lemma actual_compact_canonical_expansion (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (α β:ℝ)(hα:0<α)(hαβ:α≤β)(hβc:β<xCritical) :
    ∃C B c H:ℝ,0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧
      ∀g k K:ℕ,H≤(complexity g p:ℝ)→(K:ℝ)≤c*Real.sqrt (complexity g p:ℝ)→
      ∀x∈Icc α β,(k:ℝ)=(complexity g p:ℝ)*WP.Psi x→
      |realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k-
        ∑j∈Finset.range (K+1),HigherOrder.rawExtractedCoefficient P p j (inverseY x)/(complexity g p:ℝ)^j|≤
      C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1) := by
  obtain ⟨Ω,f,C,B,κ,a,H0,hΩ,hcover,hC,hB,hκ,ha,hH0,hf,hf0,hrest,hbound,hmodels⟩:=
    HigherOrder.optimal_marked_model_real_comparison_with_budget P p hp
  exact actual_compact_raw_expansion_of_parameter_data P p hp α β hα hαβ hβc Ω f C B κ a H0 hΩ hcover
    hC hB hκ ha hH0 hf hrest hbound hmodels
end WP.Analysis

namespace WP.Analysis
lemma actual_compact_extracted_expansion (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (α β:ℝ)(hα:0<α)(hαβ:α≤β)(hβc:β<xCritical) :
    ∃C B c H:ℝ,0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧
      ∀g k K:ℕ,H≤(complexity g p:ℝ)→(K:ℝ)≤c*Real.sqrt (complexity g p:ℝ)→
      ∀x∈Icc α β,(k:ℝ)=(complexity g p:ℝ)*WP.Psi x→
      |realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k-
        ∑j∈Finset.range (K+1),HigherOrder.extractedCoefficient P p j (inverseY x)/(complexity g p:ℝ)^j|≤
      C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1) := by
  obtain ⟨C,B,c,H,hC,hB,hc,hH,herror⟩ := actual_compact_canonical_expansion P p hp α β hα hαβ hβc
  refine ⟨C,B,c,H,hC,hB,hc,hH,?_⟩
  intro g k K hg hK x hx hroot
  have hxI : x ∈ Ico (0 : ℝ) xCritical := ⟨(hα.trans_le hx.1).le,hx.2.trans_lt hβc⟩
  have hY := (inverseY_branch x hxI).1
  have hY0 : inverseY x ≠ 0 := by
    intro hz
    have he := (inverseY_branch x hxI).2
    rw [hz,XR_zero] at he
    linarith [hα.trans_le hx.1]
  have hYcrit : inverseY x ≠ y₀ := ne_of_lt hY.2
  simpa only [HigherOrder.extractedCoefficient,if_neg hY0,if_neg hYcrit]
    using herror g k K hg hK x hx hroot
end WP.Analysis
