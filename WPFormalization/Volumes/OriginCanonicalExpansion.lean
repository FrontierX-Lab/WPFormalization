import WPFormalization.HigherOrder.FixedSourceOriginCanonicalModel
import WPFormalization.Volumes.TinyFrequencyComparison
import WPFormalization.Volumes.OriginNonTinyCoefficientComparison
import WPFormalization.Analysis.ExponentialToGevreyTwo
/-! The original marked coefficient divided by the original extractionQ
has the prescribed canonical CG3 expansion uniformly at all sufficiently
small densities, including k=0. A single actual optimal source supplies
both frequency regimes, the finite-model expansion and its native budget.
The common constants precede g,k,K, and no auxiliary asymptotic premise
remains in the P-only producer. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 3000000 in
lemma actual_origin_extracted_expansion (P:PsiTheory)(p:ℕ)(hp:1≤p):
    ∃ν0 C B c H:ℝ,0<ν0 ∧ 0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧
      ∀g k K:ℕ,H≤(complexity g p:ℝ)→(k:ℝ)/(complexity g p:ℝ)≤ν0→
        (K:ℝ)≤c*Real.sqrt (complexity g p:ℝ)→
      |realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k-
        ∑j∈Finset.range (K+1),HigherOrder.extractedCoefficient P p j
          (densityY (2*(k:ℝ)/(complexity g p:ℝ)))/(complexity g p:ℝ)^j|≤
        C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1):=by
  obtain ⟨Ω,L,CL,BL,κ,a,Hs,S,Bc,ρ,D,Cs,d,Csmall,DM,E,hΩ,hcover,hCL,hBL,hκ,ha,hHs,
    hρ,hρx,hD,hCs,hd,hCsmall,hDM,hE,hLa,hL0,hLr,hLb,hS,hS0,hSd,hBc0,htrace,hlocal,hAa,hAb,hcircle,hmodels⟩:=
    HigherOrder.actual_strong_optimal_origin_model_data P p hp
  have hBc:AnalyticAt ℂ Bc 0:=(hlocal 0 (by simpa only[norm_zero] using hρ.le)).2.2.1
  have hBcn:Bc 0≠0:=by rw[hBc0];exact one_ne_zero
  have hSr:∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ):=fun x hx=>(htrace x hx).1
  have hBr:∀x∈Icc (0:ℝ) ρ,Bc (x:ℂ)=(extractionB p x:ℂ):=fun x hx=>(htrace x hx).2.2
  have hBn:∀x∈Icc (0:ℝ) ρ,‖Bc (x:ℂ)-1‖≤1/2:=by
    intro x hx
    exact (hlocal (x:ℂ) (by rw[Complex.norm_of_nonneg hx.1];exact hx.2)).2.2.2.1
  have hmap:∀z:ℂ,‖z‖≤ρ→PositiveConvolution.planarInverse P z∈Ω:=fun z hz=>(hlocal z hz).2.2.2.2
  have hSrg:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ):=by
    filter_upwards[eventually_lt_nhds hρ] with t ht ht0
    exact hSr t ⟨ht0,ht.le⟩
  have hBrg:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ):=by
    filter_upwards[eventually_lt_nhds hρ] with t ht ht0
    exact hBr t ⟨ht0,ht.le⟩
  obtain ⟨δm,Cm,Bm,hδm,hCm,hBm,hmodelerr⟩:=HigherOrder.fixed_source_origin_canonical_model_expansion P p hp Ω L CL BL
    hΩ hcover hCL hBL hLa hL0 hLr hLb S Bc hS hBc hSrg hBrg
  obtain ⟨κlo,Ct,Ht,hκlo,hCt,hHt,hHst,htiny⟩:=HigherOrder.tiny_frequency_coefficient_comparison_of_source P p S Bc L
    ρ κ (a/4) d Csmall Hs hρ hρx (by positivity) hd hCsmall hHs hS hS0 hSd hSr hBr hBn
    (by
      intro g hg
      rcases hmodels g hg with ⟨hbudget,hP,hreal,hM,hbase,hsmall,hcirc⟩
      exact ⟨fun z hz=>(hM z hz).1,hsmall⟩)
  obtain ⟨η,Cn,bn,Hn,hη,hηρ,hCn,hbn,hHn,hHsn,hnontiny⟩:=HigherOrder.origin_nontiny_coefficient_comparison_of_source P p hp
    Ω L S Bc ρ BL D κ a E Hs κlo hρ hρx hBL hD ha hE hHs hκlo hS hSd hBc hBcn hSr hBr hmap hAb hBn hcircle
    (by
      intro g hg
      rcases hmodels g hg with ⟨hbudget,hP,hreal,hM,hbase,hsmall,hcirc⟩
      exact ⟨hbudget,fun z hz=>⟨(hP z hz).2.1,(hP z hz).2.2.1⟩,fun z hz=>(hM z hz).1,hbase⟩)
  obtain ⟨r,hr,hxr⟩:=Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp
    (densitySaddle_tendsto_zero_right.eventually (eventually_lt_nhds hη)))
  let ν0:ℝ:=min δm (r/2)
  let be:ℝ:=min (a/4) bn
  let Ce:ℝ:=Ct+Cn
  let B:ℝ:=Bm+4/be^2
  let C:ℝ:=Cm+Ce
  let c:ℝ:=min κ (1/2)
  let H:ℝ:=Hs+Ht+Hn+1
  have hν0:0<ν0:=lt_min hδm (half_pos hr)
  have hν0δ:ν0≤δm:=min_le_left _ _
  have hν0r:ν0<r:=(min_le_right _ _).trans_lt (half_lt_self hr)
  have hbe:0<be:=lt_min (by positivity) hbn
  have hCe:0<Ce:=add_pos hCt hCn
  have hB:0<B:=by dsimp[B];positivity
  have hC:0<C:=by dsimp[C];positivity
  have hc:0<c:=lt_min hκ (by norm_num)
  have hH:0<H:=by dsimp[H];positivity
  refine ⟨ν0,C,B,c,H,hν0,hC,hB,hc,hH,?_⟩
  intro g k K hg hν hK
  let h:ℝ:=complexity g p
  let J:ℕ:=⌊κ*Real.sqrt h⌋₊
  let ν:ℝ:=(k:ℝ)/h
  have hhS:Hs≤h:=by dsimp[H] at hg;linarith
  have hhT:Ht≤h:=by dsimp[H] at hg;linarith
  have hhN:Hn≤h:=by dsimp[H] at hg;linarith
  have hh1:1≤h:=by dsimp[H] at hg;linarith
  have hh:0<h:=by linarith
  have hs:Stable g p:=by
    have hn:1≤complexity g p:=by exact_mod_cast (show (1:ℝ)≤(complexity g p:ℝ) from hh1)
    unfold Stable complexity at *
    omega
  have hKκ:(K:ℝ)≤κ*Real.sqrt h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_left κ (1/2)) (Real.sqrt_nonneg h))
  have hKJ:K≤J:=Nat.le_floor hKκ
  have hsqrt:Real.sqrt h≤h:=(Real.sqrt_le_iff).mpr ⟨hh.le,by nlinarith⟩
  have hKhalf:(K:ℝ)≤h/2:=by
    have ht:=hK.trans (mul_le_mul_of_nonneg_right (min_le_right κ (1/2)) (Real.sqrt_nonneg h))
    nlinarith
  have hbudget:2*BL*((J:ℝ)+1)^2≤h:=(hmodels g hhS).1
  have hActual:‖WP.coeff (iteratedDeriv p (Phi P g)) k/(extractionQ g p k:ℂ)-
      WP.coeff (HigherOrder.normalizedFiniteMarkedModel P g p S Bc L J) k/
        ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)‖≤Ce*Real.exp (-be*Real.sqrt h):=by
    by_cases hk:(k:ℝ)≤κlo*Real.sqrt h
    · have he:=(htiny g hhT k hk).2.2
      apply he.trans
      have hr:Real.exp (-(a/4)*Real.sqrt h)≤Real.exp (-be*Real.sqrt h):=
        Real.exp_le_exp.mpr (by nlinarith[min_le_left (a/4) bn,Real.sqrt_nonneg h])
      exact mul_le_mul (by dsimp[Ce];linarith) hr (Real.exp_pos _).le hCe.le
    · have hlo:κlo*Real.sqrt h≤(k:ℝ):=(not_le.mp hk).le
      have hkp:0<(k:ℝ):=(mul_pos hκlo (Real.sqrt_pos.mpr hh)).trans_le hlo
      have hνp:0<ν:=div_pos hkp hh
      let x:ℝ:=XR (densityY (2*ν))
      have hx:x∈Ioo (0:ℝ) xCritical:=(physicalDensitySaddle_spec ν hνp).1
      have hΨ:Psi x=ν:=(physicalDensitySaddle_spec ν hνp).2
      have hxη:x<η:=hxr (show dist ν 0<r by rw[Real.dist_eq,sub_zero,abs_of_pos hνp];exact hν.trans_lt hν0r) hνp.le
      have hroot:(k:ℝ)=h*Psi x:=by rw[hΨ];dsimp[ν];field_simp
      have he:=hnontiny g hhN x ⟨hx.1,hxη⟩ k hroot hlo
      apply he.trans
      have hr:Real.exp (-bn*Real.sqrt h)≤Real.exp (-be*Real.sqrt h):=
        Real.exp_le_exp.mpr (by nlinarith[min_le_right (a/4) bn,Real.sqrt_nonneg h])
      exact mul_le_mul (by dsimp[Ce];linarith) hr (Real.exp_pos _).le hCe.le
  have hModel:=hmodelerr g k K J hh (hν.trans hν0δ) hKhalf hKJ hbudget
  have hcoef:WP.coeff (iteratedDeriv p (Phi P g)) k=(realCoeff (iteratedDeriv p (Phi P g)) k:ℂ):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using (marked_generating_nonnegative_coefficients P g p hp hs k).2
  have hsum:(∑j∈Finset.range (K+1),(h:ℂ)⁻¹^j*(HigherOrder.extractedCoefficient P p j (densityY (2*(k:ℝ)/h)):ℂ))=
      ((∑j∈Finset.range (K+1),HigherOrder.extractedCoefficient P p j (densityY (2*(k:ℝ)/h))/h^j:ℝ):ℂ):=by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw[inv_pow]
    ring
  have htri:=(norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hActual hModel)
  rw[hcoef,hsum,←Complex.ofReal_div,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at htri
  have hExp:=exp_neg_sqrt_gevrey_two_bound be h hbe hh (K+1)
  have hBmB:Bm≤B:=by
    dsimp[B]
    have ht:(0:ℝ)≤4/be^2:=by positivity
    linarith
  have hExpB:4/be^2≤B:=by dsimp[B];linarith
  have hp1:Bm^(K+1)≤B^(K+1):=pow_le_pow_left₀ hBm.le hBmB _
  have hp2:(4/be^2)^(K+1)≤B^(K+1):=pow_le_pow_left₀ (by positivity) hExpB _
  calc _≤Ce*Real.exp (-be*Real.sqrt h)+Cm*Bm^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=htri
       _≤Ce*((4/be^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))+
          Cm*Bm^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=
            add_le_add (mul_le_mul_of_nonneg_left hExp hCe.le) le_rfl
       _≤Ce*(B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))+
          Cm*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by gcongr
       _=_:=by dsimp[C];ring
end WP.Analysis
