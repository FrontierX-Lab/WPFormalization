import WPFormalization.Volumes.CriticalGaussianUniformError
import WPFormalization.Volumes.CriticalNumeratorBounds
import WPFormalization.Volumes.CriticalPoissonScale
import WPFormalization.Analysis.ComplexGevreyTwoPointwise
/-! The actual finite critical source integral times the true inverse Poisson normalizer has the original full raw CG3 expansion, with a uniform all-order Gevrey-two error and exponential tail. This is a finite analytic model result; transfer to the actual generating-function coefficient remains separate. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
set_option maxHeartbeats 1000000 in
lemma CriticalGaussianCoordinateData.original_raw_uniform_gaussian_gevrey_two_all_cutoffs
    (d:CriticalGaussianCoordinateData) (P:PsiTheory) (p:ℕ) (hp:1≤p)
    (Q:ℂ→ℂ) (Ω:Set ℂ) (f:ℕ→ℂ→ℂ) (C0 B0:ℝ)
    (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ))
    (hΩ:IsOpen Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (hC0:0<C0) (hB0:0<B0)
    (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hrest:∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hbound:∀j z,z∈Ω→‖f j z‖≤C0*B0^j*(j.factorial:ℝ)^2) :
    ∃R ρ A E:ℝ,0<R ∧ R<y₀ ∧ 0<ρ ∧ 0<A ∧ 0<E ∧
      ∀τ∈Ioc (0:ℝ) ρ,∃c a H:ℝ,0<c ∧ 0<a ∧ 0<H ∧
      ∀δ∈Ioo (0:ℝ) R,∀h:ℝ,H≤h→∀J K:ℕ,K≤J→
        2*B0*((J:ℝ)+1)^2≤h→(K:ℝ)≤c*Real.sqrt h→
        ‖(finiteMorseSourceIntegral (fun u:ℂ=>d.kernel.centeredPhase d.L d.q ((δ:ℂ),u))
            (fun s u=>d.preMorseAmplitude Q p f s ((δ:ℂ),u)) h (τ/Real.sqrt (Real.sqrt h)) J/
              (Real.sqrt (2*Real.pi):ℂ))*
            (((poissonNormalizer (h*WP.Psi (XR (y₀-δ))))⁻¹:ℝ):ℂ)-
          ∑j∈Finset.range (K+1),(HigherOrder.rawExtractedCoefficient P p j (y₀-δ):ℂ)/(h:ℂ)^j‖≤
        A*E^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+A*Real.exp (-a*Real.sqrt h) := by
  obtain ⟨R1,ρ,A1,E1,hR1,hR1y,hρ,hA1,hE1,hnum⟩:=
    d.original_numerator_uniform_gaussian_gevrey_two_all_cutoffs P p hp Q Ω f C0 B0
      hQ hQ0 hQphys hΩ hcover hC0 hB0 hf hrest hbound
  obtain ⟨R2,Cn,Bn,hR2,hR2y,hCn,hBn,hncoeff⟩:=
    d.original_numerator_uniform_gevrey_two_bound P p hp Q Ω f C0 B0
      hQ hQ0 hQphys hΩ hcover hC0 hB0 hf hrest hbound
  obtain ⟨R3,Cd,Bd,cd,Hd,M,hR3,hR3y,hCd,hBd,hcd,hHd,hM,hden⟩:=d.kernel.inverse_poisson_uniform_scaled_data
  let R:ℝ:=min R1 (min R2 R3)/2
  let C:ℝ:=max Cn Cd
  let B:ℝ:=max Bn Bd
  let A':ℝ:=A1/Real.sqrt (2*Real.pi)
  let A:ℝ:=M*A'+2*C*Cd+8*C^2+1
  let E:ℝ:=E1+Bd+2*B*(Real.exp 1)^2
  have hR:0<R:=half_pos (lt_min hR1 (lt_min hR2 hR3))
  have hRR1:R<R1:=(half_lt_self (lt_min hR1 (lt_min hR2 hR3))).trans_le (min_le_left _ _)
  have hRR2:R<R2:=(half_lt_self (lt_min hR1 (lt_min hR2 hR3))).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hRR3:R<R3:=(half_lt_self (lt_min hR1 (lt_min hR2 hR3))).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hC:0<C:=hCn.trans_le (le_max_left _ _)
  have hB:0<B:=hBn.trans_le (le_max_left _ _)
  have hRoot:0<Real.sqrt (2*Real.pi):=by positivity
  have hA':0<A':=div_pos hA1 hRoot
  have hA:0<A:=by dsimp[A];positivity
  have hE:0<E:=by dsimp[E];positivity
  have hMA0:0≤M*A':=by positivity
  have hCC0:0≤2*C*Cd:=by positivity
  have hSq0:0≤8*C^2:=by positivity
  have hEE0:0≤2*B*(Real.exp 1)^2:=by positivity
  have hMA:M*A'≤A:=by dsimp[A];linarith
  have hCCE:2*C*Cd≤A:=by dsimp[A];linarith
  have h8C:8*C^2≤A:=by dsimp[A];linarith
  have hE1E:E1≤E:=by dsimp[E];linarith
  have hBdE:Bd≤E:=by dsimp[E];linarith
  have hEE:2*B*(Real.exp 1)^2≤E:=by dsimp[E];linarith
  refine ⟨R,ρ,3*A,E,hR,hRR1.trans hR1y,hρ,by positivity,hE,?_⟩
  intro τ hτ
  obtain ⟨cs,a,Hs,hcs,ha,hHs,hnumerr⟩:=hnum τ hτ
  obtain ⟨c,Hw,hc,hccap,hHw,hw⟩:=gevreyTwo_cauchy_window B (min cs cd) hB (lt_min hcs hcd)
  let H:ℝ:=max Hs (max Hd (max Hw 1))
  have hH:0<H:=hHs.trans_le (le_max_left _ _)
  refine ⟨c,a,H,hc,ha,hH,?_⟩
  intro δ hδ h hhH J K hKJ hwin hK
  have hδ1:δ∈Ioo (0:ℝ) R1:=⟨hδ.1,hδ.2.trans hRR1⟩
  have hδ2:δ∈Ioo (0:ℝ) R2:=⟨hδ.1,hδ.2.trans hRR2⟩
  have hδ3:δ∈Ioo (0:ℝ) R3:=⟨hδ.1,hδ.2.trans hRR3⟩
  have hhS:Hs≤h:=(le_max_left _ _).trans hhH
  have hhD:Hd≤h:=((le_max_left _ _).trans (le_max_right _ _)).trans hhH
  have hhW:Hw≤h:=((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hhH
  have hh1:1≤h:=((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hhH
  have hh:0<h:=zero_lt_one.trans_le hh1
  have hcsK:(K:ℝ)≤cs*Real.sqrt h:=hK.trans (mul_le_mul_of_nonneg_right (hccap.trans (min_le_left _ _)) (Real.sqrt_nonneg h))
  have hsH:Real.sqrt h≤h:=(Real.sqrt_le_iff).mpr ⟨hh.le,by nlinarith⟩
  have hcdK:(K:ℝ)≤cd*h:=hK.trans ((mul_le_mul_of_nonneg_right (hccap.trans (min_le_right _ _)) (Real.sqrt_nonneg h)).trans
    (mul_le_mul_of_nonneg_left hsH hcd.le))
  let x:ℝ:=XR (y₀-δ)
  let F:HigherOrder.Series:=extractionEvenNumerator P p x
  let G:HigherOrder.Series:=PowerSeries.rescale (WP.Psi x)⁻¹ (HigherOrder.poissonStirlingSeries⁻¹)
  let Z:ℂ:=finiteMorseSourceIntegral (fun u:ℂ=>d.kernel.centeredPhase d.L d.q ((δ:ℂ),u))
    (fun s u=>d.preMorseAmplitude Q p f s ((δ:ℂ),u)) h (τ/Real.sqrt (Real.sqrt h)) J
  let y:ℝ:=(poissonNormalizer (h*WP.Psi x))⁻¹
  have hFn:∀j,|PowerSeries.coeff j F|≤C*B^j*(j.factorial:ℝ)^2:=by
    intro j
    exact (hncoeff δ hδ2 j).trans (by dsimp[C,B];gcongr <;>exact le_max_left _ _)
  obtain ⟨hPsi,hGn,hyData⟩:=hden δ hδ3
  obtain ⟨hyM,hyerr⟩:=hyData h hhD
  have hGn':∀j,|PowerSeries.coeff j G|≤C*B^j*(j.factorial:ℝ)^2:=by
    intro j
    exact (hGn j).trans (by dsimp[C,B];gcongr <;>exact le_max_right _ _)
  have hpoly:(∑j∈Finset.range (K+1),
      ((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p x):ℝ):ℂ)/(h:ℂ)^j)=
      (inversePowerTruncation F K h:ℂ) := by
    simp only[inversePowerTruncation,F,extractionEvenNumerator,PowerSeries.coeff_mk]
    push_cast
    rfl
  have hz0:=hnumerr δ hδ1 h hhS J K hKJ hwin hcsK
  change ‖Z-(Real.sqrt (2*Real.pi):ℂ)*_‖≤_ at hz0
  rw[hpoly] at hz0
  have hz:‖Z/(Real.sqrt (2*Real.pi):ℂ)-(inversePowerTruncation F K h:ℂ)‖≤
      A'*E1^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+A'*Real.exp (-a*Real.sqrt h) := by
    have he:Z/(Real.sqrt (2*Real.pi):ℂ)-(inversePowerTruncation F K h:ℂ)=
        (Z-(Real.sqrt (2*Real.pi):ℂ)*(inversePowerTruncation F K h:ℂ))/(Real.sqrt (2*Real.pi):ℂ):=by field_simp[show (Real.sqrt (2*Real.pi):ℂ)≠0 by exact_mod_cast hRoot.ne']
    rw[he,norm_div,Complex.norm_of_nonneg hRoot.le]
    exact (div_le_div_of_nonneg_right hz0 hRoot.le).trans_eq (by dsimp[A'];ring)
  have he:=complex_mul_value_gevreyTwo_truncation_error F G C B hC.le hB hFn hGn' K h hh (hw h hhW K hK)
    (Z/(Real.sqrt (2*Real.pi):ℂ)) y
    (A'*E1^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+A'*Real.exp (-a*Real.sqrt h))
    (Cd*Bd^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)) M hz (hyerr K hcdK) hyM
  have hYp:0<y₀-δ:=by linarith[hδ.2,hRR1,hR1y]
  have hYlt:y₀-δ<y₀:=by linarith[hδ.1]
  have hx:x∈Ioo (0:ℝ) xCritical:=by
    constructor
    · simpa only[XR_zero] using XR_strictMonoOn (show (0:ℝ)∈Iic y₀ from y₀_pos.le) (show y₀-δ∈Iic y₀ from hYlt.le) hYp
    · exact XR_strictMonoOn (show y₀-δ∈Iic y₀ from hYlt.le) (show y₀∈Iic y₀ from by simp) hYlt
  have hprod:(inversePowerTruncation (F*G) K h:ℂ)=
      ∑j∈Finset.range (K+1),(HigherOrder.rawExtractedCoefficient P p j (y₀-δ):ℂ)/(h:ℂ)^j := by
    dsimp only[inversePowerTruncation]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    have hc0:PowerSeries.coeff j (F*G)=HigherOrder.rawExtractedCoefficient P p j (y₀-δ):=
      (raw_extraction_even_product_coefficient P p hp x hx j).symm
    rw[hc0]
  rw[hprod] at he
  apply he.trans
  let v:ℝ:=((K+1).factorial:ℝ)^2/h^(K+1)
  have hv:0≤v:=by dsimp[v];positivity
  have hmain1:(M*A')*E1^(K+1)*v≤A*E^(K+1)*v:=
    mul_le_mul_of_nonneg_right (mul_le_mul hMA (pow_le_pow_left₀ hE1.le hE1E _) (by positivity) hA.le) hv
  have hmain2:(2*C*Cd)*Bd^(K+1)*v≤A*E^(K+1)*v:=
    mul_le_mul_of_nonneg_right (mul_le_mul hCCE (pow_le_pow_left₀ hBd.le hBdE _) (by positivity) hA.le) hv
  have hmain3:(8*C^2)*(2*B*(Real.exp 1)^2)^(K+1)*v≤A*E^(K+1)*v:=
    mul_le_mul_of_nonneg_right (mul_le_mul h8C (pow_le_pow_left₀ (by positivity) hEE _) (by positivity) hA.le) hv
  have htail:(M*A')*Real.exp (-a*Real.sqrt h)≤A*Real.exp (-a*Real.sqrt h):=
    mul_le_mul_of_nonneg_right hMA (Real.exp_pos _).le
  have hRhs:(3*A)*E^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+(3*A)*Real.exp (-a*Real.sqrt h)=
      (3*A)*E^(K+1)*v+(3*A)*Real.exp (-a*Real.sqrt h):=by dsimp[v];ring
  rw[hRhs]
  have heq:M*(A'*E1^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+A'*Real.exp (-a*Real.sqrt h))+
      2*C*(Cd*Bd^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1))+
      8*C^2*(2*B*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)=
      (M*A')*E1^(K+1)*v+(2*C*Cd)*Bd^(K+1)*v+(8*C^2)*(2*B*(Real.exp 1)^2)^(K+1)*v+
        (M*A')*Real.exp (-a*Real.sqrt h):=by dsimp[v];ring
  rw[heq]
  have hTail0:0≤A*Real.exp (-a*Real.sqrt h):=by positivity
  nlinarith
end WP.Analysis
