import WPFormalization.Volumes.CompactNumeratorGaussian
import WPFormalization.Volumes.CompactNumeratorBounds
import WPFormalization.Analysis.PoissonInverseUniformScale
import WPFormalization.Analysis.ComplexGevreyTwoPointwise
import WPFormalization.Analysis.ParameterInverse
/-! The literal compact finite source integral times the genuine inverse Poisson normalizer has the ORIGINAL raw CG3 expansion, uniformly on the compact physical interval and at every allowed truncation order. Actual local chart identities and finite-cover bounds precede multiplication by the exact rescaled inverse Stirling series. The given S/l/Bc/f/B and native J budget are retained. Transfer from this finite analytic model to the true generating coefficient remains separate. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1000000 in
lemma compact_original_raw_uniform_gaussian_gevrey_two_all_cutoffs
    (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hbc : b < xCritical)
    (S l Bc : ℂ → ℂ) (Ω : Set ℂ) (f : ℕ → ℂ → ℂ) (C0 B0 : ℝ)
    (hΩ : IsOpen Ω) (hcover : ∀ Y ∈ Icc (0 : ℝ) y₀, (Y : ℂ) ∈ Ω)
    (hC0 : 0 < C0) (hB0 : 0 < B0) (hf : ∀ j, AnalyticOnNhd ℂ (f j) Ω)
    (hfr : ∀ j Y, Y ∈ Icc (0 : ℝ) y₀ → f j (Y : ℂ) =
      (HigherOrder.markedCoefficient P p j Y : ℂ))
    (hbound : ∀ j z, z ∈ Ω → ‖f j z‖ ≤ C0 * B0^j * (j.factorial : ℝ)^2)
    (hdata : ∀ x ∈ Icc a b, AnalyticAt ℂ S (x : ℂ) ∧ AnalyticAt ℂ l (x : ℂ) ∧
      ((fun t : ℝ => S (t : ℂ)) =ᶠ[𝓝 x] (fun t : ℝ => (extractionS t : ℂ))) ∧
      l (x : ℂ) = ((Real.sqrt (WP.euler WP.Psi x))⁻¹ : ℝ) ∧
      ∀ᶠ q : ℂ in 𝓝 (x : ℂ), (l q)^2 * ((complexEuler^[2]) S) q = 1)
    (hBc : ∀ x ∈ Ico (0 : ℝ) xCritical,
      AnalyticAt ℂ Bc (x : ℂ) ∧ Bc (x : ℂ) = (extractionB p x : ℂ)) :
    ∃ ρ A E : ℝ, 0 < ρ ∧ 0 < A ∧ 0 < E ∧
      ∀ τ ∈ Ioc (0 : ℝ) ρ, ∃ c rate H : ℝ, 0 < c ∧ 0 < rate ∧ 0 < H ∧
      ∀ x ∈ Icc a b, ∀ h : ℝ, H ≤ h → ∀ J K : ℕ, K ≤ J →
        2 * B0 * ((J : ℝ) + 1)^2 ≤ h → (K : ℝ) ≤ c * Real.sqrt h →
        ‖(finiteMorseSourceIntegral (fun u : ℂ => centeredExponentialPhase S l ((x : ℂ),u))
            (fun s u => compactPremorseAmplitude P Bc l f s ((x : ℂ),u))
            h (τ / Real.sqrt (Real.sqrt h)) J / (Real.sqrt (2*Real.pi) : ℂ)) *
            (((poissonNormalizer (h*WP.Psi x))⁻¹ : ℝ) : ℂ) -
          ∑ j ∈ Finset.range (K+1),
            (HigherOrder.rawExtractedCoefficient P p j (inverseY x) : ℂ) / (h : ℂ)^j‖ ≤
          A * E^(K+1) * ((K+1).factorial : ℝ)^2 / h^(K+1) +
            A * Real.exp (-rate*Real.sqrt h) := by
  obtain ⟨ρ,A1,E1,hρ,hA1,hE1,hnum⟩ :=
    compact_original_numerator_uniform_gaussian_gevrey_two_all_cutoffs P p hp a b ha hab hbc
      S l Bc Ω f C0 B0 hΩ hcover hC0 hB0 hf hfr hbound hdata hBc
  obtain ⟨Cn,Bn,hCn,hBn,hncoeff⟩ :=
    compact_original_numerator_uniform_coefficient_bound P p hp a b ha hab hbc
      S l Bc Ω f C0 B0 hΩ hcover hC0 hB0 hf hfr hbound hdata hBc
  have haI : a ∈ Ioo (0 : ℝ) xCritical := ⟨ha,hab.trans_lt hbc⟩
  have hYa := (inverseY_branch a ⟨ha.le,haI.2⟩).1
  have hYapos : 0 < inverseY a := by
    by_contra hn
    have he : inverseY a = 0 := le_antisymm (le_of_not_gt hn) hYa.1
    have he' := (inverseY_branch a ⟨ha.le,haI.2⟩).2
    rw [he,XR_zero] at he'
    linarith
  have hPa : 0 < WP.Psi a := by
    have he := density_strictMonoOn ⟨le_rfl,y₀_pos⟩ hYa hYapos
    rw [density_zero_value] at he
    exact half_pos he
  have hPmin (x : ℝ) (hx : x ∈ Icc a b) : WP.Psi a ≤ WP.Psi x :=
    Psi_strictMonoOn.monotoneOn haI ⟨ha.trans_le hx.1,hx.2.trans_lt hbc⟩ hx.1
  obtain ⟨Cd,Bd,cd,Hd,M,hCd,hBd,hcd,hHd,hM,hden⟩ := poissonInverse_uniform_scaled_data (WP.Psi a) hPa
  have hphysical (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Ioo (0 : ℝ) xCritical :=
    ⟨ha.trans_le hx.1,hx.2.trans_lt hbc⟩
  let C:ℝ:=max Cn Cd
  let B:ℝ:=max Bn Bd
  let A':ℝ:=A1/Real.sqrt (2*Real.pi)
  let A:ℝ:=M*A'+2*C*Cd+8*C^2+1
  let E:ℝ:=E1+Bd+2*B*(Real.exp 1)^2
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
  refine ⟨ρ,3*A,E,hρ,by positivity,hE,?_⟩
  intro τ hτ
  obtain ⟨cs,a,Hs,hcs,ha,hHs,hnumerr⟩:=hnum τ hτ
  obtain ⟨c,Hw,hc,hccap,hHw,hw⟩:=gevreyTwo_cauchy_window B (min cs cd) hB (lt_min hcs hcd)
  let H:ℝ:=max Hs (max Hd (max Hw 1))
  have hH:0<H:=hHs.trans_le (le_max_left _ _)
  refine ⟨c,a,H,hc,ha,hH,?_⟩
  intro x hx h hhH J K hKJ hwin hK
  have hxI : x ∈ Ioo (0 : ℝ) xCritical := hphysical x hx
  have hhS:Hs≤h:=(le_max_left _ _).trans hhH
  have hhD:Hd≤h:=((le_max_left _ _).trans (le_max_right _ _)).trans hhH
  have hhW:Hw≤h:=((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hhH
  have hh1:1≤h:=((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hhH
  have hh:0<h:=zero_lt_one.trans_le hh1
  have hcsK:(K:ℝ)≤cs*Real.sqrt h:=hK.trans (mul_le_mul_of_nonneg_right (hccap.trans (min_le_left _ _)) (Real.sqrt_nonneg h))
  have hsH:Real.sqrt h≤h:=(Real.sqrt_le_iff).mpr ⟨hh.le,by nlinarith⟩
  have hcdK:(K:ℝ)≤cd*h:=hK.trans ((mul_le_mul_of_nonneg_right (hccap.trans (min_le_right _ _)) (Real.sqrt_nonneg h)).trans
    (mul_le_mul_of_nonneg_left hsH hcd.le))
  let F:HigherOrder.Series:=extractionEvenNumerator P p x
  let G:HigherOrder.Series:=PowerSeries.rescale (WP.Psi x)⁻¹ (HigherOrder.poissonStirlingSeries⁻¹)
  let Z:ℂ:=finiteMorseSourceIntegral (fun u:ℂ=>centeredExponentialPhase S l ((x:ℂ),u))
    (fun s u=>compactPremorseAmplitude P Bc l f s ((x:ℂ),u)) h (τ/Real.sqrt (Real.sqrt h)) J
  let y:ℝ:=(poissonNormalizer (h*WP.Psi x))⁻¹
  have hFn:∀j,|PowerSeries.coeff j F|≤C*B^j*(j.factorial:ℝ)^2:=by
    intro j
    exact (hncoeff x hx j).trans (by dsimp[C,B];gcongr <;>exact le_max_left _ _)
  obtain ⟨hGn,hyData⟩:=hden (WP.Psi x) (hPmin x hx)
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
  have hz0:=hnumerr x hx h hhS J K hKJ hwin hcsK
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
  have hprod:(inversePowerTruncation (F*G) K h:ℂ)=
      ∑j∈Finset.range (K+1),(HigherOrder.rawExtractedCoefficient P p j (inverseY x):ℂ)/(h:ℂ)^j := by
    dsimp only[inversePowerTruncation]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    have hc0:PowerSeries.coeff j (F*G)=HigherOrder.rawExtractedCoefficient P p j (inverseY x) := by
      change PowerSeries.coeff j (F*G) = PowerSeries.coeff (2*j)
        (HigherOrder.extractionNumerator P p (XR (inverseY x)) * (HigherOrder.extractionDenominator (XR (inverseY x)))⁻¹)
      rw [(inverseY_branch x ⟨hxI.1.le,hxI.2⟩).2]
      exact (raw_extraction_even_product_coefficient P p hp x hxI j).symm
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
