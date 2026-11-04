import WPFormalization.Analysis.GaussianTruncationWindow
import WPFormalization.Analysis.UniformMorseFiniteModel
import WPFormalization.Volumes.UniformCriticalMorseDomain
import WPFormalization.Volumes.CriticalRawCoefficientMatching
/-! The actual critical finite Morse model has a uniform Gevrey-two Gaussian error at every smaller common cutoff. The supplied coefficient family and its native budget are retained, and the prescribed numerator coefficients are identified by the proved original CG3 matching. -/
noncomputable section
open Set MeasureTheory
namespace WP.Analysis
lemma CriticalGaussianCoordinateData.uniform_finite_model_gaussian_error_all_cutoffs
    (d:CriticalGaussianCoordinateData) (Q:ℂ→ℂ) (p:ℕ) (f:ℕ→ℂ→ℂ)
    (Ω:Set ℂ) (C B:ℝ) (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1)
    (hΩ:IsOpen Ω) (hcover:(y₀:ℂ)∈Ω) (hC:0<C) (hB:0<B)
    (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hbound:∀j z,z∈Ω→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2) :
    ∃ρ A E T D:ℝ,0<ρ ∧ 0<A ∧ 0<E ∧ 0<T ∧ 1≤D ∧
      ∀τ∈Ioc (0:ℝ) ρ,∀δ:ℂ,‖δ‖<ρ→∀h:ℝ,1≤h→∀J K:ℕ,K≤J→
        B*((J:ℝ)+1)^2/h≤1/2→8*((K:ℝ)+1)≤h→
        ‖finiteMorseSourceIntegral (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u))
            (fun s u=>d.preMorseAmplitude Q p f s (δ,u)) h (τ/Real.sqrt (Real.sqrt h)) J-
          (Real.sqrt (2*Real.pi):ℂ)*∑j∈Finset.range (K+1),
            gaussianModelCoefficient (fun s u=>d.modelAmplitude Q p f s (δ,u)) j/(h:ℂ)^j‖≤
        A*E^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+
          T*D^(2*(K+1))*Real.exp (-(τ^2/4)*Real.sqrt h) := by
  obtain ⟨W,ρ,R,S,D0,Cw,hρ,hR,hS,hD0,hCw,hρR,hρS,hdata⟩:=
    d.uniform_morse_model_domain Q p f Ω C B hQ hQ0 hΩ hcover hC hB hf hbound
  let A:ℝ:=2*D0*(Real.sqrt (4*Real.pi)+Real.sqrt (2*Real.pi))
  let E:ℝ:=2*max B (4/R^2)
  let T:ℝ:=4*D0*Real.sqrt (8*Real.pi)+4*D0*Cw*ρ^2
  let D:ℝ:=2*max 1 R⁻¹
  have hA:0<A:=by dsimp[A];positivity
  have hE:0<E:=mul_pos (by norm_num) (hB.trans_le (le_max_left _ _))
  have hT:0<T:=by dsimp[T];positivity
  have hD:1≤D:=by dsimp[D];linarith[le_max_left (1:ℝ) R⁻¹]
  refine ⟨ρ,A,E,T,D,hρ,hA,hE,hT,hD,?_⟩
  intro τ hτ δ hδ h hh1 J K hKJ hwin hsmall
  have hh:0<h:=zero_lt_one.trans_le hh1
  have hs1:1≤Real.sqrt h:=by simpa using Real.sqrt_le_sqrt hh1
  have hss1:1≤Real.sqrt (Real.sqrt h):=by simpa using Real.sqrt_le_sqrt hs1
  let r:ℝ:=τ/Real.sqrt (Real.sqrt h)
  have hr:0<r:=by dsimp[r];exact div_pos hτ.1 (by positivity)
  have hrρ:r≤ρ:=(div_le_self hτ.1.le hss1).trans hτ.2
  have hrR:r<R:=(hrρ.trans hρR).trans_lt (half_lt_self hR)
  have hrS:r<S:=hrρ.trans_lt hρS
  obtain ⟨hφ,hU,hmap,hphase,ha,hb,htrans,hbnd,hend⟩:=hdata δ hδ
  obtain ⟨hpq,hnq,hpq4,hnq4,hp,hn,hUp,hUn⟩:=hend r ⟨hr,hrρ⟩
  let ep:ℂ:=W (δ,(r:ℂ))-(r:ℂ)
  let en:ℂ:=W (δ,-(r:ℂ))+(r:ℂ)
  have heP:(r:ℂ)+ep=W (δ,(r:ℂ)):=by dsimp[ep];ring
  have heN:-(r:ℂ)+en=W (δ,-(r:ℂ)):=by dsimp[en];ring
  have hc:=uniform_finite_morse_connector_bound
    (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u)) (fun u:ℂ=>d.U (δ,u))
    (fun s u=>d.preMorseAmplitude Q p f s (δ,u)) (fun s u=>d.modelAmplitude Q p f s (δ,u))
    D0 B Cw h r R S J ep en hD0.le hB.le hCw.le hh hr hrR hrS hφ (fun s hs=>ha s)
    (fun s hs=>(hb s).mono Metric.ball_subset_closedBall) hU hmap
    (fun u hu=>⟨hphase u hu,fun s hs=>htrans s u hu⟩)
    (fun s hs u hu=>hbnd s u (Metric.ball_subset_closedBall hu)) hwin hpq4 hnq4
    (by dsimp only[ep,en];linarith) (by rw[heP];exact hp) (by rw[heN];exact hn)
    (by rw[heP];exact hUp) (by rw[heN];exact hUn)
  have hscalar:4*D0*Cw*Real.sqrt h*r^2=4*D0*Cw*τ^2 := by
    calc _ = 4*D0*Cw*(Real.sqrt h*(τ/Real.sqrt (Real.sqrt h))^2):=by dsimp only[r];ring
         _ = _:=by rw[gaussian_shrinking_cutoff_prefactor τ h hh]
  rw[hscalar] at hc
  have he:=finite_morse_gaussian_remainder_from_connector
    (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u))
    (fun s u=>d.preMorseAmplitude Q p f s (δ,u)) (fun s u=>d.modelAmplitude Q p f s (δ,u))
    D0 B R r h (4*D0*Cw*τ^2) J K hD0.le hB.le hR hr (hrρ.trans hρR) hh hb hbnd hKJ hwin hsmall hc
  have hexp:-(h/4)*r^2=-(τ^2/4)*Real.sqrt h:=by
    dsimp only[r]
    linear_combination -(gaussian_shrinking_radius_exponent τ h hh)
  rw[hexp] at he
  apply he.trans
  change A*E^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+
      (4*D0*Real.sqrt (8*Real.pi)*D^(2*(K+1))+4*D0*Cw*τ^2)*Real.exp (-(τ^2/4)*Real.sqrt h)≤_
  apply add_le_add le_rfl
  have hpD:1≤D^(2*(K+1)):=one_le_pow₀ hD
  have hbase:0≤4*D0*Cw*ρ^2:=by positivity
  have hsmallcoef:4*D0*Cw*τ^2≤4*D0*Cw*ρ^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hτ.1.le hτ.2 2) (by positivity)
  calc _ ≤ (4*D0*Real.sqrt (8*Real.pi)*D^(2*(K+1))+(4*D0*Cw*ρ^2)*D^(2*(K+1)))*Real.exp (-(τ^2/4)*Real.sqrt h):=by
             exact mul_le_mul_of_nonneg_right (add_le_add le_rfl
               (hsmallcoef.trans (le_mul_of_one_le_right hbase hpD))) (Real.exp_pos _).le
       _ = _:=by dsimp only[T];ring
end WP.Analysis



namespace WP.Analysis
lemma CriticalGaussianCoordinateData.uniform_finite_model_gaussian_gevrey_two_all_cutoffs
    (d:CriticalGaussianCoordinateData) (Q:ℂ→ℂ) (p:ℕ) (f:ℕ→ℂ→ℂ)
    (Ω:Set ℂ) (C B:ℝ) (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1)
    (hΩ:IsOpen Ω) (hcover:(y₀:ℂ)∈Ω) (hC:0<C) (hB:0<B)
    (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hbound:∀j z,z∈Ω→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2) :
    ∃ρ A E:ℝ,0<ρ ∧ 0<A ∧ 0<E ∧ ∀τ∈Ioc (0:ℝ) ρ,
      ∃c a H:ℝ,0<c ∧ 0<a ∧ 0<H ∧
      ∀δ:ℂ,‖δ‖<ρ→∀h:ℝ,H≤h→∀J K:ℕ,K≤J→
        2*B*((J:ℝ)+1)^2≤h→(K:ℝ)≤c*Real.sqrt h→
        ‖finiteMorseSourceIntegral (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u))
            (fun s u=>d.preMorseAmplitude Q p f s (δ,u)) h (τ/Real.sqrt (Real.sqrt h)) J-
          (Real.sqrt (2*Real.pi):ℂ)*∑j∈Finset.range (K+1),
            gaussianModelCoefficient (fun s u=>d.modelAmplitude Q p f s (δ,u)) j/(h:ℂ)^j‖≤
        A*E^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+A*Real.exp (-a*Real.sqrt h) := by
  obtain ⟨ρ,A0,E,T,D,hρ,hA0,hE,hT,hD,herror⟩:=
    d.uniform_finite_model_gaussian_error_all_cutoffs Q p f Ω C B hQ hQ0 hΩ hcover hC hB hf hbound
  let A:ℝ:=A0+T*D^2+1
  have hA:0<A:=by dsimp[A];positivity
  have hA0A:A0≤A:=by dsimp[A];have ht:=mul_nonneg hT.le (sq_nonneg D);linarith
  have hTDA:T*D^2≤A:=by dsimp[A];linarith
  refine ⟨ρ,A,E,hρ,hA,hE,?_⟩
  intro τ hτ
  have hτ0:0<τ:=hτ.1
  obtain ⟨c,hc,hc1,hclog⟩:=exists_gaussian_outer_window D (τ^2/4) hD (by positivity)
  refine ⟨c,τ^2/8,256,hc,by positivity,by norm_num,?_⟩
  intro δ hδ h hh J K hKJ hwin hK
  have hh1:1≤h:=by linarith
  have hh0:0<h:=by linarith
  have hsmall:=gaussian_order_small_of_sqrt_window h c K hh hc1 hK
  have hwin':B*((J:ℝ)+1)^2/h≤1/2:=(div_le_iff₀ hh0).mpr (by linarith)
  have he:=herror τ hτ δ hδ h hh1 J K hKJ hwin' hsmall
  have habs:=gaussian_polynomial_outer_exponential_absorption D (τ^2/4) c (Real.sqrt h)
    hD (by positivity) hc.le (Real.sqrt_nonneg h) hclog K hK
  have habs':D^(2*(K+1))*Real.exp (-(τ^2/4)*Real.sqrt h)≤D^2*Real.exp (-(τ^2/8)*Real.sqrt h) := by
    convert habs using 1 <;>ring
  calc _ ≤ A0*E^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+
      T*(D^2*Real.exp (-(τ^2/8)*Real.sqrt h)) :=
        he.trans (add_le_add le_rfl (by rw[mul_assoc];exact mul_le_mul_of_nonneg_left habs' hT.le))
       _ ≤ _:=by
         apply add_le_add
         · exact div_le_div_of_nonneg_right
             (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA0A (pow_nonneg hE.le _)) (sq_nonneg _)) (pow_nonneg hh0.le _)
         · calc _ = (T*D^2)*Real.exp (-(τ^2/8)*Real.sqrt h):=by ring
                _ ≤ _:=mul_le_mul_of_nonneg_right hTDA (Real.exp_pos _).le
end WP.Analysis

namespace WP.Analysis
open Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.original_numerator_uniform_gaussian_gevrey_two_all_cutoffs
    (d:CriticalGaussianCoordinateData) (P:PsiTheory) (p:ℕ) (hp:1≤p)
    (Q:ℂ→ℂ) (Ω:Set ℂ) (f:ℕ→ℂ→ℂ) (C B:ℝ)
    (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ))
    (hΩ:IsOpen Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (hC:0<C) (hB:0<B)
    (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hrest:∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hbound:∀j z,z∈Ω→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2) :
    ∃R ρ A E:ℝ,0<R ∧ R<y₀ ∧ 0<ρ ∧ 0<A ∧ 0<E ∧
      ∀τ∈Ioc (0:ℝ) ρ,∃c a H:ℝ,0<c ∧ 0<a ∧ 0<H ∧
      ∀δ∈Ioo (0:ℝ) R,∀h:ℝ,H≤h→∀J K:ℕ,K≤J→
        2*B*((J:ℝ)+1)^2≤h→(K:ℝ)≤c*Real.sqrt h→
        ‖finiteMorseSourceIntegral (fun u:ℂ=>d.kernel.centeredPhase d.L d.q ((δ:ℂ),u))
            (fun s u=>d.preMorseAmplitude Q p f s ((δ:ℂ),u)) h (τ/Real.sqrt (Real.sqrt h)) J-
          (Real.sqrt (2*Real.pi):ℂ)*∑j∈Finset.range (K+1),
            ((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p (XR (y₀-δ))):ℝ):ℂ)/(h:ℂ)^j‖≤
        A*E^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+A*Real.exp (-a*Real.sqrt h) := by
  obtain ⟨ρ,A,E,hρ,hA,hE,herror⟩:=
    d.uniform_finite_model_gaussian_gevrey_two_all_cutoffs Q p f Ω C B hQ hQ0 hΩ
      (hcover _ ⟨y₀_pos.le,le_rfl⟩) hC hB hf hbound
  obtain ⟨Rm,hRm,hRmy,hraw⟩:=d.original_raw_coefficients_eq_critical_model P p hp Q f Ω hΩ
    (hcover _ ⟨y₀_pos.le,le_rfl⟩) hQ hQ0 hQphys hf hrest
  let R:ℝ:=min ρ Rm/2
  have hR:0<R:=half_pos (lt_min hρ hRm)
  have hRρ:R<ρ:=(half_lt_self (lt_min hρ hRm)).trans_le (min_le_left _ _)
  have hRRm:R<Rm:=(half_lt_self (lt_min hρ hRm)).trans_le (min_le_right _ _)
  refine ⟨R,ρ,A,E,hR,hRRm.trans hRmy,hρ,hA,hE,?_⟩
  intro τ hτ
  obtain ⟨c,a,H,hc,ha,hH,he⟩:=herror τ hτ
  refine ⟨c,a,H,hc,ha,hH,?_⟩
  intro δ hδ h hh J K hKJ hwin hK
  have hδρ:‖(δ:ℂ)‖<ρ:=by rw[Complex.norm_of_nonneg hδ.1.le];exact hδ.2.trans hRρ
  have hpoly:(∑j∈Finset.range (K+1),
      ((PowerSeries.coeff (2*j) (HigherOrder.extractionNumerator P p (XR (y₀-δ))):ℝ):ℂ)/(h:ℂ)^j)=
      ∑j∈Finset.range (K+1),gaussianModelCoefficient (fun s u=>d.modelAmplitude Q p f s ((δ:ℂ),u)) j/(h:ℂ)^j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw[(hraw δ ⟨hδ.1,hδ.2.trans hRRm⟩ j).1]
  rw[hpoly]
  exact he (δ:ℂ) hδρ h hh J K hKJ hwin hK
end WP.Analysis
