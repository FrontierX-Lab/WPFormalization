import WPFormalization.Analysis.NormalizedMorseModelDomain
import WPFormalization.Analysis.UniformMorseFiniteModel
/-! The common normalized Morse domain gives a uniform all-order Gaussian error for the literal finite source model. The native amplitude budget, all smaller shrinking cutoffs and the supplied coefficient family are retained; no extraction coefficient identity or actual generating-function comparison is assumed. -/
noncomputable section
namespace WP.Analysis
open Set MeasureTheory
lemma NormalizedMorseModelDomain.gaussian_error_all_cutoffs
    {F a y : ℂ × ℂ → ℂ} {f : ℕ → ℂ → ℂ} {B : ℝ}
    (d : NormalizedMorseModelDomain F a y f B) (hB : 0 < B) :
    ∃ A E T D : ℝ, 0 < A ∧ 0 < E ∧ 0 < T ∧ 1 ≤ D ∧
      ∀ τ ∈ Ioc (0 : ℝ) d.rho, ∀ δ : ℂ, ‖δ‖ < d.rho →
      ∀ h : ℝ, 1 ≤ h → ∀ J K : ℕ, K ≤ J →
        B * ((J : ℝ) + 1)^2 / h ≤ 1/2 → 8 * ((K : ℝ) + 1) ≤ h →
        ‖finiteMorseSourceIntegral (fun u : ℂ => F (δ,u))
            (fun s u => morseSourceAmplitude a y f s (δ,u)) h (τ / Real.sqrt (Real.sqrt h)) J -
          (Real.sqrt (2*Real.pi) : ℂ) * ∑ j ∈ Finset.range (K+1),
            gaussianModelCoefficient (fun s u => morseTransformedAmplitude a y f d.U s (δ,u)) j / (h : ℂ)^j‖ ≤
          A * E^(K+1) * ((K+1).factorial : ℝ)^2 / h^(K+1) +
            T * D^(2*(K+1)) * Real.exp (-(τ^2/4)*Real.sqrt h) := by
  let ρ := d.rho
  let R := d.R
  let S := d.S
  let D0 := d.D
  let Cw := d.Cw
  have hρ : 0 < ρ := d.rho_pos
  have hR : 0 < R := d.R_pos
  have hS : 0 < S := d.S_pos
  have hD0 : 0 < D0 := d.D_pos
  have hCw : 0 < Cw := d.Cw_pos
  have hρR : ρ ≤ R/2 := d.rho_R
  have hρS : ρ < S := d.rho_S
  let A:ℝ:=2*D0*(Real.sqrt (4*Real.pi)+Real.sqrt (2*Real.pi))
  let E:ℝ:=2*max B (4/R^2)
  let T:ℝ:=4*D0*Real.sqrt (8*Real.pi)+4*D0*Cw*ρ^2
  let D:ℝ:=2*max 1 R⁻¹
  have hA:0<A:=by dsimp[A];positivity
  have hE:0<E:=mul_pos (by norm_num) (hB.trans_le (le_max_left _ _))
  have hT:0<T:=by dsimp[T];positivity
  have hD:1≤D:=by dsimp[D];linarith[le_max_left (1:ℝ) R⁻¹]
  refine ⟨A,E,T,D,hA,hE,hT,hD,?_⟩
  intro τ hτ δ hδ h hh1 J K hKJ hwin hsmall
  have hh:0<h:=zero_lt_one.trans_le hh1
  have hs1:1≤Real.sqrt h:=by simpa using Real.sqrt_le_sqrt hh1
  have hss1:1≤Real.sqrt (Real.sqrt h):=by simpa using Real.sqrt_le_sqrt hs1
  let r:ℝ:=τ/Real.sqrt (Real.sqrt h)
  have hr:0<r:=by dsimp[r];exact div_pos hτ.1 (by positivity)
  have hrρ:r≤ρ:=(div_le_self hτ.1.le hss1).trans hτ.2
  have hrR:r<R:=(hrρ.trans hρR).trans_lt (half_lt_self hR)
  have hrS:r<S:=hrρ.trans_lt hρS
  have hφ := d.phase_diff δ hδ
  have hU := d.U_diff δ hδ
  have hmap := d.maps δ hδ
  have hphase := d.quadratic δ hδ
  have ha := d.pre_diff δ hδ
  have hb := d.post_diff δ hδ
  have htrans := d.transform δ hδ
  have hbnd := d.bound δ hδ
  have hend := d.endpoints δ hδ
  obtain ⟨hpq,hnq,hpq4,hnq4,hp,hn,hUp,hUn⟩:=hend r ⟨hr,hrρ⟩
  let ep:ℂ:=d.W (δ,(r:ℂ))-(r:ℂ)
  let en:ℂ:=d.W (δ,-(r:ℂ))+(r:ℂ)
  have heP:(r:ℂ)+ep=d.W (δ,(r:ℂ)):=by dsimp[ep];ring
  have heN:-(r:ℂ)+en=d.W (δ,-(r:ℂ)):=by dsimp[en];ring
  have hc:=uniform_finite_morse_connector_bound
    (fun u:ℂ=>F (δ,u)) (fun u:ℂ=>d.U (δ,u))
    (fun s u=>morseSourceAmplitude a y f s (δ,u)) (fun s u=>morseTransformedAmplitude a y f d.U s (δ,u))
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
    (fun u:ℂ=>F (δ,u))
    (fun s u=>morseSourceAmplitude a y f s (δ,u)) (fun s u=>morseTransformedAmplitude a y f d.U s (δ,u))
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
open Set MeasureTheory
lemma normalized_morse_exists_outer_window (D a:ℝ) (hD:1≤D) (ha:0<a) :
    ∃c:ℝ,0<c ∧ c≤1 ∧ 2*c*Real.log D≤a/2 := by
  have hlog:0≤Real.log D:=Real.log_nonneg hD
  let c:ℝ:=min 1 (a/(8*(Real.log D+1)))
  have hc:0<c:=lt_min zero_lt_one (div_pos ha (by positivity))
  have hc1:c≤1:=min_le_left _ _
  have hcr:c≤a/(8*(Real.log D+1)):=min_le_right _ _
  have hmul:c*(8*(Real.log D+1))≤a:=(le_div_iff₀ (by positivity)).mp hcr
  exact ⟨c,hc,hc1,by nlinarith[mul_nonneg hc.le hlog]⟩

lemma normalized_morse_order_small_of_sqrt_window (h c:ℝ) (K:ℕ)
    (hh:256≤h) (hc:c≤1) (hK:(K:ℝ)≤c*Real.sqrt h) :
    8*((K:ℝ)+1)≤h := by
  have hh0:0≤h:=by linarith
  have hs:0≤Real.sqrt h:=Real.sqrt_nonneg h
  have hs16:16≤Real.sqrt h:=by
    have he:=Real.sqrt_le_sqrt hh
    norm_num at he
    exact he
  have hK':(K:ℝ)≤Real.sqrt h:=hK.trans (mul_le_of_le_one_left hs hc)
  have hsq:=Real.sq_sqrt hh0
  nlinarith

lemma NormalizedMorseModelDomain.gaussian_gevrey_two_all_cutoffs
    {F a y : ℂ × ℂ → ℂ} {f : ℕ → ℂ → ℂ} {B : ℝ}
    (d : NormalizedMorseModelDomain F a y f B) (hB : 0 < B) :
    ∃ A E : ℝ, 0 < A ∧ 0 < E ∧
      ∀ τ ∈ Ioc (0 : ℝ) d.rho, ∃ c b H : ℝ, 0 < c ∧ 0 < b ∧ 0 < H ∧
      ∀ δ : ℂ, ‖δ‖ < d.rho → ∀ h : ℝ, H ≤ h → ∀ J K : ℕ, K ≤ J →
        2 * B * ((J : ℝ) + 1)^2 ≤ h → (K : ℝ) ≤ c * Real.sqrt h →
        ‖finiteMorseSourceIntegral (fun u : ℂ => F (δ,u))
            (fun s u => morseSourceAmplitude a y f s (δ,u)) h (τ / Real.sqrt (Real.sqrt h)) J -
          (Real.sqrt (2*Real.pi) : ℂ) * ∑ j ∈ Finset.range (K+1),
            gaussianModelCoefficient (fun s u => morseTransformedAmplitude a y f d.U s (δ,u)) j / (h : ℂ)^j‖ ≤
          A * E^(K+1) * ((K+1).factorial : ℝ)^2 / h^(K+1) +
            A * Real.exp (-b*Real.sqrt h) := by
  obtain ⟨A0,E,T,D,hA0,hE,hT,hD,herror⟩ := d.gaussian_error_all_cutoffs hB
  let A:ℝ:=A0+T*D^2+1
  have hA:0<A:=by dsimp[A];positivity
  have hA0A:A0≤A:=by dsimp[A];have ht:=mul_nonneg hT.le (sq_nonneg D);linarith
  have hTDA:T*D^2≤A:=by dsimp[A];linarith
  refine ⟨A,E,hA,hE,?_⟩
  intro τ hτ
  have hτ0:0<τ:=hτ.1
  obtain ⟨c,hc,hc1,hclog⟩:=normalized_morse_exists_outer_window D (τ^2/4) hD (by positivity)
  refine ⟨c,τ^2/8,256,hc,by positivity,by norm_num,?_⟩
  intro δ hδ h hh J K hKJ hwin hK
  have hh1:1≤h:=by linarith
  have hh0:0<h:=by linarith
  have hsmall:=normalized_morse_order_small_of_sqrt_window h c K hh hc1 hK
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
