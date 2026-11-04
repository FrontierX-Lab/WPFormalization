import WPFormalization.Analysis.LogScaleVariation
import WPFormalization.Volumes.TransportPrimitive
import WPFormalization.Volumes.TransportProof
import WPFormalization.Analysis.ZCriticalScale
import WPFormalization.Marked.LogGrowth

/-! Genuine integration of the marked logarithmic transport error.
The actual Phi and comparison model give f = log(pi*F/model). The proved
transport equation and log Z derivative imply an exact variation estimate.
At B = y₀-h⁻² the actual critical scale of Z yields O(log(g+1)/g), uniformly
for every Y ≤ B. The final assembly lemmas explicitly take a short-window
log anchor; they do not assert that anchor or register it as external.
Once the genuine endpoint proof supplies it, the original global relative
prefactor bound follows by monotonicity, the two intervals, and exponentiation. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma A_continuousOn_closed_parameter : ContinuousOn A (Icc (0:ℝ) y₀) := by
  apply continuousOn_iff_continuous_restrict.mpr
  unfold A
  exact (Complex.continuous_re.comp (barH_joint_continuous.comp
    (continuous_id.prodMk continuous_const))).div_const 3
lemma total_weight_continuousOn_parameter :
    ContinuousOn (fun Y => ∑'l : ℕ,weight Y l) (Ico (0:ℝ) y₀) := by
  have hT : ContinuousOn (deriv T) (Ico (0:ℝ) y₀) := fun Y hY =>
    (T_analyticAt_interior Y hY).deriv.continuousAt.continuousWithinAt
  exact (hT.const_mul (-2:ℝ)).congr (fun Y hY => Theta_eq_neg_two_T_deriv Y hY)
lemma Z_continuousOn_parameter : ContinuousOn Z (Ico (0:ℝ) y₀) := by
  have hr : ContinuousOn r (Ico (0:ℝ) y₀) := continuousOn_iff_continuous_restrict.mpr r_continuous_interior
  have hp : ContinuousOn (fun Y => Real.rpow (r Y) (3/2:ℝ)) (Ico (0:ℝ) y₀) := by
    simpa only [Real.rpow_eq_pow] using hr.rpow_const (p := (3/2:ℝ)) (fun Y hY => Or.inr (by norm_num))
  exact ((A_continuousOn_closed_parameter.mono Ico_subset_Icc_self).mul a_continuous.continuousOn).mul hp
lemma logZ_continuousOn_parameter : ContinuousOn (fun Y => Real.log (Z Y)) (Ico (0:ℝ) y₀) :=
  Z_continuousOn_parameter.log (fun Y hY => (marked_Z_pos Y hY).ne')
lemma logZ_hasDerivAt_open_parameter (Y : ℝ) (hY : Y ∈ Ioo (0:ℝ) y₀) :
    HasDerivAt (fun Y => Real.log (Z Y)) (-1/(A Y*r Y)) Y := by
  simpa only [Z] using logNormalizedAction_hasDerivAt_open_parameter Y hY
end WP.Analysis
namespace WP

def prefactorLogError (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  Real.log (Real.pi*markedF P g p (XR Y)/markedModel g p Y)

lemma markedModel_continuousOn_parameter (g p : ℕ) :
    ContinuousOn (markedModel g p) (Ico (0:ℝ) y₀) := by
  have hA := Analysis.A_continuousOn_closed_parameter.mono Ico_subset_Icc_self
  have hΘ : ContinuousOn Theta (Ico (0:ℝ) y₀) := Analysis.total_weight_continuousOn_parameter
  have hr : ContinuousOn r (Ico (0:ℝ) y₀) :=
    continuousOn_iff_continuous_restrict.mpr Analysis.r_continuous_interior
  have hp : ContinuousOn (fun Y => Real.rpow (r Y) ((p:ℝ)/2)) (Ico (0:ℝ) y₀) := by
    simpa only [Real.rpow_eq_pow] using hr.rpow_const (p := ((p:ℝ)/2))
      (fun Y hY => Or.inr (by positivity))
  exact (((continuousOn_const.mul ((Analysis.Z_continuousOn_parameter.inv₀
    (fun Y hY => (Analysis.marked_Z_pos Y hY).ne')).pow (complexity g p))).mul hp).mul
      (hA.mul hΘ).sqrt)

lemma prefactorLogError_continuousOn_parameter (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p)
    (hs : Stable g p) : ContinuousOn (prefactorLogError P g p) (Ico (0:ℝ) y₀) := by
  have hF : ContinuousOn (fun Y => markedF P g p (XR Y)) (Ico (0:ℝ) y₀) :=
    fun Y hY => (markedF_parameter_hasDerivAt P g p Y hY).continuousAt.continuousWithinAt
  exact ((hF.const_mul Real.pi).div (markedModel_continuousOn_parameter g p)
    (fun Y hY => (markedModel_pos_parameter g p hs Y hY).ne')).log
      (fun Y hY => (div_pos (mul_pos Real.pi_pos (markedF_pos_parameter P g p hp hs Y hY))
        (markedModel_pos_parameter g p hs Y hY)).ne')

lemma prefactorLogError_hasDerivAt (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (hs : Stable g p)
    (Y : ℝ) (hY : Y ∈ Ioo (0:ℝ) y₀) :
    HasDerivAt (prefactorLogError P g p)
      ((A Y*r Y*deriv (fun t => Real.log (markedF P g p (XR t))) Y-
        ((complexity g p:ℝ)+transportBeta p Y))/(A Y*r Y)) Y := by
  have hYi : Y ∈ Ico (0:ℝ) y₀ := ⟨hY.1.le,hY.2⟩
  have hF := markedF_parameter_log_hasDerivAt P g p hp hs Y hYi
  have hM := Analysis.markedModel_log_hasDerivAt_open_parameter g p hs Y hY
  have hd := ((hasDerivAt_const Y (Real.log Real.pi)).add hF).sub hM
  have he : prefactorLogError P g p =ᶠ[𝓝 Y]
      (fun t => Real.log Real.pi+Real.log (markedF P g p (XR t))-Real.log (markedModel g p t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hY] with t ht
    have hFpos := markedF_pos_parameter P g p hp hs t ⟨ht.1.le,ht.2⟩
    have hMpos := markedModel_pos_parameter g p hs t ⟨ht.1.le,ht.2⟩
    exact (Real.log_div (mul_ne_zero Real.pi_ne_zero hFpos.ne') hMpos.ne').trans
      (by rw [Real.log_mul Real.pi_ne_zero hFpos.ne'])
  convert hd.congr_of_eventuallyEq he using 1
  rw [hF.deriv]
  unfold transportBeta
  field_simp [(Analysis.marked_A_pos Y ⟨hY.1.le,hY.2.le⟩).ne',(r_pos Y hYi).ne'] <;> ring

lemma prefactorLogError_deriv_bound (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0 < C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y ∈ Ioo (0:ℝ) y₀,
      |deriv (prefactorLogError P g p) Y| ≤ C/((complexity g p:ℝ)*A Y*r Y) := by
  obtain ⟨C,hC,G,hb⟩ := transport_equation_proof P p hp
  refine ⟨C,hC,max G 2,?_⟩
  intro g hg Y hY
  have hs : Stable g p := by unfold Stable;omega
  have hYi : Y ∈ Ico (0:ℝ) y₀ := ⟨hY.1.le,hY.2⟩
  have hAr := mul_pos (Analysis.marked_A_pos Y ⟨hY.1.le,hY.2.le⟩) (r_pos Y hYi)
  rw [(prefactorLogError_hasDerivAt P g p hp hs Y hY).deriv,abs_div,abs_of_pos hAr]
  calc
    _ ≤ (C/(complexity g p:ℝ))/(A Y*r Y) :=
      div_le_div_of_nonneg_right (hb g (by omega) Y hYi) hAr.le
    _ = _ := by ring
end WP
namespace WP
lemma prefactorLogError_variation (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0 < C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y ∈ Ico (0:ℝ) y₀,
      ∀ B ∈ Ico (0:ℝ) y₀,Y ≤ B →
      |prefactorLogError P g p Y-prefactorLogError P g p B| ≤
        C/(complexity g p:ℝ)*(Real.log (Z Y)-Real.log (Z B)) := by
  obtain ⟨C,hC,G,hb⟩ := prefactorLogError_deriv_bound P p hp
  refine ⟨C,hC,max G 2,?_⟩
  intro g hg Y hY B hB hYB
  have hs : Stable g p := by unfold Stable;omega
  have hsub : Icc Y B ⊆ Ico (0:ℝ) y₀ := fun x hx => ⟨hY.1.trans hx.1,hx.2.trans_lt hB.2⟩
  have hmem (x : ℝ) (hx : x ∈ Ioo Y B) : x ∈ Ioo (0:ℝ) y₀ :=
    ⟨hY.1.trans_lt hx.1,hx.2.trans hB.2⟩
  rw [abs_sub_comm]
  apply Analysis.log_scale_variation_bound (prefactorLogError P g p) (fun x => Real.log (Z x))
    Y B (C/(complexity g p:ℝ)) hYB
    ((prefactorLogError_continuousOn_parameter P g p hp hs).mono hsub)
    (Analysis.logZ_continuousOn_parameter.mono hsub)
  · exact fun x hx => (prefactorLogError_hasDerivAt P g p hp hs x (hmem x hx)).differentiableAt
  · exact fun x hx => (Analysis.logZ_hasDerivAt_open_parameter x (hmem x hx)).differentiableAt
  · intro x hx
    rw [(Analysis.logZ_hasDerivAt_open_parameter x (hmem x hx)).deriv]
    convert hb g (by omega) x (hmem x hx) using 1 <;> ring
end WP
namespace WP.Analysis
lemma logZ_antitoneOn_parameter : AntitoneOn (fun Y => Real.log (Z Y)) (Ico (0:ℝ) y₀) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ico 0 y₀) logZ_continuousOn_parameter
  · intro Y hY
    rw [interior_Ico] at hY
    exact (logZ_hasDerivAt_open_parameter Y hY).differentiableAt.differentiableWithinAt
  · intro Y hY
    rw [interior_Ico] at hY
    rw [(logZ_hasDerivAt_open_parameter Y hY).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_pos (marked_A_pos Y ⟨hY.1.le,hY.2.le⟩) (r_pos Y ⟨hY.1.le,hY.2⟩)).le
lemma logZ_le_zero_parameter (Y : ℝ) (hY : Y ∈ Ico (0:ℝ) y₀) :
    Real.log (Z Y) ≤ Real.log (Z 0) :=
  logZ_antitoneOn_parameter ⟨le_rfl,y₀_pos⟩ hY hY.1
end WP.Analysis
namespace WP.Analysis
lemma complexity_log_bound (g p : ℕ) (hg : 2 ≤ g) :
    Real.log (complexity g p:ℝ) ≤ Real.log ((p:ℝ)+2)+Real.log ((g:ℝ)+1) := by
  have hh : 0 < (complexity g p:ℝ) := by
    exact_mod_cast (show 0 < complexity g p by unfold complexity;omega)
  have hNat : complexity g p ≤ (p+2)*(g+1) := by
    have h₁ : complexity g p ≤ 2*g+p := Nat.sub_le _ _
    nlinarith [Nat.zero_le (p*g)]
  have hbound : (complexity g p:ℝ) ≤ ((p:ℝ)+2)*((g:ℝ)+1) := by exact_mod_cast hNat
  exact (Real.log_le_log hh hbound).trans_eq (Real.log_mul (by positivity) (by positivity))
end WP.Analysis
namespace WP
lemma prefactorLogError_long_interval (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0 < C ∧ ∃ G : ℕ,∀ g ≥ G,
      let h : ℝ := complexity g p
      let B : ℝ := y₀-(h⁻¹)^2
      B ∈ Ico (0:ℝ) y₀ ∧ ∀ Y ∈ Ico (0:ℝ) y₀,Y ≤ B →
        |prefactorLogError P g p Y-prefactorLogError P g p B| ≤ C*Real.log ((g:ℝ)+1)/(g:ℝ) := by
  obtain ⟨C,hC,G,hvar⟩ := prefactorLogError_variation P p hp
  obtain ⟨M,δ,hM,hδ,hlog⟩ := Analysis.Z_critical_log_bound
  have hδtendsto : Tendsto (fun g : ℕ => ((complexity g p:ℝ)⁻¹)^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0),Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (Analysis.complexity_real_tendsto_atTop p)).pow 2
  have heδ := hδtendsto.eventually (eventually_lt_nhds (lt_min hδ y₀_pos))
  obtain ⟨Gδ,hsmall⟩ := eventually_atTop.mp heδ
  let q : ℝ := Real.log 2
  have hq : 0 < q := Real.log_pos (by norm_num)
  let N : ℝ := |Real.log (Z 0)|+M+5*Real.log ((p:ℝ)+2)
  have hN : 0 < N := by
    have hl : 0 ≤ Real.log ((p:ℝ)+2) := Real.log_nonneg (by have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p;linarith)
    dsimp [N]
    positivity
  let D : ℝ := N/q+5
  have hD : 0 < D := by dsimp [D];positivity
  refine ⟨C*D,mul_pos hC hD,max (max G Gδ) 2,?_⟩
  intro g hg
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  have hgG : G ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans hg)
  have hgδ : Gδ ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans hg)
  have hhNat : g ≤ complexity g p := by unfold complexity;omega
  have hhg : (g:ℝ) ≤ (complexity g p:ℝ) := by exact_mod_cast hhNat
  have hgp : (0:ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hhp : 0 < (complexity g p:ℝ) := hgp.trans_le hhg
  let h : ℝ := complexity g p
  let B : ℝ := y₀-(h⁻¹)^2
  have hbδ : (h⁻¹)^2 < min δ y₀ := hsmall g hgδ
  have hpow : 0 < (h⁻¹)^2 := sq_pos_of_pos (inv_pos.mpr hhp)
  have hB : B ∈ Ico (0:ℝ) y₀ := by
    dsimp [B]
    exact ⟨(sub_pos.mpr (hbδ.trans_le (min_le_right _ _))).le,sub_lt_self _ hpow⟩
  refine ⟨hB,?_⟩
  intro Y hY hYB
  have hlogB := hlog B hB (by dsimp [B];linarith [hbδ.trans_le (min_le_left _ _)])
  have hδlog : Real.log (y₀-B) = -2*Real.log h := by
    dsimp [B]
    rw [show y₀-(y₀-(h⁻¹)^2)=(h⁻¹)^2 by ring,Real.log_pow,Real.log_inv]
    ring
  rw [hδlog] at hlogB
  have hZgap : Real.log (Z Y)-Real.log (Z B) ≤ D*Real.log ((g:ℝ)+1) := by
    have hzY := Analysis.logZ_le_zero_parameter Y hY
    have hlogh := Analysis.complexity_log_bound g p hg2
    have hqL : q ≤ Real.log ((g:ℝ)+1) := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ g+1))
    have hNL : N ≤ (N/q)*Real.log ((g:ℝ)+1) := by
      have ht := mul_le_mul_of_nonneg_left hqL (div_pos hN hq).le
      rwa [div_mul_cancel₀ N hq.ne'] at ht
    have hlower : -M ≤ Real.log (Z B)+5*Real.log h := by
      have he := (abs_le.mp hlogB).1
      linarith
    have hfirst : Real.log (Z Y)-Real.log (Z B) ≤ N+5*Real.log ((g:ℝ)+1) := by
      dsimp [N]
      change Real.log h ≤ _ at hlogh
      linarith [le_abs_self (Real.log (Z 0))]
    dsimp [D]
    nlinarith
  calc
    _ ≤ C/h*(Real.log (Z Y)-Real.log (Z B)) := hvar g hgG Y hY B hB hYB
    _ ≤ C/h*(D*Real.log ((g:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hZgap (div_pos hC hhp).le
    _ ≤ C*D*Real.log ((g:ℝ)+1)/(g:ℝ) := by
      have hlg : 0 ≤ Real.log ((g:ℝ)+1) := Real.log_nonneg (by have hg0 : (0:ℝ) ≤ g := Nat.cast_nonneg g;linarith)
      have hhInv : h⁻¹ ≤ (g:ℝ)⁻¹ := inv_anti₀ hgp hhg
      have ht := mul_le_mul_of_nonneg_left hhInv (mul_nonneg (mul_pos hC hD).le hlg)
      convert ht using 1 <;> ring
end WP
namespace WP
lemma prefactorLogError_uniform_of_endpoint_anchor (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (hanchor : ∃ C : ℝ,0 < C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y ∈ Ico (0:ℝ) y₀,
      y₀-Y ≤ ((complexity g p:ℝ)⁻¹)^2 → |prefactorLogError P g p Y| ≤ C/(g:ℝ)) :
    ∃ C : ℝ,0 < C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y ∈ Ico (0:ℝ) y₀,
      |prefactorLogError P g p Y| ≤ C*Real.log ((g:ℝ)+1)/(g:ℝ) := by
  obtain ⟨Cv,hCv,Gv,hv⟩ := prefactorLogError_long_interval P p hp
  obtain ⟨Ca,hCa,Ga,ha⟩ := hanchor
  let q : ℝ := Real.log 2
  have hq : 0 < q := Real.log_pos (by norm_num)
  refine ⟨Cv+Ca/q,by positivity,max (max Gv Ga) 2,?_⟩
  intro g hg Y hY
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  have hgV : Gv ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans hg)
  have hgA : Ga ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans hg)
  have hgp : (0:ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hlpos : 0 ≤ Real.log ((g:ℝ)+1) := Real.log_nonneg (by have h : (0:ℝ) ≤ g := Nat.cast_nonneg g;linarith)
  have hqL : q ≤ Real.log ((g:ℝ)+1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ g+1))
  have hca : Ca ≤ Ca/q*Real.log ((g:ℝ)+1) := by
    have h := mul_le_mul_of_nonneg_left hqL (div_pos hCa hq).le
    rwa [div_mul_cancel₀ Ca hq.ne'] at h
  let B : ℝ := y₀-((complexity g p:ℝ)⁻¹)^2
  have hb := hv g hgV
  change B ∈ Ico (0:ℝ) y₀ ∧ ∀ Y ∈ Ico (0:ℝ) y₀,Y ≤ B →
    |prefactorLogError P g p Y-prefactorLogError P g p B| ≤ Cv*Real.log ((g:ℝ)+1)/(g:ℝ) at hb
  have hpoint : |prefactorLogError P g p Y| ≤ Cv*Real.log ((g:ℝ)+1)/(g:ℝ)+Ca/(g:ℝ) := by
    by_cases hYB : Y ≤ B
    · have hBδ : y₀-B ≤ ((complexity g p:ℝ)⁻¹)^2 := by dsimp [B];linarith
      have hBa := ha g hgA B hb.1 hBδ
      calc
        _ = |(prefactorLogError P g p Y-prefactorLogError P g p B)+prefactorLogError P g p B| := by congr 1;ring
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hb.2 Y hY hYB) hBa)
    · have hδ : y₀-Y ≤ ((complexity g p:ℝ)⁻¹)^2 := by dsimp [B] at hYB;linarith
      exact (ha g hgA Y hY hδ).trans (le_add_of_nonneg_left (div_nonneg (mul_nonneg hCv.le hlpos) hgp.le))
  calc
    _ ≤ _ := hpoint
    _ = (Cv*Real.log ((g:ℝ)+1)+Ca)/(g:ℝ) := by ring
    _ ≤ ((Cv+Ca/q)*Real.log ((g:ℝ)+1))/(g:ℝ) := by
      apply div_le_div_of_nonneg_right _ hgp.le
      nlinarith

lemma absolute_prefactor_of_log_anchor (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (hanchor : ∃ C : ℝ,0 < C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y ∈ Ico (0:ℝ) y₀,
      y₀-Y ≤ ((complexity g p:ℝ)⁻¹)^2 → |prefactorLogError P g p Y| ≤ C/(g:ℝ)) :
    ∃ C : ℝ,0 < C ∧ ∃ G : ℕ,∀ g ≥ G,∀ Y ∈ Ico (0:ℝ) y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y-1| ≤ C*Real.log ((g:ℝ)+1)/(g:ℝ) := by
  obtain ⟨C,hC,G,hlog⟩ := prefactorLogError_uniform_of_endpoint_anchor P p hp hanchor
  have ht0 : Tendsto (fun g : ℕ => Real.log ((g:ℝ)+1)/(g:ℝ)) atTop (𝓝 (0:ℝ)) := by
    have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def,pow_one,one_mul,add_neg_cancel_right] using ht
  have ht := ht0.const_mul C
  simp only [mul_zero] at ht
  obtain ⟨G₁,hsmall⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)))
  refine ⟨2*C,by positivity,max (max G G₁) 2,?_⟩
  intro g hg Y hY
  have hgG : G ≤ g := (le_max_left _ _).trans ((le_max_left _ _).trans hg)
  have hg₁ : G₁ ≤ g := (le_max_right _ _).trans ((le_max_left _ _).trans hg)
  have hs : Stable g p := by unfold Stable;omega
  have hR : 0 < Real.pi*markedF P g p (XR Y)/markedModel g p Y :=
    div_pos (mul_pos Real.pi_pos (markedF_pos_parameter P g p hp hs Y hY))
      (markedModel_pos_parameter g p hs Y hY)
  have hlogbound := hlog g hgG Y hY
  have hlogsmall : |prefactorLogError P g p Y| ≤ 1 := by
    have hh := hsmall g hg₁
    have he : C*Real.log ((g:ℝ)+1)/(g:ℝ) = C*(Real.log ((g:ℝ)+1)/(g:ℝ)) := by ring
    rw [he] at hlogbound
    exact hlogbound.trans hh.le
  have he := Real.abs_exp_sub_one_le hlogsmall
  rw [prefactorLogError,Real.exp_log hR] at he
  calc
    _ ≤ 2*|prefactorLogError P g p Y| := he
    _ ≤ 2*(C*Real.log ((g:ℝ)+1)/(g:ℝ)) := mul_le_mul_of_nonneg_left hlogbound (by norm_num)
    _ = _ := by ring
end WP
