import WPFormalization.Volumes.PointMassFourier
import WPFormalization.Volumes.PointMassOuter
import WPFormalization.Volumes.PointMassVariance
import WPFormalization.Volumes.PointMassCompactIntegral
noncomputable section
namespace WP.PositiveConvolution
open Set MeasureTheory
lemma critical_character_integral_scaled_bound_of_arc (P:PsiTheory) (c₀:ℝ) (hc:0<c₀)
    (harc:∃δ εA:ℝ,0<δ∧0<εA∧∀ε∈Ioo 0 εA,∀θ∈Icc (-Real.pi) Real.pi,
      |θ|≤δ→‖universalV P ((xCritical*(1-ε):ℝ)*Complex.exp ((θ:ℂ)*Complex.I))/
        universalV P ((xCritical*(1-ε):ℝ):ℂ)‖≤(1+θ^2/(4*ε^2))^(-1/8:ℝ)):
    ∃ε0 C:ℝ,0<ε0∧ε0≤1/2∧0<C∧∀h H:ℕ,1≤h→16≤H→c₀*(h:ℝ)≤H→
      ∀ε∈Ioo 0 ε0,
      (∫θ:ℝ in (-Real.pi)..Real.pi,
        ‖universalV P ((xCritical*(1-ε):ℝ)*Complex.exp ((θ:ℂ)*Complex.I))/
          universalV P ((xCritical*(1-ε):ℝ):ℂ)‖^H)*
            Real.sqrt ((h:ℝ)*euler Psi (xCritical*(1-ε)))≤C:=by
  obtain ⟨δ,εA,hδ,hεA,hArc⟩:=harc
  obtain ⟨C0,εO,hC0,hεO,hεOhalf,hOut⟩:=universalV_outer_relative_bound P δ hδ
  obtain ⟨εV,hεV,hVar⟩:=eulerPsi_critical_upper
  let ε0:ℝ:=min εA (min εO (min εV (min (1/(4*C0^2)) (1/2))))
  have hε0:0<ε0:=by dsimp[ε0];positivity
  have h0A:ε0≤εA:=min_le_left _ _
  have h0O:ε0≤εO:=(min_le_right _ _).trans (min_le_left _ _)
  have h0V:ε0≤εV:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h0C:ε0≤1/(4*C0^2):=(min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h0half:ε0≤1/2:=(min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let K:ℝ:=8*Real.pi+8*Real.pi*C0^2
  have hK:0<K:=by dsimp[K];positivity
  refine ⟨ε0,K*Real.sqrt (2/c₀),hε0,h0half,mul_pos hK (Real.sqrt_pos.mpr (by positivity)),?_⟩
  intro h H hh hH hrel ε hε
  let x:ℝ:=xCritical*(1-ε)
  have hx:x∈Ioo 0 xCritical:=by
    have hhalf:ε<1/2:=hε.2.trans_le h0half
    dsimp[x]
    constructor
    · exact mul_pos Analysis.xCritical_pos_parameter (by linarith)
    · nlinarith[mul_pos Analysis.xCritical_pos_parameter hε.1]
  have hcf:Continuous (fun θ:ℝ=>
      ‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖^H):=
    (((universalV_circle_continuous P x hx).div_const _).norm.pow H)
  have hq:C0*Real.sqrt ε≤1/2:=by
    have he:ε≤1/(4*C0^2):=hε.2.le.trans h0C
    have hh:ε*(4*C0^2)≤1:=(le_div_iff₀ (by positivity)).mp he
    have hs:(C0*Real.sqrt ε)^2=C0^2*ε:=by rw[mul_pow,Real.sq_sqrt hε.1.le]
    have hp:0≤C0*Real.sqrt ε:=mul_nonneg hC0.le (Real.sqrt_nonneg _)
    nlinarith
  have hI:=critical_circle_integral_bound _ hcf H ε δ C0 hH hε.1 hC0.le hq
    (fun θ hθ hnear=>by
      have hb:=hArc ε ⟨hε.1,hε.2.trans_le h0A⟩ θ hθ hnear
      have hp:=pow_le_pow_left₀ (norm_nonneg _) hb H
      calc
        _ ≤ ((1+θ^2/(4*ε^2))^(-1/8:ℝ))^H:=hp
        _ = (1+θ^2/(4*ε^2))^(-(H:ℝ)/8:ℝ):=by
          rw[←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
          congr 1
          ring)
    (fun θ hθ houter=>pow_le_pow_left₀ (norm_nonneg _)
      (hOut ε ⟨hε.1,hε.2.trans_le h0O⟩ θ hθ houter) H)
  have hvar:euler Psi x≤2/ε^2:=hVar ε ⟨hε.1,hε.2.trans_le h0V⟩
  have hv:euler Psi x*ε^2≤2:=(le_div_iff₀ (sq_pos_of_pos hε.1)).mp hvar
  have hrat:(h:ℝ)≤(H:ℝ)/c₀:=(le_div_iff₀ hc).mpr (by simpa only[mul_comm] using hrel)
  have hscale:ε^2*((h:ℝ)*euler Psi x)≤(2/c₀)*(H:ℝ):=by
    calc
      _ = (h:ℝ)*(euler Psi x*ε^2):=by ring
      _ ≤ (h:ℝ)*2:=mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _)
      _ ≤ ((H:ℝ)/c₀)*2:=mul_le_mul_of_nonneg_right hrat (by norm_num)
      _ = _:=by ring
  have hv0:0≤(h:ℝ)*euler Psi x:=by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact (mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)).le
  have hs:=scaled_sqrt_le ε (H:ℝ) ((h:ℝ)*euler Psi x) (2/c₀) hε.1
    (by exact_mod_cast (show 0<H by omega)) hv0 (by positivity) hscale
  calc
    _ ≤ (K*ε/Real.sqrt (H:ℝ))*Real.sqrt ((h:ℝ)*euler Psi x):=
      mul_le_mul_of_nonneg_right hI (Real.sqrt_nonneg _)
    _ = K*(ε/Real.sqrt (H:ℝ)*Real.sqrt ((h:ℝ)*euler Psi x)):=by ring
    _ ≤ K*Real.sqrt (2/c₀):=mul_le_mul_of_nonneg_left hs hK.le
end WP.PositiveConvolution

namespace WP.PositiveConvolution
open Set MeasureTheory
lemma point_mass_bound_of_arc (P:PsiTheory)
    (harc:∃δ εA:ℝ,0<δ∧0<εA∧∀ε∈Ioo 0 εA,∀θ∈Icc (-Real.pi) Real.pi,
      |θ|≤δ→‖universalV P ((xCritical*(1-ε):ℝ)*Complex.exp ((θ:ℂ)*Complex.I))/
        universalV P ((xCritical*(1-ε):ℝ):ℂ)‖≤(1+θ^2/(4*ε^2))^(-1/8:ℝ))
    (c₀:ℝ) (hc:0<c₀):
    ∃C:ℝ,0<C∧∀h H:ℕ,1≤h→16≤H→c₀*(h:ℝ)≤H→
      ∀x∈Ioo 0 xCritical,∀R:ℂ→ℂ,
      AnalyticOnNhd ℂ R (Metric.ball 0 xCritical)→
      (∀j,0≤realCoeff R j∧(WP.coeff R j).im=0)→0<(R x).re→(R x).im=0→
      (∀z:ℂ,‖z‖<xCritical→HasSum (fun j=>WP.coeff R j*z^j) (R z))→
      ∀j:ℕ,realCoeff (fun z=>universalV P z^H*R z) j*x^j/
        (universalV P x^H*R x).re≤C/Real.sqrt ((h:ℝ)*euler Psi x):=by
  obtain ⟨ε0,CC,hε0,hε0half,hCC,hcrit⟩:=critical_character_integral_scaled_bound_of_arc P c₀ hc harc
  let b:ℝ:=xCritical*(1-ε0)
  have hb:0<b:=by dsimp[b];exact mul_pos Analysis.xCritical_pos_parameter (by linarith)
  have hbx:b<xCritical:=by dsimp[b];nlinarith[mul_pos Analysis.xCritical_pos_parameter hε0]
  obtain ⟨CI,hCI,hcomp⟩:=compact_character_integral_scaled_bound P c₀ b hc hb hbx
  let M:ℝ:=max CI CC
  have hM:0<M:=hCI.trans_le (le_max_left _ _)
  refine ⟨M/(2*Real.pi),div_pos hM (mul_pos (by norm_num) Real.pi_pos),?_⟩
  intro h H hh hH hrel x hx R hRa ha hRp hRi hs j
  have hvp:0<(h:ℝ)*euler Psi x:=by
    apply mul_pos
    · exact_mod_cast (show 0<h by omega)
    · exact mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hsv:0<Real.sqrt ((h:ℝ)*euler Psi x):=Real.sqrt_pos.mpr hvp
  have hI:(∫θ:ℝ in (-Real.pi)..Real.pi,
      ‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖^H)*
        Real.sqrt ((h:ℝ)*euler Psi x)≤M:=by
    by_cases hxb:x≤b
    · exact (hcomp h H hh (by omega) hrel x ⟨hx.1,hxb⟩).trans (le_max_left _ _)
    · let ε:ℝ:=1-x/xCritical
      have hεp:0<ε:=by
        have hd:x/xCritical<1:=(div_lt_one Analysis.xCritical_pos_parameter).mpr hx.2
        dsimp[ε]
        linarith
      have he:xCritical*(1-ε)=x:=by dsimp[ε];field_simp [Analysis.xCritical_pos_parameter.ne'] <;>ring
      have hεlt:ε<ε0:=by
        have ht:b<x:=lt_of_not_ge hxb
        have hd:xCritical*ε<xCritical*ε0:=by dsimp[b] at ht;rw[←he] at ht;nlinarith
        exact (mul_lt_mul_iff_right₀ Analysis.xCritical_pos_parameter).mp hd
      have ht:=hcrit h H hh hH hrel ε ⟨hεp,hεlt⟩
      rw[he] at ht
      exact ht.trans (le_max_right _ _)
  apply (le_div_iff₀ hsv).2
  calc
    _ ≤ ((2*Real.pi)⁻¹*(∫θ:ℝ in (-Real.pi)..Real.pi,
        ‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖^H))*
          Real.sqrt ((h:ℝ)*euler Psi x):=
      mul_le_mul_of_nonneg_right (point_mass_fourier_reduction P H x hx R hRa ha hRp hRi hs j) hsv.le
    _ = (2*Real.pi)⁻¹*((∫θ:ℝ in (-Real.pi)..Real.pi,
        ‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖^H)*
          Real.sqrt ((h:ℝ)*euler Psi x)):=by ring
    _ ≤ (2*Real.pi)⁻¹*M:=mul_le_mul_of_nonneg_left hI (by positivity)
    _ = M/(2*Real.pi):=by ring
end WP.PositiveConvolution
