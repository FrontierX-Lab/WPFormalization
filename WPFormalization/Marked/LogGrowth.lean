import WPFormalization.Marked.GrowthBounds
import WPFormalization.Statements.HarmonicComparison
import WPFormalization.Marked.Positivity
import WPFormalization.Analysis.HarmonicCentral
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Equation (6.3), paper label `eq:TL11`, for the actual marked generating
functions. The exact harmonic normalization cancels the factor 3, the proved
uniform comparison controls its ratio, and the central lattice estimate
controls the harmonic coefficient. The error is uniform on the closed
parameter interval and is o(g) for each positive fixed number of markings. -/

noncomputable section
namespace WP
open Set Filter
open scoped Topology
lemma barH_one_log_A (Y:ℝ)(hY:Y∈Icc 0 y₀):
    Real.log (barH Y 1).re=Real.log 3+Real.log (A Y) := by
  have ha:0 < A Y:=by unfold A;exact div_pos (Analysis.barH_one_re_pos Y hY) (by norm_num)
  have he:(barH Y 1).re=3*A Y:=by unfold A;ring
  rw[he,Real.log_mul (by norm_num) ha.ne']
lemma W_log_harmonic_decomposition (P:PsiTheory)(g p:ℕ)(hp:1 ≤ p)(hs:Stable g p)
    (Y:ℝ)(hY:Y∈Icc 0 y₀):
    Real.log (W P g p Y)-Real.log (Real.Gamma (complexity g p))+
      (complexity g p:ℝ)*Real.log (A Y)=
      Real.log (ratio P g (List.replicate p 0) Y)+
      Real.log (harmonicCoeff Y (complexity g p) (dimension g p))+
      (complexity g p:ℝ)*Real.log (barH Y 1).re := by
  have hh:0 < complexity g p:=by unfold complexity;unfold Stable at hs;omega
  have hhR:(0:ℝ)<complexity g p:=by exact_mod_cast hh
  have hΓ:0 < Real.Gamma (complexity g p:ℝ):=Real.Gamma_pos_of_pos hhR
  have hC:0 < harmonicCoeff Y (complexity g p) (dimension g p):=harmonicCoeff_pos Y _ _ hh hY
  have hNorm:0 < normalized P g (List.replicate p 0) Y:=normalized_pos_valid_nonempty P g _
    (by simpa only[List.length_replicate] using hp) (by simpa only[List.length_replicate] using hs) (by simp) Y hY
  have hMod:0 < model g (List.replicate p 0) Y:=model_pos g _ Y (by simpa only[List.length_replicate] using hs) hY
  have hR:0 < ratio P g (List.replicate p 0) Y:=div_pos hNorm hMod
  rw[W_eq_ratio_harmonic P g p hs Y hY,
    Real.log_mul (by positivity) hR.ne',Real.log_mul (by positivity) hC.ne',
    Real.log_mul (by positivity) hΓ.ne',Real.log_pow,barH_one_log_A Y hY]
  ring
lemma marked_dimension_offset (g p:ℕ)(hg:2 ≤ g):
    (dimension g p:ℝ)-3*(complexity g p:ℝ)/2= -(p:ℝ)/2 := by
  unfold dimension complexity
  rw[Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
  push_cast
  ring
lemma W_uniform_log_envelope (P:PsiTheory)(p:ℕ)(hp:1 ≤ p):∃C:ℝ,0 < C ∧∃g₀:ℕ,∀g≥g₀,
    ∀Y∈Icc (0:ℝ) y₀,
      |Real.log (W P g p Y)-Real.log (Real.Gamma (complexity g p))+
        (complexity g p:ℝ)*Real.log (A Y)| ≤
      C*(Real.sqrt (complexity g p:ℝ)+(Real.log ((complexity g p:ℝ)+1))^2+1) := by
  obtain ⟨Cr,hCr,hRatio⟩:=harmonic_comparison P p hp
  obtain ⟨Cc,hCc,h₀,hCentral⟩:=Analysis.harmonicCoeff_central_log_bound ((p:ℝ)/2) (by positivity)
  let C:ℝ:=Cr+Cc+2
  refine ⟨C,by dsimp[C];positivity,max 2 h₀,?_⟩
  intro g hgg Y hY
  have hg:2 ≤ g:=(le_max_left _ _).trans hgg
  have hst:Stable g p:=by unfold Stable;omega
  let h:=complexity g p
  let m:=dimension g p
  have hhg:g ≤ h:=by dsimp[h];unfold complexity;omega
  have hh:0 < h:=by omega
  have hh1:(1:ℝ) ≤ h:=by exact_mod_cast (by omega:1 ≤ h)
  have hr:1 ≤ Real.sqrt (h:ℝ):=by nlinarith[Real.sqrt_nonneg (h:ℝ),Real.sq_sqrt (show (0:ℝ) ≤ h by positivity)]
  have hm:|(m:ℝ)-3*(h:ℝ)/2| ≤ ((p:ℝ)/2)*Real.sqrt (h:ℝ):=by
    dsimp[m,h]
    rw[marked_dimension_offset g p hg,abs_div,abs_neg,abs_of_nonneg (Nat.cast_nonneg p)]
    norm_num only[Nat.abs_ofNat]
    have hp0:(0:ℝ) ≤ p:=Nat.cast_nonneg _
    nlinarith
  have hcent:=hCentral h ((le_max_right _ _).trans (hgg.trans hhg)) hh Y hY m hm
  have hrat:=hRatio g (List.replicate p 0) (by simp) hst (by simp) Y hY
  have hrat':-Cr*(Real.log ((h:ℝ)+1))^2 ≤ Real.log (ratio P g (List.replicate p 0) Y) ∧
      Real.log (ratio P g (List.replicate p 0) Y) ≤ Cr*Real.sqrt (h:ℝ):=by
    simpa only[List.length_replicate] using hrat
  let F:ℝ:=Real.sqrt (h:ℝ)+(Real.log ((h:ℝ)+1))^2+1
  have hF:1 ≤ F:=by dsimp[F];nlinarith[Real.sqrt_nonneg (h:ℝ),sq_nonneg (Real.log ((h:ℝ)+1))]
  have hRabs:|Real.log (ratio P g (List.replicate p 0) Y)| ≤ Cr*F:=by
    apply abs_le.mpr
    dsimp[F]
    constructor <;> nlinarith[hrat'.1,hrat'.2,Real.sqrt_nonneg (h:ℝ),sq_nonneg (Real.log ((h:ℝ)+1))]
  have hl0:0 ≤ Real.log (h:ℝ):=Real.log_nonneg hh1
  have hl:Real.log (h:ℝ) ≤ Real.log ((h:ℝ)+1):=Real.log_le_log (by positivity) (by linarith)
  have hLog:|Real.log (h:ℝ)|/2 ≤ F:=by
    rw[abs_of_nonneg hl0]
    dsimp[F]
    nlinarith[sq_nonneg (Real.log ((h:ℝ)+1)),Real.sqrt_nonneg (h:ℝ)]
  have hExact:=W_log_harmonic_decomposition P g p hp hst Y hY
  change |Real.log (W P g p Y)-Real.log (Real.Gamma (h:ℝ))+(h:ℝ)*Real.log (A Y)| ≤ C*F
  rw[hExact]
  change |Real.log (ratio P g (List.replicate p 0) Y)+Real.log (harmonicCoeff Y h m)+
      (h:ℝ)*Real.log (barH Y 1).re| ≤ C*F
  have he:Real.log (ratio P g (List.replicate p 0) Y)+Real.log (harmonicCoeff Y h m)+(h:ℝ)*Real.log (barH Y 1).re=
      Real.log (ratio P g (List.replicate p 0) Y)+
      (Real.log (harmonicCoeff Y h m)+(h:ℝ)*Real.log (barH Y 1).re+Real.log (h:ℝ)/2)-Real.log (h:ℝ)/2:=by ring
  rw[he]
  calc _ ≤ |Real.log (ratio P g (List.replicate p 0) Y)|+
          |Real.log (harmonicCoeff Y h m)+(h:ℝ)*Real.log (barH Y 1).re+Real.log (h:ℝ)/2|+|Real.log (h:ℝ)|/2:=by
           calc _ ≤ |Real.log (ratio P g (List.replicate p 0) Y)+
                     (Real.log (harmonicCoeff Y h m)+(h:ℝ)*Real.log (barH Y 1).re+Real.log (h:ℝ)/2)|+
                     |Real.log (h:ℝ)/2|:=abs_sub _ _
                _ ≤ _:=by rw[abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)];gcongr;exact abs_add_le _ _
       _ ≤ Cr*F+Cc+F:=add_le_add (add_le_add hRabs hcent) hLog
       _ ≤ C*F:=by
         have hCcF:=mul_nonneg hCc.le (sub_nonneg.mpr hF)
         dsimp[C]
         nlinarith
end WP

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma complexity_real_tendsto_atTop (p:ℕ):Tendsto (fun g:ℕ=>(complexity g p:ℝ)) atTop atTop := by
  have he:∀ᶠg:ℕ in atTop,(g:ℝ) ≤ (complexity g p:ℝ):=by
    filter_upwards[eventually_ge_atTop 2] with g hg
    exact_mod_cast (show g ≤ complexity g p by unfold complexity;omega)
  exact tendsto_atTop_mono' atTop he tendsto_natCast_atTop_atTop
lemma complexity_div_genus_tendsto (p:ℕ):
    Tendsto (fun g:ℕ=>(complexity g p:ℝ)/(g:ℝ)) atTop (𝓝 2) := by
  have ht:=(tendsto_const_div_atTop_nhds_zero_nat ((p:ℝ)-2)).const_add (2:ℝ)
  simp only[add_zero] at ht
  apply ht.congr'
  filter_upwards[eventually_ge_atTop 1] with g hg
  have hg0:(g:ℝ)≠0:=by exact_mod_cast (show g≠0 by omega)
  unfold complexity
  rw[Nat.cast_sub (by omega)]
  push_cast
  field_simp <;> ring
lemma complexity_sqrt_div_self_tendsto (p:ℕ):
    Tendsto (fun g:ℕ=>Real.sqrt (complexity g p:ℝ)/(complexity g p:ℝ)) atTop (𝓝 0) := by
  have ht:=complexity_real_tendsto_atTop p
  have hs:=(Real.tendsto_sqrt_atTop.comp ht).const_div_atTop (1:ℝ)
  apply hs.congr'
  filter_upwards[ht.eventually (eventually_gt_atTop (0:ℝ))] with g hg
  have hr:0 < Real.sqrt (complexity g p:ℝ):=Real.sqrt_pos.mpr hg
  apply (div_eq_div_iff hr.ne' hg.ne').mpr
  nlinarith[Real.sq_sqrt hg.le]
lemma complexity_log_sq_div_self_tendsto (p:ℕ):
    Tendsto (fun g:ℕ=>(Real.log ((complexity g p:ℝ)+1))^2/(complexity g p:ℝ)) atTop (𝓝 0) := by
  have ht:=(Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 2 one_ne_zero).comp
    (tendsto_atTop_add_const_right atTop 1 (complexity_real_tendsto_atTop p))
  simpa only[Function.comp_def,one_mul,add_neg_cancel_right] using ht
lemma complexity_error_envelope_tendsto (p:ℕ):
    Tendsto (fun g:ℕ=>(Real.sqrt (complexity g p:ℝ)+(Real.log ((complexity g p:ℝ)+1))^2+1)/(g:ℝ))
      atTop (𝓝 0) := by
  have hs:=complexity_sqrt_div_self_tendsto p
  have hl:=complexity_log_sq_div_self_tendsto p
  have hi:=(complexity_real_tendsto_atTop p).const_div_atTop (1:ℝ)
  have ht:=(hs.add hl).add hi
  simp only[add_zero] at ht
  have hh:Tendsto (fun g:ℕ=>(Real.sqrt (complexity g p:ℝ)+(Real.log ((complexity g p:ℝ)+1))^2+1)/(complexity g p:ℝ))
      atTop (𝓝 0):=by
    apply ht.congr'
    exact Eventually.of_forall (fun g=>by ring)
  have hm:=hh.mul (complexity_div_genus_tendsto p)
  simp only[zero_mul] at hm
  apply hm.congr'
  filter_upwards[(complexity_real_tendsto_atTop p).eventually (eventually_gt_atTop (0:ℝ)),eventually_ge_atTop 1] with g hg hgg
  have hg0:(g:ℝ)≠0:=by exact_mod_cast (show g≠0 by omega)
  field_simp
end WP.Analysis

namespace WP
open Set Filter
open scoped Topology
theorem W_uniform_log_growth (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∀ ε : ℝ, 0 < ε → ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Icc (0 : ℝ) y₀,
      |Real.log (W P g p Y) - Real.log (Real.Gamma (complexity g p)) +
        (complexity g p : ℝ) * Real.log (A Y)| ≤ ε * (g : ℝ) := by
  intro ε hε
  obtain ⟨C,hC,g₀,hbound⟩ := W_uniform_log_envelope P p hp
  have ht := (Analysis.complexity_error_envelope_tendsto p).const_mul C
  simp only [mul_zero] at ht
  have he := ht.eventually (gt_mem_nhds hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨max 1 (max g₀ N), ?_⟩
  intro g hg Y hY
  have hg1 : 1 ≤ g := (le_max_left _ _).trans hg
  have hgg : g₀ ≤ g := (le_max_left _ _).trans ((le_max_right _ _).trans hg)
  have hgN : N ≤ g := (le_max_right _ _).trans ((le_max_right _ _).trans hg)
  have hgp : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hsmall := (div_lt_iff₀ hgp).mp (show
      C * (Real.sqrt (complexity g p : ℝ) + (Real.log ((complexity g p : ℝ) + 1)) ^ 2 + 1) /
        (g : ℝ) < ε by simpa only [mul_div_assoc] using hN g hgN)
  exact (hbound g hgg Y hY).trans hsmall.le
end WP
