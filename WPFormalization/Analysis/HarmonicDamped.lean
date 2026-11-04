import WPFormalization.Analysis.HarmonicL1
/-! Quantitative damped Gaussian error for the actual harmonic family.
The radius power estimate keeps the Gaussian factor; real Gaussian moments
and the true off-zero characteristic gap control the outer region. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma power_difference_bound_radius (x y:ℂ) (R:ℝ) (hR:0≤R)
    (hx:‖x‖≤R) (hy:‖y‖≤R) (n:ℕ):
    ‖x^(n+1)-y^(n+1)‖≤((n+1:ℕ):ℝ)*R^n*‖x-y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he:x^(n+1+1)-y^(n+1+1)=x^(n+1)*(x-y)+(x^(n+1)-y^(n+1))*y:=by ring
    rw [he]
    calc
      _ ≤ ‖x^(n+1)*(x-y)‖+‖(x^(n+1)-y^(n+1))*y‖ := norm_add_le _ _
      _ ≤ R^(n+1)*‖x-y‖+(((n+1:ℕ):ℝ)*R^n*‖x-y‖)*R := by
        simp only [norm_mul,norm_pow]
        exact add_le_add (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx _) (norm_nonneg _))
          (mul_le_mul ih hy (norm_nonneg _) (by positivity))
      _ = _ := by push_cast;ring

lemma centeredHarmonic_damped_gaussian_error : ∃δ C β:ℝ,0<δ ∧0<C ∧0<β ∧
    ∀Y∈Icc (0:ℝ) y₀,∀h:ℕ,2≤h→∀t:ℝ,|t/Real.sqrt (h:ℝ)|≤δ→
    ‖centeredHarmonic Y ((t/Real.sqrt (h:ℝ):ℝ):ℂ)^h-harmonicGaussianKernel Y t‖≤
      (C*|t|^3/Real.sqrt (h:ℝ))*Real.exp (-β*t^2) := by
  obtain ⟨δE,C,hδE,hC,herror⟩:=centeredHarmonic_uniform_gaussian_error
  obtain ⟨δB,β₀,hδB,hβ₀,hbound⟩:=centeredHarmonic_uniform_gaussian_bound
  obtain ⟨c,B,s,hc,hB,hs,hvar⟩:=harmonic_uniform_bounds
  let β:ℝ:=min β₀ (c/2)
  have hβ:0<β:=by dsimp[β];positivity
  refine ⟨min δE δB,C,β/2,by positivity,hC,by positivity,?_⟩
  intro Y hY h hh t ht
  have hhpos:0<h:=by omega
  let u:ℝ:=t/Real.sqrt (h:ℝ)
  let g:ℂ:=Complex.exp (-(harmonicVariance Y:ℂ)/2*(u:ℂ)^2)
  let R:ℝ:=Real.exp (-β*u^2)
  have hnorm:‖centeredHarmonic Y (u:ℂ)‖≤R := by
    apply (hbound Y hY u (ht.trans (min_le_right _ _))).trans
    apply Real.exp_le_exp.mpr
    have hb:β≤β₀:=min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg u)]
  have hgnorm:‖g‖≤R := by
    have he:-(harmonicVariance Y:ℂ)/2*(u:ℂ)^2=((-harmonicVariance Y/2*u^2:ℝ):ℂ):=by push_cast;rfl
    dsimp[g,R]
    rw [he,Complex.norm_exp,Complex.ofReal_re]
    apply Real.exp_le_exp.mpr
    have hb:β≤c/2:=min_le_right _ _
    have hv: c≤harmonicVariance Y:=(hvar Y hY).2.2.1
    nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg u),mul_le_mul_of_nonneg_right hv (sq_nonneg u)]
  have hpow:‖centeredHarmonic Y (u:ℂ)^h-g^h‖≤(h:ℝ)*R^(h-1)*‖centeredHarmonic Y (u:ℂ)-g‖ := by
    have he:h-1+1=h:=by omega
    simpa only [he] using power_difference_bound_radius _ _ R (by dsimp[R];positivity) hnorm hgnorm (h-1)
  have hbase:‖centeredHarmonic Y (u:ℂ)-g‖≤C*|u|^3:=herror Y hY u (ht.trans (min_le_left _ _))
  have hdecay:R^(h-1)≤Real.exp (-(β/2)*t^2) := by
    dsimp[R]
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hcast:((h-1:ℕ):ℝ)≥(h:ℝ)/2 := by
      rw [Nat.cast_sub (by omega : 1≤h),Nat.cast_one]
      have hreal:(2:ℝ)≤h:=by exact_mod_cast hh
      linarith
    have hmul:=mul_le_mul_of_nonneg_right hcast (mul_nonneg hβ.le (sq_nonneg u))
    have hscale:(h:ℝ)*u^2=t^2:=nat_mul_scaled_quadratic h hhpos t
    have heq:(h:ℝ)/2*(β*u^2)=β/2*t^2 := by
      calc _=β/2*((h:ℝ)*u^2):=by ring
           _=_:=by rw[hscale]
    nlinarith
  have hC:(h:ℝ)*(C*|u|^3)=C*|t|^3/Real.sqrt (h:ℝ):=by
    calc _=C*((h:ℝ)*|u|^3):=by ring
         _= _:=by change C*((h:ℝ)*|t/Real.sqrt (h:ℝ)|^3)=_; rw [nat_mul_scaled_cubic h hhpos t];ring
  have hp:=hpow.trans (mul_le_mul_of_nonneg_left hbase (by positivity))
  have hfinal:=mul_le_mul_of_nonneg_left hdecay (show 0≤(h:ℝ)*(C*|u|^3) by positivity)
  rw [hC] at hfinal
  have he:g^h=harmonicGaussianKernel Y t:=gaussian_base_power _ t h hhpos
  rw [he] at hp
  apply hp.trans
  calc _=((h:ℝ)*(C*|u|^3))*R^(h-1):=by ring
       _=(C*|t|^3/Real.sqrt (h:ℝ))*R^(h-1):=by rw[hC]
       _≤_:=hfinal
end WP.Analysis

noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
open scoped Topology
lemma abs_pow_gaussian_integrable (β:ℝ)(hβ:0<β)(n:ℕ):
    Integrable (fun t:ℝ=>|t|^n*Real.exp (-β*t^2)) volume := by
  have hi:= (integrable_rpow_mul_exp_neg_mul_sq hβ (s:=(n:ℝ)) (by linarith [Nat.cast_nonneg (α:=ℝ) n])).norm
  simpa only [Real.rpow_natCast,Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)] using hi
lemma gaussian_tail_weight_integrable (δ β:ℝ)(hβ:0<β)(h:ℕ):
    Integrable (fun t:ℝ=>|t| *gaussianOuterTail δ β h t) volume := by
  apply (abs_pow_gaussian_integrable β hβ 1).mono'
  · exact continuous_abs.aestronglyMeasurable.mul
      (gaussianOuterTail_integrable δ β hβ h).aestronglyMeasurable
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs,abs_of_nonneg (by unfold gaussianOuterTail;split_ifs <;> positivity)]
    unfold gaussianOuterTail
    split_ifs <;> simp <;> positivity
lemma gaussian_tail_weight_bound (δ β:ℝ)(hδ:0<δ)(hβ:0<β)(h:ℕ)(hh:0<h):
    (∫t:ℝ,|t| *gaussianOuterTail δ β h t)≤
      (1/(δ*Real.sqrt (h:ℝ)))*(∫t:ℝ,|t|^2*Real.exp (-β*t^2)) := by
  have hr:0<Real.sqrt (h:ℝ):=Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hD:0<δ*Real.sqrt (h:ℝ):=mul_pos hδ hr
  have hpoint (t:ℝ):|t| *gaussianOuterTail δ β h t≤
      (1/(δ*Real.sqrt (h:ℝ)))*(|t|^2*Real.exp (-β*t^2)) := by
    unfold gaussianOuterTail
    split_ifs with ht
    · have hh:|t|≤|t|^2/(δ*Real.sqrt (h:ℝ)):=by
        apply (le_div_iff₀ hD).mpr
        nlinarith [mul_le_mul_of_nonneg_right ht.le (abs_nonneg t)]
      calc _≤(|t|^2/(δ*Real.sqrt (h:ℝ)))*Real.exp (-β*t^2):=
               mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
           _=_:=by ring
    · simp only [mul_zero]
      positivity
  calc _≤∫t:ℝ,(1/(δ*Real.sqrt (h:ℝ)))*(|t|^2*Real.exp (-β*t^2)):=
          integral_mono (gaussian_tail_weight_integrable δ β hβ h)
            ((abs_pow_gaussian_integrable β hβ 2).const_mul _) hpoint
       _=_:=integral_const_mul _ _
end WP.Analysis

namespace WP.Analysis
open Complex
lemma phase_difference_bound (p q t:ℝ):
    ‖Complex.exp (-(p:ℂ)*(t:ℂ)*Complex.I)-Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)‖≤|p-q| *|t| := by
  have he:Complex.exp (-(p:ℂ)*(t:ℂ)*Complex.I)-Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)=
      Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*(Complex.exp (Complex.I*((-(p-q)*t:ℝ):ℂ))-1):=by
    rw [mul_sub,mul_one,←Complex.exp_add]
    congr 2
    push_cast
    ring
  have hn:‖Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)‖=1:=by
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re,Complex.mul_im]
  rw [he,norm_mul,hn,one_mul]
  calc _≤‖(-(p-q)*t:ℝ)‖:=Real.norm_exp_I_mul_ofReal_sub_one_le
       _=|p-q| *|t|:=by rw [Real.norm_eq_abs,abs_mul,abs_neg]
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma geometric_weight_integrable (ρ:ℝ)(h:ℕ):
    Integrable (fun t:ℝ=>|t| *geometricOuterEnvelope ρ h t) volume := by
  have he:(fun t:ℝ=>|t| *geometricOuterEnvelope ρ h t)=
      (Icc (-(Real.pi*Real.sqrt (h:ℝ))) (Real.pi*Real.sqrt (h:ℝ))).indicator
        (fun t:ℝ=>|t| *ρ^h):=by
    ext t
    simp only [geometricOuterEnvelope,Set.indicator_apply,Set.mem_Icc,←abs_le]
    split_ifs <;> simp
  rw [he]
  exact (continuous_abs.mul continuous_const).integrableOn_Icc.integrable_indicator measurableSet_Icc
lemma geometric_weight_bound (ρ:ℝ)(hρ:0≤ρ)(h:ℕ):
    (∫t:ℝ,|t| *geometricOuterEnvelope ρ h t)≤2*Real.pi^2*(h:ℝ)*ρ^h := by
  have hpoint (t:ℝ):|t| *geometricOuterEnvelope ρ h t≤
      (Real.pi*Real.sqrt (h:ℝ))*geometricOuterEnvelope ρ h t := by
    unfold geometricOuterEnvelope
    split_ifs with ht
    · exact mul_le_mul_of_nonneg_right ht (by positivity)
    · simp
  calc _≤∫t:ℝ,(Real.pi*Real.sqrt (h:ℝ))*geometricOuterEnvelope ρ h t :=
           integral_mono (geometric_weight_integrable ρ h)
             ((geometricOuterEnvelope_integrable ρ h).const_mul _) hpoint
       _=(Real.pi*Real.sqrt (h:ℝ))*(2*Real.pi*Real.sqrt (h:ℝ)*ρ^h):=by
         rw[integral_const_mul,geometricOuterEnvelope_integral]
       _=2*Real.pi^2*(Real.sqrt (h:ℝ))^2*ρ^h:=by ring
       _=_:=by rw [Real.sq_sqrt (show (0:ℝ)≤h by positivity)]
lemma geometric_weight_uniform_rate (ρ:ℝ)(hρ:0≤ρ)(hρ1:ρ<1):
    ∃C:ℝ,0<C ∧∀h:ℕ,0<h→(∫t:ℝ,|t| *geometricOuterEnvelope ρ h t)≤C/Real.sqrt (h:ℝ) := by
  have hs:Summable (fun n:ℕ=>(n:ℝ)^2*ρ^n):=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by rwa[Real.norm_eq_abs,abs_of_nonneg hρ])
  let C:ℝ:=2*Real.pi^2*((∑'n:ℕ,(n:ℝ)^2*ρ^n)+1)
  have hS:0≤∑'n:ℕ,(n:ℝ)^2*ρ^n:=tsum_nonneg (fun n=>by positivity)
  refine ⟨C,by dsimp[C];positivity,?_⟩
  intro h hh
  have hr:0<Real.sqrt (h:ℝ):=Real.sqrt_pos.mpr (by exact_mod_cast hh)
  have hhR:(1:ℝ)≤h:=by exact_mod_cast hh
  have hrs:Real.sqrt (h:ℝ)^2=(h:ℝ):=Real.sq_sqrt (by positivity)
  have hrh:Real.sqrt (h:ℝ)≤(h:ℝ):=by nlinarith [Real.sqrt_nonneg (h:ℝ)]
  have ht:(h:ℝ)^2*ρ^h≤∑'n:ℕ,(n:ℝ)^2*ρ^n:=hs.le_tsum h (fun n _=>by positivity)
  apply (le_div_iff₀ hr).mpr
  have hfirst:=mul_le_mul_of_nonneg_right (geometric_weight_bound ρ hρ h) hr.le
  have hsecond:=mul_le_mul_of_nonneg_left hrh (show 0≤2*Real.pi^2*(h:ℝ)*ρ^h by positivity)
  have hthird:=mul_le_mul_of_nonneg_left ht (show 0≤2*Real.pi^2 by positivity)
  dsimp[C]
  nlinarith
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma harmonicFourier_damped_envelope : ∃δ C β γ ρ:ℝ,
    0<δ ∧0<C ∧0<β ∧0<γ ∧0≤ρ ∧ρ<1 ∧∀Y∈Icc (0:ℝ) y₀,∀h:ℕ,2≤h→∀t:ℝ,
    ‖scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t‖≤
      (C*|t|^3/Real.sqrt (h:ℝ))*Real.exp (-β*t^2)+geometricOuterEnvelope ρ h t+gaussianOuterTail δ γ h t := by
  obtain ⟨δE,C,β,hδE,hC,hβ,herror⟩:=centeredHarmonic_damped_gaussian_error
  obtain ⟨c,B,s,hc,hB,hs,hvar⟩:=harmonic_uniform_bounds
  let δ:ℝ:=min δE Real.pi
  have hδ:0<δ:=by dsimp[δ];positivity
  have hδπ:δ≤Real.pi:=min_le_right _ _
  obtain ⟨ρ,hρ,hρ1,hgap⟩:=harmonicCharacteristic_uniform_gap δ hδ hδπ
  refine ⟨δ,C,β,c/2,ρ,hδ,hC,hβ,by positivity,hρ,hρ1,?_⟩
  intro Y hY h hh t
  have hhpos:0<h:=by omega
  let r:=Real.sqrt (h:ℝ)
  let u:=t/r
  have hr:0<r:=Real.sqrt_pos.mpr (by exact_mod_cast hhpos)
  have huAbs:|u|=|t|/r:=by dsimp[u];rw[abs_div,abs_of_pos hr]
  have hG:‖harmonicGaussianKernel Y t‖≤Real.exp (-(c/2)*t^2):=by
    rw[harmonicGaussianKernel_norm]
    apply Real.exp_le_exp.mpr
    have hv:=(hvar Y hY).2.2.1
    nlinarith [mul_le_mul_of_nonneg_right hv (sq_nonneg t)]
  have hEnv:0≤(C*|t|^3/Real.sqrt (h:ℝ))*Real.exp (-β*t^2):=by positivity
  have hGeo:0≤geometricOuterEnvelope ρ h t:=by unfold geometricOuterEnvelope;split_ifs <;> positivity
  have hTail:0≤gaussianOuterTail δ (c/2) h t:=by unfold gaussianOuterTail;split_ifs <;> positivity
  by_cases hInner:|t|≤δ*r
  · have huδ:|u|≤δ:=by rw[huAbs];exact (div_le_iff₀ hr).mpr hInner
    have hCut:|t|≤Real.pi*r:=hInner.trans (mul_le_mul_of_nonneg_right hδπ hr.le)
    have hE:=herror Y hY h hh t (huδ.trans (min_le_left _ _))
    rw[scaledHarmonicFourier,if_pos hCut]
    nlinarith
  · have hOut:δ*r< |t|:=lt_of_not_ge hInner
    have hTailEq:gaussianOuterTail δ (c/2) h t=Real.exp (-(c/2)*t^2):=by
      unfold gaussianOuterTail
      rw[if_pos hOut]
    by_cases hCut:|t|≤Real.pi*r
    · have huPi:u∈Icc (-Real.pi) Real.pi:=by
        apply abs_le.mp
        rw[huAbs]
        exact (div_le_iff₀ hr).mpr hCut
      have huδ:δ≤|u|:=by rw[huAbs];exact (le_div_iff₀ hr).mpr hOut.le
      have hChar:=hgap Y hY u huPi huδ
      have hPower:‖centeredHarmonic Y (u:ℂ)^h‖≤ρ^h:=by
        rw[norm_pow,centeredHarmonic_norm_real]
        exact pow_le_pow_left₀ (norm_nonneg _) hChar h
      have hsum:=(norm_sub_le (centeredHarmonic Y (u:ℂ)^h) (harmonicGaussianKernel Y t)).trans (add_le_add hPower hG)
      rw[scaledHarmonicFourier,if_pos hCut,geometricOuterEnvelope,if_pos hCut,hTailEq]
      nlinarith
    · rw[scaledHarmonicFourier,if_neg hCut,zero_sub,norm_neg,hTailEq]
      nlinarith
end WP.Analysis
