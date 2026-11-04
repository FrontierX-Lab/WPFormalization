import WPFormalization.Coefficients.UniformSaddleCompactLower
import WPFormalization.Coefficients.UniformSaddleOrigin
import WPFormalization.Coefficients.UniformSaddlePoissonLower
import WPFormalization.Coefficients.UniformSaddleReduction
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: Proof. -/
noncomputable section
namespace WP.Coefficients
open Set Filter
open scoped Topology
lemma finite_positive_grid_lower (f:ℕ→ℕ→ℝ)(hf:∀h m,0<f h m)(N M:ℕ):
    ∃c:ℝ,0<c∧∀h≤ N,∀m≤ M,c≤ f h m:=by
  induction N with
  | zero=>
    obtain ⟨c,hc,hbound⟩:=finite_positive_sequence_lower (f 0) (hf 0) M
    refine ⟨c,hc,?_⟩
    intro h hh m hm
    have he:h=0:=by omega
    simpa only[he] using hbound m hm
  | succ N ih=>
    obtain ⟨c,hc,hbound⟩:=ih
    obtain ⟨d,hd,hnew⟩:=finite_positive_sequence_lower (f (N+1)) (hf (N+1)) M
    refine ⟨min c d,lt_min hc hd,?_⟩
    intro h hh m hm
    by_cases hh':h≤ N
    · exact (min_le_left _ _).trans (hbound h hh' m hm)
    · have he:h=N+1:=by omega
      exact (min_le_right _ _).trans (by simpa only[he] using hnew m hm)
lemma saddleKernelMass_pos (h m:ℕ)(hh:1≤ h)(hm:2*m≤3*h):
    0<tiltedKernelMass (saddleZeta ((m:ℝ)/h)) h m:=by
  by_cases hm0:m=0
  · subst m
    simp[tiltedKernelMass_eq_unscaled,saddleZeta_zero,H_zero,Analysis.derivX_zero,unscaledCoeff_zero]
  · have hhR:0<(h:ℝ):=by exact_mod_cast (show 0<h by omega)
    have hν:0<(m:ℝ)/h:=div_pos (by exact_mod_cast Nat.pos_of_ne_zero hm0) hhR
    have hνU:(m:ℝ)/h≤3/2:=by
      apply (div_le_iff₀ hhR).mpr
      have hc:(2:ℝ)*m≤3*h:=by exact_mod_cast hm
      nlinarith
    exact tiltedKernelMass_pos _ (saddleZeta_pos _ hν hνU)
      (saddleZeta_spec _ ⟨hν.le,hνU⟩).1.2 h m (by omega)
lemma tiltedKernelMass_saddle_uniform_polynomial_lower:
    ∃c:ℝ,0<c∧∀h m:ℕ,1≤ h→2*m≤3*h→
      c/((m:ℝ)+1)≤ tiltedKernelMass (saddleZeta ((m:ℝ)/h)) h m:=by
  obtain ⟨ν₁,T₁,hν₁,hT₁,horigin⟩:=tiltedKernelMass_origin_lower
  obtain ⟨cP,hcP,hpoisson⟩:=poissonCenter_polynomial_lower
  obtain ⟨C,hC,hmean⟩:=unscaledMean_uniform_linear_variance_bounds
  let ν₀:ℝ:=min ν₁ 1
  have hν₀:0<ν₀:=lt_min hν₁ zero_lt_one
  let a:ℝ:=min (r 0/2) (ν₀/(2*C))
  have ha:0<a:=lt_min (half_pos (r_pos 0 ⟨le_rfl,y₀_pos⟩)) (by positivity)
  have har:a≤ r 0:=by
    have he:=min_le_left (r 0/2) (ν₀/(2*C))
    dsimp[a] at *
    linarith[r_pos 0 ⟨le_rfl,y₀_pos⟩]
  obtain ⟨cK,T₂,hcK,hT₂,hcompact⟩:=tiltedKernelMass_compact_polynomial_lower a ha har
  let T:ℝ:=max T₁ T₂
  let N:ℕ:=Nat.ceil T
  let f:ℕ→ℕ→ℝ:=fun h m=>if 1≤ h∧2*m≤3*h then
      tiltedKernelMass (saddleZeta ((m:ℝ)/h)) h m*((m:ℝ)+1) else 1
  have hf:∀h m,0<f h m:=by
    intro h m
    dsimp[f]
    split_ifs with hv
    · exact mul_pos (saddleKernelMass_pos h m hv.1 hv.2) (by positivity)
    · norm_num
  obtain ⟨cF,hcF,hfinite⟩:=finite_positive_grid_lower f hf N (3*N)
  let c:ℝ:=min cF (min (cP/2) cK)
  have hc:0<c:=lt_min hcF (lt_min (half_pos hcP) hcK)
  refine ⟨c,hc,?_⟩
  intro h m hh hm
  have hh0:0<h:=by omega
  have hhR:0<(h:ℝ):=by exact_mod_cast hh0
  have hν0:0≤(m:ℝ)/h:=div_nonneg (Nat.cast_nonneg m) hhR.le
  have hνU:(m:ℝ)/h≤3/2:=by
    apply (div_le_iff₀ hhR).mpr
    have he:(2:ℝ)*m≤3*h:=by exact_mod_cast hm
    nlinarith
  have hζ:=(saddleZeta_spec ((m:ℝ)/h) ⟨hν0,hνU⟩)
  by_cases hlarge:T≤(h:ℝ)
  · by_cases hm0:m=0
    · subst m
      have hp:=saddleKernelMass_pos h 0 hh (by omega)
      have hc1:c≤1:=by
        have hf00:=hfinite 0 (by omega) 0 (by omega)
        simp only[f,show ¬(1≤(0:ℕ)∧2*0≤3*0) by omega,ite_false] at hf00
        exact (min_le_left _ _).trans hf00
      simpa only[Nat.cast_zero,zero_div,saddleZeta_zero,zero_add,div_one,
        tiltedKernelMass_eq_unscaled,Complex.ofReal_zero,H_zero,Analysis.derivX_zero,Complex.one_re,one_pow,
        pow_zero,unscaledCoeff_zero,mul_one] using hc1
    · have hmpos:0 < m:=Nat.pos_of_ne_zero hm0
      by_cases hsmall:(m:ℝ)/h≤ν₀
      · have hlo:=horigin h m hh ((le_max_left _ _).trans hlarge) hmpos
          (hsmall.trans (min_le_left _ _))
        have hcp:=div_le_div_of_nonneg_right (min_le_left (cP/2) cK) (by positivity:(0:ℝ)≤(m:ℝ)+1)
        have hcc:c≤ cP/2:=(min_le_right _ _).trans (min_le_left _ _)
        calc
          c/((m:ℝ)+1)≤(cP/2)/((m:ℝ)+1):=div_le_div_of_nonneg_right hcc (by positivity)
          _ = (cP/((m:ℝ)+1))/2:=by ring
          _ ≤ poissonCenter m/2:=div_le_div_of_nonneg_right (hpoisson m) (by norm_num)
          _ ≤ _:=hlo
      · have haz:a≤ saddleZeta ((m:ℝ)/h):=by
          have hs:ν₀<(m:ℝ)/h:=lt_of_not_ge hsmall
          have ht:=(hmean _ hζ.1).2.1
          rw[hζ.2] at ht
          have hau:a≤ν₀/(2*C):=min_le_right _ _
          have hau':a*(2*C)≤ν₀:=(le_div_iff₀ (by positivity)).mp hau
          nlinarith
        have hlo:=hcompact _ ⟨haz,hζ.1.2⟩ h m hh0 ((le_max_right _ _).trans hlarge)
          (by rw[hζ.2];field_simp)
        exact (div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (by positivity)).trans hlo
  · have hhN:h≤ N:=by
      have hceil:T≤(N:ℝ):=Nat.le_ceil T
      have he:(h:ℝ)≤ N:=(le_of_not_ge hlarge).trans hceil
      exact_mod_cast he
    have hmN:m≤3*N:=by omega
    have hlo:=hfinite h hhN m hmN
    simp only[f] at hlo
    rw[ite_eq_left ⟨hh,hm⟩] at hlo
    apply (div_le_iff₀ (by positivity:(0:ℝ)<(m:ℝ)+1)).mpr
    exact (min_le_left _ _).trans hlo
end WP.Coefficients
namespace WP
open Set
lemma uniform_saddle_proof : ∃ C : ℝ, 0 < C ∧
    ∀ h : ℕ, 1 ≤ h → ∀ m : ℕ, 2*m ≤ 3*h →
      |Real.log (unscaledCoeff h m) +
        (h : ℝ)*Real.log (H 0 (saddleZeta ((m : ℝ)/h))).re +
        (m : ℝ)*Real.log (saddleZeta ((m : ℝ)/h))| ≤ C*Real.log (h+1) :=by
  obtain ⟨c,hc,hlower⟩:=Coefficients.tiltedKernelMass_saddle_uniform_polynomial_lower
  obtain ⟨C,hC,hlog⟩:=Coefficients.log_probability_bound_of_polynomial_lower c hc
  refine ⟨C,hC,?_⟩
  intro h hh m hm
  by_cases hm0:m=0
  · subst m
    rw[uniform_saddle_zero_exact]
    have hh1:(1:ℝ)≤(h:ℝ)+1:=by linarith only [show (0:ℝ)≤(h:ℝ) from Nat.cast_nonneg h]
    simpa only[abs_zero] using mul_nonneg hC.le (Real.log_nonneg hh1)
  · have hh0:0<h:=by omega
    have hhR:0<(h:ℝ):=by exact_mod_cast hh0
    have hν:0<(m:ℝ)/h:=div_pos (by exact_mod_cast Nat.pos_of_ne_zero hm0) hhR
    have hνU:(m:ℝ)/h≤3/2:=by
      apply (div_le_iff₀ hhR).mpr
      have hmr:(2:ℝ)*m≤3*h:=by exact_mod_cast hm
      nlinarith
    have hζ:=Coefficients.saddleZeta_spec ((m:ℝ)/h) ⟨hν.le,hνU⟩
    have hz:=Coefficients.saddleZeta_pos _ hν hνU
    have hident:=Coefficients.tiltedKernelMass_log_identity _ hz hζ.1.2 h m hh0
    rw[←hident]
    exact hlog h m hh hm _ (hlower h m hh hm)
      (Coefficients.tiltedKernelMass_le_one _ hζ.1 h m hh0)
end WP
