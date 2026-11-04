import WPFormalization.Analysis.PoissonNormalizer
import WPFormalization.Analysis.PoissonPhasePrefactor
/-! The true Poisson central factor is uniformly bounded away from zero once k exceeds a fixed positive multiple of sqrt(h). Constants precede h and k; the zero-frequency case belongs to the separate exact origin normalization. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma poissonNormalizer_large_nat_bounds:
    ∃N:ℝ,1≤N ∧ ∀k:ℕ,N≤(k:ℝ)→
      1/2≤Real.sqrt (2*Real.pi*k)*poissonCenter k ∧
      Real.sqrt (2*Real.pi*k)*poissonCenter k≤3/2:=by
  obtain ⟨C,B,c,H,hC,hB,hc,hH,herr⟩:=poissonNormalizer_gevrey_one
  let N:ℝ:=max 1 (max H (2*C*B))
  refine ⟨N,le_max_left _ _,?_⟩
  intro k hk
  have hk1:1≤(k:ℝ):=(le_max_left _ _).trans hk
  have hkpos:0<(k:ℝ):=zero_lt_one.trans_le hk1
  have hkNat:1≤k:=by exact_mod_cast hk1
  have hkH:H≤(k:ℝ):=((le_max_left _ _).trans (le_max_right _ _)).trans hk
  have hkCB:2*C*B≤(k:ℝ):=((le_max_right _ _).trans (le_max_right _ _)).trans hk
  have he:=herr 0 k hkH (by simpa only[Nat.cast_zero] using (mul_pos hc hkpos).le)
  simp only[inversePowerTruncation,Finset.sum_range_one,
    PowerSeries.coeff_zero_eq_constantCoeff,WP.HigherOrder.poissonStirlingSeries_constant,
    pow_zero,div_one,Nat.zero_add,pow_one,Nat.factorial_one,Nat.cast_one,mul_one] at he
  have herrHalf:C*B/(k:ℝ)≤1/2:=(div_le_iff₀ hkpos).mpr (by nlinarith)
  have hlo:1/2≤poissonNormalizer k:=by linarith[neg_le_of_abs_le he]
  have hup:poissonNormalizer k≤3/2:=by linarith[le_of_abs_le he]
  rw[poissonNormalizer_nat k hkNat] at hlo hup
  exact ⟨hlo,hup⟩

lemma poissonNormalizer_nonTiny_window (κ:ℝ)(hκ:0<κ):
    ∃H:ℝ,0<H ∧ ∀h:ℝ,H≤h→∀k:ℕ,κ*Real.sqrt h≤(k:ℝ)→
      1≤k ∧ 1/2≤Real.sqrt (2*Real.pi*k)*poissonCenter k ∧
      Real.sqrt (2*Real.pi*k)*poissonCenter k≤3/2 ∧
      (poissonCenter k*Real.sqrt (k:ℝ))⁻¹≤2*Real.sqrt (2*Real.pi):=by
  obtain ⟨N,hN,hbound⟩:=poissonNormalizer_large_nat_bounds
  have hg:Tendsto (fun h:ℝ=>κ*Real.sqrt h) atTop atTop:=
    Filter.Tendsto.const_mul_atTop hκ Real.tendsto_sqrt_atTop
  obtain ⟨H0,hH0⟩:=eventually_atTop.1 (hg.eventually (eventually_ge_atTop N))
  let H:ℝ:=max H0 1
  have hH:0<H:=zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨H,hH,?_⟩
  intro h hh k hk
  have hNk:N≤(k:ℝ):=(hH0 h ((le_max_left _ _).trans hh)).trans hk
  have hk1:1≤k:=by exact_mod_cast hN.trans hNk
  have hkpos:0<(k:ℝ):=by exact_mod_cast (show 0<k by omega)
  have hpc:0<poissonCenter k:=by unfold poissonCenter;positivity
  have hsq:0<Real.sqrt (k:ℝ):=Real.sqrt_pos.mpr hkpos
  have hb:=hbound k hNk
  refine ⟨hk1,hb.1,hb.2,?_⟩
  rw[Real.sqrt_mul (by positivity:(0:ℝ)≤2*Real.pi)] at hb
  rw[←one_div]
  apply (div_le_iff₀ (mul_pos hpc hsq)).mpr
  nlinarith[hb.1]

lemma poisson_central_factor_bound_nonTiny (κ:ℝ)(hκ:0<κ):
    ∃H:ℝ,0<H ∧ ∀h:ℝ,H≤h→∀k:ℕ,κ*Real.sqrt h≤(k:ℝ)→
      ∀z:ℂ,‖z‖≤2→‖z/((poissonCenter k*Real.sqrt (k:ℝ):ℝ):ℂ)‖≤4*Real.sqrt (2*Real.pi):=by
  obtain ⟨H,hH,hbounds⟩:=poissonNormalizer_nonTiny_window κ hκ
  refine ⟨H,hH,?_⟩
  intro h hh k hk z hz
  have ht:=hbounds h hh k hk
  have hkpos:0<(k:ℝ):=by exact_mod_cast (show 0<k by omega)
  have hpc:0<poissonCenter k:=by unfold poissonCenter;positivity
  have hden:0<poissonCenter k*Real.sqrt (k:ℝ):=mul_pos hpc (Real.sqrt_pos.mpr hkpos)
  rw[norm_div,Complex.norm_of_nonneg hden.le,div_eq_mul_inv]
  apply (mul_le_mul hz ht.2.2.2 (inv_nonneg.mpr hden.le) (by norm_num:(0:ℝ)≤2)).trans_eq
  ring
end WP.Analysis
