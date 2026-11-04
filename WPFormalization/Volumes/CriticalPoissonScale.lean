import WPFormalization.Volumes.CriticalInversePsi
import WPFormalization.Analysis.PoissonNormalizer
/-! The true critical density supplies h*Psi>=h and a bounded inverse unit; the exact rescaled inverse Poisson-Stirling series and actual Poisson normalizer have uniform errors. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma CriticalKernelUnits.Psi_large_near_critical (k:CriticalKernelUnits) :
    ∃R:ℝ,0<R ∧ R<y₀ ∧ ∀δ∈Ioo (0:ℝ) R,
      1≤WP.Psi (XR (y₀-δ)) ∧ 0≤(WP.Psi (XR (y₀-δ)))⁻¹ ∧ (WP.Psi (XR (y₀-δ)))⁻¹≤1 := by
  obtain ⟨R,hR,hRy,hunit,htrace⟩:=k.inversePsiUnit_common_bound
  refine ⟨R,hR,hRy,?_⟩
  intro δ hδ
  have hY:0<y₀-δ:=by linarith[hδ.2]
  have hYc:y₀-δ∈Ico (0:ℝ) y₀:=⟨hY.le,by linarith[hδ.1]⟩
  have hd:=density_strictMonoOn ⟨le_rfl,y₀_pos⟩ hYc hY
  rw[density_zero_value] at hd
  have hP:0<WP.Psi (XR (y₀-δ)):=by
    dsimp only[WP.Psi]
    rw[inverseY_eq_of_root _ _ hYc.2.le rfl]
    exact half_pos hd
  have ht:‖((1/WP.Psi (XR (y₀-δ)):ℝ):ℂ)‖≤1:=by
    rw[←htrace δ hδ]
    exact (hunit (δ:ℂ) (by rw[Complex.norm_of_nonneg hδ.1.le];exact hδ.2.le)).2
  simp only[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hP)] at ht
  have hPle:1≤WP.Psi (XR (y₀-δ)):=by
    have hh:1≤1*WP.Psi (XR (y₀-δ)):=(div_le_iff₀ hP).mp ht
    simpa only[one_mul] using hh
  exact ⟨hPle,inv_nonneg.mpr hP.le,by simpa only[one_div] using ht⟩

lemma inversePowerTruncation_rescale_inv (f:HigherOrder.Series) (ψ h:ℝ) (K:ℕ) :
    inversePowerTruncation (PowerSeries.rescale ψ⁻¹ f) K h=inversePowerTruncation f K (h*ψ) := by
  dsimp only[inversePowerTruncation]
  apply Finset.sum_congr rfl
  intro j hj
  simp only[PowerSeries.coeff_rescale,mul_pow,div_eq_mul_inv,inv_pow,mul_inv_rev]
  ring

lemma rescale_unit_interval_gevreyTwo_bound (f:HigherOrder.Series) (C B t:ℝ)
    (hC:0≤C) (hB:0≤B) (ht:0≤t) (ht1:t≤1)
    (hf:∀j,|PowerSeries.coeff j f|≤C*B^j*(j.factorial:ℝ)) (j:ℕ) :
    |PowerSeries.coeff j (PowerSeries.rescale t f)|≤C*B^j*(j.factorial:ℝ)^2 := by
  rw[PowerSeries.coeff_rescale,abs_mul,abs_pow,abs_of_nonneg ht]
  have hp:t^j≤1:=pow_le_one₀ ht ht1
  have hf1:1≤(j.factorial:ℝ):=by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos j)
  have hfact:(j.factorial:ℝ)≤(j.factorial:ℝ)^2:=by nlinarith
  calc _ ≤ 1*(C*B^j*(j.factorial:ℝ)):=mul_le_mul hp (hf j) (abs_nonneg _) (by positivity)
       _ ≤ _:=by simp only[one_mul];exact mul_le_mul_of_nonneg_left hfact (by positivity)

lemma CriticalKernelUnits.inverse_poisson_uniform_scaled_data (k:CriticalKernelUnits) :
    ∃R C B c H M:ℝ,0<R ∧ R<y₀ ∧ 0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧ 0<M ∧
      ∀δ∈Ioo (0:ℝ) R,
      let ψ:ℝ:=WP.Psi (XR (y₀-δ))
      1≤ψ ∧
      (∀j:ℕ,|PowerSeries.coeff j (PowerSeries.rescale ψ⁻¹ (HigherOrder.poissonStirlingSeries⁻¹))|≤C*B^j*(j.factorial:ℝ)^2) ∧
      ∀h:ℝ,H≤h→|(poissonNormalizer (h*ψ))⁻¹|≤M ∧ ∀K:ℕ,(K:ℝ)≤c*h→
        |(poissonNormalizer (h*ψ))⁻¹-inversePowerTruncation
          (PowerSeries.rescale ψ⁻¹ (HigherOrder.poissonStirlingSeries⁻¹)) K h|≤
          C*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1) := by
  obtain ⟨R,hR,hRy,hPsi⟩:=k.Psi_large_near_critical
  obtain ⟨Cc,Bc,hCc,hBc,hcoeff⟩:=GevreyOneAsymptotic.coeff_bound
    (fun x=>(poissonNormalizer x)⁻¹) (HigherOrder.poissonStirlingSeries⁻¹) poissonNormalizer_inv_gevrey_one
  obtain ⟨Ce,Be,c,He,hCe,hBe,hc,hHe,herror⟩:=GevreyOneAsymptotic.uniform_above_linear_scale
    (fun x=>(poissonNormalizer x)⁻¹) (HigherOrder.poissonStirlingSeries⁻¹) poissonNormalizer_inv_gevrey_one 1 zero_lt_one
  let C:ℝ:=max Cc Ce
  let B:ℝ:=max Bc Be
  let H:ℝ:=max He 1
  let M:ℝ:=Ce*Be+1
  have hC:0<C:=hCc.trans_le (le_max_left _ _)
  have hB:0<B:=hBc.trans_le (le_max_left _ _)
  have hH:0<H:=hHe.trans_le (le_max_left _ _)
  have hM:0<M:=by dsimp[M];positivity
  refine ⟨R,C,B,c,H,M,hR,hRy,hC,hB,hc,hH,hM,?_⟩
  intro δ hδ
  dsimp only
  let ψ:ℝ:=WP.Psi (XR (y₀-δ))
  have hψ:=hPsi δ hδ
  refine ⟨hψ.1,?_,?_⟩
  · intro j
    exact (rescale_unit_interval_gevreyTwo_bound (HigherOrder.poissonStirlingSeries⁻¹)
      Cc Bc ψ⁻¹ hCc.le hBc.le hψ.2.1 hψ.2.2 hcoeff j).trans (by dsimp[C,B];gcongr <;>exact le_max_left _ _)
  · intro h hhH
    have hhE:He≤h:=(le_max_left _ _).trans hhH
    have hh1:1≤h:=(le_max_right _ _).trans hhH
    have hh:0<h:=zero_lt_one.trans_le hh1
    have hx:1*h≤h*ψ:=by nlinarith[hψ.1]
    have hzero:=herror 0 h (h*ψ) hhE hx (by simpa only[Nat.cast_zero] using (mul_pos hc hh).le)
    have hzero':|(poissonNormalizer (h*ψ))⁻¹-1|≤Ce*Be/h := by
      simpa[inversePowerTruncation,PowerSeries.coeff_zero_eq_constantCoeff] using hzero
    constructor
    · have hb:Ce*Be/h≤Ce*Be:=div_le_self (by positivity) hh1
      have ht:|(poissonNormalizer (h*ψ))⁻¹|≤|(poissonNormalizer (h*ψ))⁻¹-1|+1:=by
        simpa only[sub_add_cancel,abs_one] using abs_add_le ((poissonNormalizer (h*ψ))⁻¹-1) 1
      dsimp[M]
      linarith
    · intro K hK
      rw[inversePowerTruncation_rescale_inv]
      apply (herror K h (h*ψ) hhE hx hK).trans
      have hfac1:1≤((K+1).factorial:ℝ):=by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (K+1))
      have hfac:((K+1).factorial:ℝ)≤((K+1).factorial:ℝ)^2:=by nlinarith
      dsimp only[C,B]
      gcongr
      · exact le_max_right _ _
      · exact le_max_right _ _
end WP.Analysis
