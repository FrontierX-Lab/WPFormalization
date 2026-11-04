import WPFormalization.Analysis.FiniteExpGevrey
/-! Actual Gevrey-one matching under multiplication. Uniform finite Taylor
bounds control products of the truncated polynomials. The factorial coefficient
bound is deduced from the actual all-order error itself, so the final product
rule has no separate coefficient-bound premise. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open PowerSeries Filter
open scoped Topology

lemma complex_taylor_linear_factorial_bound (f:ℂ→ℂ) (B M:ℝ) (hB:0<B) (hM:0≤M)
    (K:ℕ) (hd:DifferentiableOn ℂ f (Metric.closedBall 0 (1/(2*B*((K:ℝ)+1)))))
    (hc:∀z∈Metric.sphere (0:ℂ) (1/(2*B*((K:ℝ)+1))),‖f z‖≤M)
    (z:ℂ) (hz:‖z‖≤1/(4*B*((K:ℝ)+1))) :
    ‖f z-∑i∈Finset.range (K+1),WP.coeff f i*z^i‖≤
      2*M*(2*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)*‖z‖^(K+1) := by
  have hR:0<1/(2*B*((K:ℝ)+1)) := by positivity
  have hzR:‖z‖≤(1/(2*B*((K:ℝ)+1)))/2 := by
    convert hz using 1;field_simp;ring
  have he:=complex_taylor_remainder_bound f _ M hR hM hd hc (K+1) z hzR
  apply he.trans
  have hratio:‖z‖/(1/(2*B*((K:ℝ)+1)))=(2*B*‖z‖)*((K+1:ℕ):ℝ) := by
    push_cast
    field_simp
  rw [hratio,mul_pow]
  calc
    _ ≤ 2*M*((2*B*‖z‖)^(K+1)*((Real.exp 1)^(K+1)*((K+1).factorial:ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (order_pow_le_exp_factorial (K+1))
        (pow_nonneg (by positivity) _)) (by positivity)
    _ = _ := by simp only [mul_pow];ring

lemma truncatedSeriesPolynomial_mul_coeff (f g:WP.HigherOrder.Series) (K n:ℕ) (hn:n≤K) :
    WP.coeff (fun z=>truncatedSeriesPolynomial f K z*truncatedSeriesPolynomial g K z) n=
      ((PowerSeries.coeff n (f*g):ℝ):ℂ) := by
  rw [←taylor_coeff,taylor_mul (truncatedSeriesPolynomial_analytic f K 0)
    (truncatedSeriesPolynomial_analytic g K 0),PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro ij hij
  have he:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  simp only [taylor_coeff,truncatedSeriesPolynomial_coeff,ite_eq_left (show ij.1≤K by omega),
    ite_eq_left (show ij.2≤K by omega)]

lemma truncatedSeriesPolynomial_mul_remainder (f g:WP.HigherOrder.Series) (C B:ℝ)
    (hC:0≤C) (hB:0<B)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (hg:∀n,|PowerSeries.coeff n g|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ) (z:ℂ) (hz:‖z‖≤1/(4*B*((K:ℝ)+1))) :
    ‖truncatedSeriesPolynomial f K z*truncatedSeriesPolynomial g K z-
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (f*g):ℝ):ℂ)*z^i‖≤
      8*C^2*(2*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)*‖z‖^(K+1) := by
  have hd:DifferentiableOn ℂ (fun w=>truncatedSeriesPolynomial f K w*truncatedSeriesPolynomial g K w)
      (Metric.closedBall 0 (1/(2*B*((K:ℝ)+1)))) := by
    intro w hw
    exact ((truncatedSeriesPolynomial_analytic f K w).mul
      (truncatedSeriesPolynomial_analytic g K w)).differentiableAt.differentiableWithinAt
  have hc:∀w∈Metric.sphere (0:ℂ) (1/(2*B*((K:ℝ)+1))),
      ‖truncatedSeriesPolynomial f K w*truncatedSeriesPolynomial g K w‖≤4*C^2 := by
    intro w hw
    have hwR:‖w‖≤1/(2*B*((K:ℝ)+1)) := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using Metric.sphere_subset_closedBall hw
    rw [norm_mul]
    have he:=mul_le_mul (truncatedSeriesPolynomial_norm_bound f C B hC hB hf K w hwR)
      (truncatedSeriesPolynomial_norm_bound g C B hC hB hg K w hwR) (norm_nonneg _) (by positivity)
    nlinarith
  have he:=complex_taylor_linear_factorial_bound
    (fun w=>truncatedSeriesPolynomial f K w*truncatedSeriesPolynomial g K w) B (4*C^2) hB
    (by positivity) K hd hc z hz
  have hcoef:(∑i∈Finset.range (K+1),WP.coeff
      (fun w=>truncatedSeriesPolynomial f K w*truncatedSeriesPolynomial g K w) i*z^i)=
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (f*g):ℝ):ℂ)*z^i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [truncatedSeriesPolynomial_mul_coeff f g K i (by have := Finset.mem_range.mp hi;omega)]
  rw [hcoef] at he
  convert he using 1;ring


def inversePowerTruncation (f:WP.HigherOrder.Series) (K:ℕ) (h:ℝ) : ℝ :=
  ∑i∈Finset.range (K+1),PowerSeries.coeff i f/h^i

def GevreyOneAsymptotic (F:ℝ→ℝ) (f:WP.HigherOrder.Series) : Prop :=
  ∃C B c h₀:ℝ,0<C ∧ 0<B ∧ 0<c ∧ 0<h₀ ∧ ∀K:ℕ,∀h:ℝ,
    h₀≤h → (K:ℝ)≤c*h → |F h-inversePowerTruncation f K h|≤
      C*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1)

lemma GevreyOneAsymptotic.coeff_bound (F:ℝ→ℝ) (f:WP.HigherOrder.Series)
    (hF:GevreyOneAsymptotic F f) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀n:ℕ,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ) := by
  obtain ⟨C,B,c,h₀,hC,hB,hc,hh₀,herr⟩:=hF
  refine ⟨C+|PowerSeries.constantCoeff f|,B,by positivity,hB,?_⟩
  intro n
  cases n with
  | zero=>simp only [PowerSeries.coeff_zero_eq_constantCoeff,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one];linarith
  | succ n=>
    have hcoeff:|PowerSeries.coeff (n+1) f|≤C*B^(n+1)*((n+1).factorial:ℝ) := by
      let A:ℝ:=C*B^(n+1)*((n+1).factorial:ℝ)
      let D:ℝ:=C*B^(n+2)*((n+2).factorial:ℝ)
      have hlim:Tendsto (fun h:ℝ=>A+D/h) atTop (𝓝 A) := by
        have hd:Tendsto (fun h:ℝ=>D*h⁻¹) atTop (𝓝 0) := by
          simpa only [mul_zero] using (tendsto_const_nhds : Tendsto (fun _:ℝ=>D) atTop (𝓝 D)).mul tendsto_inv_atTop_zero
        simpa only [div_eq_mul_inv,add_zero] using (tendsto_const_nhds : Tendsto (fun _:ℝ=>A) atTop (𝓝 A)).add hd
      change |PowerSeries.coeff (n+1) f|≤A
      apply ge_of_tendsto hlim
      filter_upwards [eventually_ge_atTop h₀,eventually_ge_atTop (((n+1:ℕ):ℝ)/c)] with h hh hwindow
      have hp:0<h:=lt_of_lt_of_le hh₀ hh
      have hw:(n+1:ℕ)≤c*h := by
        have he:((n+1:ℕ):ℝ)≤h*c := (div_le_iff₀ hc).mp hwindow
        simpa only [mul_comm] using he
      have hw₀:(n:ℝ)≤c*h := by exact le_trans (by norm_num) hw
      have he₀:=herr n h hh hw₀
      have he₁:=herr (n+1) h hh hw
      have hdiff:inversePowerTruncation f (n+1) h-inversePowerTruncation f n h=
          PowerSeries.coeff (n+1) f/h^(n+1) := by
        dsimp only [inversePowerTruncation]
        rw [Finset.sum_range_succ]
        ring
      have he:|PowerSeries.coeff (n+1) f/h^(n+1)|≤
          C*B^(n+2)*((n+2).factorial:ℝ)/h^(n+2)+C*B^(n+1)*((n+1).factorial:ℝ)/h^(n+1) := by
        rw [←hdiff]
        calc
          _ ≤ |inversePowerTruncation f (n+1) h-F h|+|F h-inversePowerTruncation f n h| := abs_sub_le _ _ _
          _ ≤ _ := add_le_add (by simpa only [abs_sub_comm,Nat.add_assoc] using he₁) he₀
      have hpow:0<h^(n+1):=pow_pos hp _
      rw [abs_div,abs_of_pos hpow] at he
      have he':|PowerSeries.coeff (n+1) f|≤
          (C*B^(n+2)*((n+2).factorial:ℝ)/h^(n+2)+C*B^(n+1)*((n+1).factorial:ℝ)/h^(n+1))*h^(n+1) :=
        (div_le_iff₀ hpow).mp he
      convert he' using 1
      dsimp[A,D]
      rw [show n+2=(n+1)+1 by omega,pow_succ]
      field_simp
      ring
    exact hcoeff.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith[abs_nonneg (PowerSeries.constantCoeff f)] : C≤C+|PowerSeries.constantCoeff f|)
      (pow_nonneg hB.le _)) (Nat.cast_nonneg _))


lemma truncatedSeriesPolynomial_mul_real_remainder (f g:WP.HigherOrder.Series) (C B:ℝ)
    (hC:0≤C) (hB:0<B)
    (hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ))
    (hg:∀n,|PowerSeries.coeff n g|≤C*B^n*(n.factorial:ℝ))
    (K:ℕ) (h:ℝ) (hh:0<h) (hwindow:4*B*((K:ℝ)+1)≤h) :
    |inversePowerTruncation f K h*inversePowerTruncation g K h-inversePowerTruncation (f*g) K h|≤
      8*C^2*(2*B*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1) := by
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(4*B*((K:ℝ)+1)) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
    exact one_div_le_one_div_of_le (by positivity) hwindow
  have he:=truncatedSeriesPolynomial_mul_remainder f g C B hC hB hf hg K ((1/h:ℝ):ℂ) hz
  have hp (s:WP.HigherOrder.Series):truncatedSeriesPolynomial s K ((1/h:ℝ):ℂ)=
      ((inversePowerTruncation s K h):ℂ) := by
    rw [truncatedSeriesPolynomial_real]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow,one_pow,mul_one_div]
  have hq:(∑i∈Finset.range (K+1),((PowerSeries.coeff i (f*g):ℝ):ℂ)*((1/h:ℝ):ℂ)^i)=
      ((inversePowerTruncation (f*g) K h):ℂ) := by
    change truncatedSeriesPolynomial (f*g) K ((1/h:ℝ):ℂ)=_
    exact hp (f*g)
  rw [hp,hp,hq,←Complex.ofReal_mul,←Complex.ofReal_sub] at he
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh),div_pow,one_pow] at he
  convert he using 1;ring

lemma GevreyOneAsymptotic.mul (F G:ℝ→ℝ) (f g:WP.HigherOrder.Series)
    (hF:GevreyOneAsymptotic F f) (hG:GevreyOneAsymptotic G g) :
    GevreyOneAsymptotic (fun h=>F h*G h) (f*g) := by
  obtain ⟨Cf,Bf,hCf,hBf,hfc⟩:=GevreyOneAsymptotic.coeff_bound F f hF
  obtain ⟨Cg,Bg,hCg,hBg,hgc⟩:=GevreyOneAsymptotic.coeff_bound G g hG
  obtain ⟨CF,BF,cF,hF₀,hCF,hBF,hcF,hhF,hFerr⟩:=hF
  obtain ⟨CG,BG,cG,hG₀,hCG,hBG,hcG,hhG,hGerr⟩:=hG
  let C₀:ℝ:=Cf+Cg
  let B₀:ℝ:=Bf+Bg
  have hC₀:0<C₀:=by dsimp[C₀];positivity
  have hB₀:0<B₀:=by dsimp[B₀];positivity
  have hf:∀n,|PowerSeries.coeff n f|≤C₀*B₀^n*(n.factorial:ℝ):=by
    intro n
    apply (hfc n).trans
    dsimp[C₀,B₀]
    gcongr <;> linarith
  have hg:∀n,|PowerSeries.coeff n g|≤C₀*B₀^n*(n.factorial:ℝ):=by
    intro n
    apply (hgc n).trans
    dsimp[C₀,B₀]
    gcongr <;> linarith
  let c:ℝ:=min cF (min cG (1/(8*B₀)))
  let H:ℝ:=max (max hF₀ hG₀) (max 1 (8*B₀))
  let MG:ℝ:=|PowerSeries.coeff 0 g|+CG*BG
  have hMG:0<MG:=by dsimp[MG];positivity
  let B:ℝ:=BF+BG+2*B₀*Real.exp 1
  let C:ℝ:=CF*MG+2*C₀*CG+8*C₀^2
  refine ⟨C,B,c,H,by dsimp[C];positivity,by dsimp[B];positivity,
    lt_min hcF (lt_min hcG (by positivity)),
    lt_of_lt_of_le hhF ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro K h hhH hK
  have hhF₀:hF₀≤h:=((le_max_left _ _).trans (le_max_left _ _)).trans hhH
  have hhG₀:hG₀≤h:=((le_max_right _ _).trans (le_max_left _ _)).trans hhH
  have hh1:1≤h:=((le_max_left _ _).trans (le_max_right _ _)).trans hhH
  have hhB:8*B₀≤h:=((le_max_right _ _).trans (le_max_right _ _)).trans hhH
  have hh:0<h:=lt_of_lt_of_le zero_lt_one hh1
  have hKF:(K:ℝ)≤cF*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hh.le)
  have hKG:(K:ℝ)≤cG*h:=hK.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) hh.le)
  have hKr:(K:ℝ)≤(1/(8*B₀))*h:=hK.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) hh.le)
  have hwindow:4*B₀*((K:ℝ)+1)≤h:=by
    have hk':(K:ℝ)*(8*B₀)≤h := (le_div_iff₀ (by positivity:0<8*B₀)).mp
      (by simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using hKr)
    nlinarith
  have hGval:|G h|≤MG:=by
    have he:=hGerr 0 h hhG₀ (by have hp:=mul_pos hcG hh;simpa only [Nat.cast_zero] using hp.le)
    simp only [inversePowerTruncation,Finset.sum_range_one,pow_zero,div_one,Nat.zero_add,pow_one,
      Nat.factorial_one,Nat.cast_one,mul_one] at he
    calc
      _ = |(G h-PowerSeries.coeff 0 g)+PowerSeries.coeff 0 g|:=by congr 1;ring
      _ ≤ |G h-PowerSeries.coeff 0 g|+|PowerSeries.coeff 0 g|:=abs_add_le _ _
      _ ≤ CG*BG/h+|PowerSeries.coeff 0 g|:=add_le_add he le_rfl
      _ ≤ MG:=by dsimp[MG];have hd:=div_le_self (mul_nonneg hCG.le hBG.le) hh1;linarith
  have hP:|inversePowerTruncation f K h|≤2*C₀:=by
    have hz:‖((1/h:ℝ):ℂ)‖≤1/(2*B₀*((K:ℝ)+1)):=by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have he:=truncatedSeriesPolynomial_norm_bound f C₀ B₀ hC₀.le hB₀ hf K ((1/h:ℝ):ℂ) hz
    rw [truncatedSeriesPolynomial_real,Complex.norm_real,Real.norm_eq_abs] at he
    convert he using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow,one_pow,mul_one_div]
  have htail:=truncatedSeriesPolynomial_mul_real_remainder f g C₀ B₀ hC₀.le hB₀ hf hg K h hh hwindow
  have hprod:|F h*G h-inversePowerTruncation f K h*inversePowerTruncation g K h|≤
      MG*(CF*BF^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
      (2*C₀)*(CG*BG^(K+1)*((K+1).factorial:ℝ)/h^(K+1)):=by
    have he:F h*G h-inversePowerTruncation f K h*inversePowerTruncation g K h=
        (F h-inversePowerTruncation f K h)*G h+
        inversePowerTruncation f K h*(G h-inversePowerTruncation g K h):=by ring
    rw [he]
    apply (abs_add_le _ _).trans
    simp only [abs_mul]
    have hfE:=hFerr K h hhF₀ hKF
    have hgE:=hGerr K h hhG₀ hKG
    have he₁:=mul_le_mul hfE hGval (abs_nonneg _) (by positivity)
    have he₂:=mul_le_mul hP hgE (abs_nonneg _) (by positivity)
    nlinarith
  have hbF:BF≤B:=by
    dsimp[B]
    have hp:0<2*B₀*Real.exp 1:=by positivity
    linarith
  have hbG:BG≤B:=by
    dsimp[B]
    have hp:0<2*B₀*Real.exp 1:=by positivity
    linarith
  have hbP:2*B₀*Real.exp 1≤B:=by dsimp[B];linarith
  calc
    _ ≤ |F h*G h-inversePowerTruncation f K h*inversePowerTruncation g K h|+
        |inversePowerTruncation f K h*inversePowerTruncation g K h-inversePowerTruncation (f*g) K h|:=abs_sub_le _ _ _
    _ ≤ MG*(CF*BF^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        (2*C₀)*(CG*BG^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        8*C₀^2*(2*B₀*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=add_le_add hprod htail
    _ ≤ MG*(CF*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        (2*C₀)*(CG*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        8*C₀^2*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by gcongr
    _ = _:=by dsimp[C];ring

end WP.Analysis
