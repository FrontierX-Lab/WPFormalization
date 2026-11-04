import Mathlib.Probability.Moments.Variance
import WPFormalization.Tight.ConnectedScale
noncomputable section
namespace WP.BoltzmannCusp
open Set MeasureTheory ProbabilityTheory

lemma centered_event_of_relative_event (G ψ m n ε C:ℝ) (hG:0<G) (hψ:0≤ψ)
    (hε:0<ε) (hC:0≤C) (hbias:|m-2*G*ψ|≤C*ψ) (hlarge:C≤ε*G)
    (he:ε≤|(1+n/G)/(1+2*ψ)-1|) : ε*G*(1+2*ψ)/2≤|n-m| := by
  have hd : 0<1+2*ψ := by positivity
  have hr : (1+n/G)/(1+2*ψ)-1=(n-2*G*ψ)/(G*(1+2*ψ)) := by field_simp;ring
  rw [hr,abs_div,abs_of_pos (mul_pos hG hd)] at he
  have hl := (le_div_iff₀ (mul_pos hG hd)).mp he
  have hb : |m-2*G*ψ|≤ε*G*(1+2*ψ)/2 := by
    have hs := mul_le_mul_of_nonneg_right hlarge hψ
    nlinarith [mul_pos hε hG]
  have ht : |n-2*G*ψ|≤|n-m|+|m-2*G*ψ| := by
    calc
      |n-2*G*ψ|=|(n-m)+(m-2*G*ψ)| := by congr 1;ring
      _≤|n-m|+|m-2*G*ψ| := abs_add_le _ _
  nlinarith

lemma chebyshev_variance_ratio_bound (V C G ψ ε:ℝ) (hV:V≤C*G*(ψ+ψ^2))
    (hC:0≤C) (hG:0<G) (hψ:0≤ψ) (hε:0<ε) :
    V/(ε*G*(1+2*ψ)/2)^2≤C/(ε^2*G) := by
  have hd : 0<(ε*G*(1+2*ψ)/2)^2 := sq_pos_of_pos (by positivity)
  apply (div_le_iff₀ hd).mpr
  have hg : G≠0 := ne_of_gt hG
  have he : ε≠0 := ne_of_gt hε
  have hprod : 0≤C*G := mul_nonneg hC hG.le
  have hpoly : ψ+ψ^2≤(1+2*ψ)^2/4 := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hpoly hprod
  have hid : C/(ε^2*G)*(ε*G*(1+2*ψ)/2)^2=C*G*((1+2*ψ)^2/4) := by
    field_simp
    <;>ring
  rw [hid]
  exact hV.trans ht

lemma measure_relative_event_le (μ:Measure ℕ) [IsProbabilityMeasure μ]
    (hX:MemLp (fun n:ℕ=>(n:ℝ)) 2 μ) (G ψ ε Cb Cv:ℝ)
    (hG:0<G) (hψ:0≤ψ) (hε:0<ε) (hCb:0≤Cb) (hCv:0≤Cv)
    (hbias:|(∫n:ℕ,(n:ℝ) ∂μ)-2*G*ψ|≤Cb*ψ) (hlarge:Cb≤ε*G)
    (hV:variance (fun n:ℕ=>(n:ℝ)) μ≤Cv*G*(ψ+ψ^2)) :
    μ {n:ℕ|ε≤|(1+(n:ℝ)/G)/(1+2*ψ)-1|}≤ENNReal.ofReal (Cv/(ε^2*G)) := by
  calc
    μ {n:ℕ|ε≤|(1+(n:ℝ)/G)/(1+2*ψ)-1|}≤
        μ {n:ℕ|ε*G*(1+2*ψ)/2≤|(n:ℝ)-(∫n:ℕ,(n:ℝ) ∂μ)|} := by
      apply measure_mono
      intro n hn
      exact centered_event_of_relative_event G ψ _ _ ε Cb hG hψ hε hCb hbias hlarge hn
    _≤ENNReal.ofReal (variance (fun n:ℕ=>(n:ℝ)) μ/(ε*G*(1+2*ψ)/2)^2) :=
      meas_ge_le_variance_div_sq hX (by positivity)
    _≤ENNReal.ofReal (Cv/(ε^2*G)) := ENNReal.ofReal_le_ofReal
      (chebyshev_variance_ratio_bound _ Cv G ψ ε hV hCv hG hψ hε)
end WP.BoltzmannCusp
namespace WP.BoltzmannCusp
open Set MeasureTheory ProbabilityTheory
lemma measure_nat_markov (μ:Measure ℕ) [IsProbabilityMeasure μ]
    (hI:Integrable (fun n:ℕ=>(n:ℝ)) μ) (R:ℝ) (hR:0<R) :
    μ {n:ℕ|R≤(n:ℝ)}≤ENNReal.ofReal ((∫n:ℕ,(n:ℝ) ∂μ)/R) := by
  have h := (hI.div_const R).measure_le_integral
    (ae_of_all μ (fun n=>div_nonneg (Nat.cast_nonneg n) hR.le))
    (s:={n:ℕ|R≤(n:ℝ)}) (fun n hn=>by
      apply (le_div_iff₀ hR).mpr
      simpa only [one_mul] using (show R≤(n:ℝ) from hn))
  simpa only [integral_div] using h
end WP.BoltzmannCusp
namespace WP.BoltzmannCusp
open Set MeasureTheory ProbabilityTheory
lemma centered_event_of_scaled_event (M m n ε:ℝ) (hM:0<M)
    (hbias:|m-M|≤ε*M/2) (he:ε≤|n/M-1|) : ε*M/2≤|n-m| := by
  have hr : n/M-1=(n-M)/M := by field_simp
  rw [hr,abs_div,abs_of_pos hM] at he
  have hl := (le_div_iff₀ hM).mp he
  have ht : |n-M|≤|n-m|+|m-M| := by
    calc
      |n-M|=|(n-m)+(m-M)| := by congr 1;ring
      _≤|n-m|+|m-M| := abs_add_le _ _
  linarith

lemma diverging_variance_ratio_bound (V C G H ψ ε:ℝ) (hV:V≤C*G*(ψ+ψ^2))
    (hC:0≤C) (hG:0<G) (hGH:G≤H) (hψ:0<ψ) (hε:0<ε) :
    V/(ε*(H*ψ)/2)^2≤(4*C/ε^2)*(1/(H*ψ)+1/G) := by
  have hH : 0<H := hG.trans_le hGH
  have hd : 0<(ε*(H*ψ)/2)^2 := sq_pos_of_pos (by positivity)
  apply (div_le_iff₀ hd).mpr
  have hh : G≤H^2/G := (le_div_iff₀ hG).mpr (by nlinarith)
  have h₁ := mul_le_mul_of_nonneg_left hGH (show 0≤C*ψ by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hh (show 0≤C*ψ^2 by positivity)
  have hid : (4*C/ε^2)*(1/(H*ψ)+1/G)*(ε*(H*ψ)/2)^2=
      C*H*ψ+C*(H^2/G)*ψ^2 := by field_simp;ring
  rw [hid]
  nlinarith

lemma measure_scaled_event_le (μ:Measure ℕ) [IsProbabilityMeasure μ]
    (hX:MemLp (fun n:ℕ=>(n:ℝ)) 2 μ) (G H ψ ε Cb Cv:ℝ)
    (hG:0<G) (hGH:G≤H) (hψ:0<ψ) (hε:0<ε) (hCv:0≤Cv)
    (hbias:|(∫n:ℕ,(n:ℝ) ∂μ)-H*ψ|≤Cb*ψ) (hlarge:2*Cb≤ε*H)
    (hV:variance (fun n:ℕ=>(n:ℝ)) μ≤Cv*G*(ψ+ψ^2)) :
    μ {n:ℕ|ε≤|(n:ℝ)/(H*ψ)-1|}≤ENNReal.ofReal ((4*Cv/ε^2)*(1/(H*ψ)+1/G)) := by
  have hH : 0<H := hG.trans_le hGH
  have hbias' : |(∫n:ℕ,(n:ℝ) ∂μ)-H*ψ|≤ε*(H*ψ)/2 := by
    have := mul_le_mul_of_nonneg_right hlarge hψ.le
    nlinarith
  calc
    μ {n:ℕ|ε≤|(n:ℝ)/(H*ψ)-1|}≤
        μ {n:ℕ|ε*(H*ψ)/2≤|(n:ℝ)-(∫n:ℕ,(n:ℝ) ∂μ)|} := by
      apply measure_mono
      intro n hn
      exact centered_event_of_scaled_event _ _ _ ε (by positivity) hbias' hn
    _≤ENNReal.ofReal (variance (fun n:ℕ=>(n:ℝ)) μ/(ε*(H*ψ)/2)^2) :=
      meas_ge_le_variance_div_sq hX (by positivity)
    _≤ENNReal.ofReal ((4*Cv/ε^2)*(1/(H*ψ)+1/G)) := ENNReal.ofReal_le_ofReal
      (diverging_variance_ratio_bound _ Cv G H ψ ε hV hCv hG hGH hψ hε)
end WP.BoltzmannCusp
