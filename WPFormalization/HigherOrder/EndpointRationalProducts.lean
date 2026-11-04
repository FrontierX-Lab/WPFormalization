import WPFormalization.Analysis.UniformTaylorRemainder
import WPFormalization.Analysis.Taylor
import WPFormalization.HigherOrder.EndpointFormal

/-! The actual finite shifted inverse product in endpointZ: common Cauchy-circle bounds, simultaneous Taylor tails, and exact identification with its formal product. No endpoint matching is assumed. -/
noncomputable section
namespace WP.HigherOrder
open PowerSeries

def endpointRationalProduct (j : ℕ) (z : ℂ) : ℂ :=
  ∏a∈Finset.range j,(1+((1/2-(a:ℝ):ℝ):ℂ)*z)⁻¹

lemma endpointRationalProduct_denominator_bound (n j a : ℕ) (hn : 1≤n) (hj : j≤n)
    (ha : a∈Finset.range j) (z : ℂ) (hz : ‖z‖≤1/(2*(n:ℝ))) :
    (1/2:ℝ) ≤ ‖1+((1/2-(a:ℝ):ℝ):ℂ)*z‖ := by
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have haR : (a:ℝ)≤n := by exact_mod_cast (Finset.mem_range.mp ha).le.trans hj
  have hc : ‖((1/2-(a:ℝ):ℝ):ℂ)‖ ≤ n := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith,by linarith [Nat.cast_nonneg (α:=ℝ) a]⟩
  have hmul : ‖((1/2-(a:ℝ):ℝ):ℂ)*z‖≤1/2 := by
    rw [norm_mul]
    calc
      _ ≤ (n:ℝ)*(1/(2*(n:ℝ))) := mul_le_mul hc hz (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have he := norm_sub_le (1+((1/2-(a:ℝ):ℝ):ℂ)*z) (((1/2-(a:ℝ):ℝ):ℂ)*z)
  simp only [add_sub_cancel_right,norm_one] at he
  linarith
lemma endpointRationalProduct_diff_closed (n j : ℕ) (hn : 1≤n) (hj : j≤n) :
    DifferentiableOn ℂ (endpointRationalProduct j) (Metric.closedBall 0 (1/(2*(n:ℝ)))) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_finsetProd
  intro a ha
  have hb := endpointRationalProduct_denominator_bound n j a hn hj ha z
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
  have hne : 1+((1/2-(a:ℝ):ℝ):ℂ)*z≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hb)
  have hlin : DifferentiableAt ℂ (fun w:ℂ => 1+((1/2-(a:ℝ):ℝ):ℂ)*w) z := by fun_prop
  exact hlin.inv hne
lemma endpointRationalProduct_norm_bound (n j : ℕ) (hn : 1≤n) (hj : j≤n)
    (z : ℂ) (hz : ‖z‖≤1/(2*(n:ℝ))) :
    ‖endpointRationalProduct j z‖≤(2:ℝ)^j := by
  unfold endpointRationalProduct
  rw [norm_prod]
  calc
    _ ≤ ∏a∈Finset.range j,(2:ℝ) := by
      apply Finset.prod_le_prod₀ (fun a ha => norm_nonneg _)
      intro a ha
      rw [norm_inv]
      have hb := endpointRationalProduct_denominator_bound n j a hn hj ha z hz
      calc
        _ ≤ (1/2:ℝ)⁻¹ := inv_anti₀ (by norm_num) hb
        _ = _ := by norm_num
    _ = _ := by simp
lemma endpointRationalProduct_taylor_remainder (n j N : ℕ) (hn : 1≤n) (hj : j≤n)
    (z : ℂ) (hz : ‖z‖≤1/(4*(n:ℝ))) :
    ‖endpointRationalProduct j z-(∑q∈Finset.range N,WP.coeff (endpointRationalProduct j) q*z^q)‖ ≤
      2*(2:ℝ)^j*(2*(n:ℝ)*‖z‖)^N := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hR : (0:ℝ)<1/(2*(n:ℝ)) := by positivity
  have hb := WP.Analysis.complex_taylor_remainder_bound (endpointRationalProduct j)
    (1/(2*(n:ℝ))) ((2:ℝ)^j) hR (by positivity) (endpointRationalProduct_diff_closed n j hn hj)
    (fun w hw => endpointRationalProduct_norm_bound n j hn hj w (by simpa only [Metric.mem_sphere,dist_zero_right] using le_of_eq hw))
    N z (by convert hz using 1 <;> ring)
  convert hb using 1
  congr 2
  field_simp
lemma endpointRationalProduct_analytic_zero (j : ℕ) : AnalyticAt ℂ (endpointRationalProduct j) 0 := by
  unfold endpointRationalProduct
  fun_prop (disch := simp)
lemma endpointRationalProduct_taylor (j : ℕ) :
    WP.Analysis.taylor (endpointRationalProduct j)=
      PowerSeries.map Complex.ofRealHom
        (∏a∈Finset.range j,(1+C (1/2-(a:ℝ))*PowerSeries.X : Series)⁻¹) := by
  induction j with
  | zero =>
    have he : endpointRationalProduct 0=fun _:ℂ => 1 := by funext z;simp [endpointRationalProduct]
    rw [he,WP.Analysis.taylor_const]
    simp
  | succ j ih =>
    have he : endpointRationalProduct (j+1)=fun z:ℂ =>
        endpointRationalProduct j z*(1+((1/2-(j:ℝ):ℝ):ℂ)*z)⁻¹ := by
      funext z
      simp only [endpointRationalProduct,Finset.prod_range_succ]
    have hlin : AnalyticAt ℂ (fun z:ℂ => 1+((1/2-(j:ℝ):ℝ):ℂ)*z) 0 := by fun_prop
    have hprod : WP.Analysis.taylor (endpointRationalProduct (j+1))=
        WP.Analysis.taylor (endpointRationalProduct j)*
          WP.Analysis.taylor (fun z:ℂ => (1+((1/2-(j:ℝ):ℝ):ℂ)*z)⁻¹) := by
      rw [he]
      exact WP.Analysis.taylor_mul (endpointRationalProduct_analytic_zero j) (hlin.inv (by simp))
    have htc : WP.Analysis.taylor (fun z:ℂ => ((1/2-(j:ℝ):ℝ):ℂ)*z)=
        C (((1/2-(j:ℝ):ℝ):ℂ))*PowerSeries.X := by
      simpa only [WP.Analysis.taylor_id] using
        WP.Analysis.taylor_const_mul (((1/2-(j:ℝ):ℝ):ℂ)) (fun z:ℂ => z)
    have htl : WP.Analysis.taylor (fun z:ℂ => 1+((1/2-(j:ℝ):ℝ):ℂ)*z)=
        1+C (((1/2-(j:ℝ):ℝ):ℂ))*PowerSeries.X := by
      have ht := WP.Analysis.taylor_add (f:=fun _:ℂ => 1)
        (g:=fun z:ℂ => ((1/2-(j:ℝ):ℝ):ℂ)*z) analyticAt_const (by fun_prop)
      simpa only [WP.Analysis.taylor_const,map_one,htc] using ht
    rw [hprod,ih,WP.Analysis.taylor_inv hlin (by simp),htl,
      Finset.prod_range_succ,map_mul]
    congr 1
    rw [WP.Analysis.map_inv_ofReal _ (by simp),map_add,map_one,map_mul,
      PowerSeries.map_C,PowerSeries.map_X] <;> rfl

end WP.HigherOrder
