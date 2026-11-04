import WPFormalization.Analysis.BorelGevrey
import WPFormalization.External.PainleveAnalyticData
import Mathlib

/-! The canonical CCH data actually satisfy the proved raw Borel Gevrey
estimate. The fixed angle, ray weights and thresholds are chosen from the
mature raw data fields. This proves the new order-uniform estimate; it does
not identify the actual GIKM native functions or the project jump table.
-/
noncomputable section
namespace WP.Analysis
open Complex MeasureTheory Set Filter Metric
namespace PA
abbrev Data := WP.External.PainleveAnalytic.CCHData
end PA

lemma painleve_laplaceAlong_eq_rayTail (H : ℂ → ℂ) (θ ξ : ℝ) :
    WP.External.PainleveAnalytic.laplaceAlong H θ ξ=laplaceRayTail H θ ξ 0 := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp [WP.External.PainleveAnalytic.laplaceAlong,WP.External.PainleveAnalytic.ray,
    laplaceRayTail,laplaceRayIntegrand,laplaceSlitFunction]
  rw [mul_comm Complex.I (θ:ℂ)]
  ring

lemma cch_rescaled_jump_gevrey (D : PA.Data) :
    ∃φ C B ξ₀:ℝ,0<φ ∧ φ<Real.pi/2 ∧ 0<C ∧ 0<B ∧ 0<ξ₀ ∧ ∀L:ℕ,∀ξ:ℝ,ξ₀≤ξ →
      ‖((ξ^(1/2:ℝ):ℝ):ℂ)*Complex.exp (ξ:ℂ)*
        (WP.External.PainleveAnalytic.laplaceAlong D.H₀ (-φ) ξ-
          WP.External.PainleveAnalytic.laplaceAlong D.H₀ φ ξ)-
        ((-2*Complex.I)*D.S)*(∑j∈Finset.range L,
          (Real.Gamma ((1/2:ℝ)+(j:ℝ))/ξ^j) • WP.coeff (fun z:ℂ => D.α (1+z)) j)‖≤
        C*B^L*(L.factorial:ℝ)/ξ^L := by
  obtain ⟨φ,hφ,hφπ,hgap,hφdist⟩ := exists_fixed_cut_angle D.r D.r_pos
  obtain ⟨bP,UP,hbP,hUP,hiP,huP⟩ := D.fixed_ray_L1 φ (by simpa only [abs_of_pos hφ] using hφ)
    (by simpa only [abs_of_pos hφ] using hφπ)
  obtain ⟨bN,UN,hbN,hUN,hiN,huN⟩ := D.fixed_ray_L1 (-φ) (by simpa only [abs_neg,abs_of_pos hφ] using hφ)
    (by simpa only [abs_neg,abs_of_pos hφ] using hφπ)
  have hH : AnalyticOnNhd ℂ D.H₀ firstBorelSlit := D.analytic
  have hform (z : ℂ) (hz : ‖z-1‖<2*D.r) (him : z.im≠0) :
      D.H₀ z=D.S*(Complex.sqrt (1-z))⁻¹*D.α z+D.β z := by
    exact D.local_form z (by simpa only [Metric.mem_ball,dist_eq_norm] using hz) (Or.inl him)
  have hhiP : IntegrableOn (fun t:ℝ => Real.exp (-(bP*t))*
      ‖D.H₀ ((t:ℂ)*Complex.exp ((φ:ℂ)*Complex.I))‖) (Ioi 0) := by
    simpa only [WP.External.PainleveAnalytic.ray,mul_comm Complex.I,neg_mul] using hiP
  have hhiN : IntegrableOn (fun t:ℝ => Real.exp (-(bN*t))*
      ‖D.H₀ ((t:ℂ)*Complex.exp (((-φ:ℝ):ℂ)*Complex.I))‖) (Ioi 0) := by
    simpa only [WP.External.PainleveAnalytic.ray,mul_comm Complex.I,neg_mul] using hiN
  have hhuP : (∫ t in Ioi 0,Real.exp (-(bP*t))*
      ‖D.H₀ ((t:ℂ)*Complex.exp ((φ:ℂ)*Complex.I))‖)≤UP := by
    simpa only [WP.External.PainleveAnalytic.ray,mul_comm Complex.I,neg_mul] using huP
  have hhuN : (∫ t in Ioi 0,Real.exp (-(bN*t))*
      ‖D.H₀ ((t:ℂ)*Complex.exp (((-φ:ℝ):ℂ)*Complex.I))‖)≤UN := by
    simpa only [WP.External.PainleveAnalytic.ray,mul_comm Complex.I,neg_mul] using huN
  obtain ⟨C,B,ξ₀,hC,hB,hξ₀,h⟩ := borel_rescaled_jump_gevrey D.H₀ D.α D.β D.S D.r φ bP bN UP UN
    D.r_pos hφ hφπ (by linarith [D.r_pos]) hφdist hH D.alpha_analytic D.beta_analytic hform
    hbP.le hbN.le hUP.le hUN.le hhiP hhiN hhuP hhuN
  refine ⟨φ,C,B,ξ₀,hφ,hφπ,hC,hB,hξ₀,?_⟩
  intro L ξ hξ
  simpa only [painleve_laplaceAlong_eq_rayTail] using h L ξ hξ
end WP.Analysis
