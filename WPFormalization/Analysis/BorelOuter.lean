import WPFormalization.Analysis.BorelLocalCut
import WPFormalization.Analysis.BorelRayTails
import Mathlib

/-! The exact local-cut integral and both unchanged infinite rays give a
truncation-independent exponential outer error. This is derived from raw
slit analyticity, the local square-root germ and fixed-ray weighted L1 data;
no conclusion about a normalized Painleve jump is assumed.
-/
noncomputable section
namespace WP.Analysis
open Complex MeasureTheory Set Filter Metric
open scoped Interval

lemma laplaceRay_decomposition (H : ℂ → ℂ) (θ ξ A : ℝ) (hA : 0≤A)
    (hi : IntegrableOn (laplaceRayIntegrand H θ ξ) (Ioi 0)) :
    laplaceRayTail H θ ξ 0=radialSegmentIntegral (laplaceSlitFunction H ξ) θ 0 A+
      laplaceRayTail H θ ξ A := by
  have hs := intervalIntegral.integral_Ioi_sub_Ioi hi hA
  change laplaceRayTail H θ ξ 0-laplaceRayTail H θ ξ A=
    radialSegmentIntegral (laplaceSlitFunction H ξ) θ 0 A at hs
  linear_combination hs

lemma borel_local_cut_exponential_outer (H α β : ℂ → ℂ) (S : ℂ) (r φ bP bN UP UN : ℝ)
    (hr : 0<r) (hφ : 0<φ) (hφπ : φ<Real.pi/2)
    (hgap : 1<(1+r)*Real.cos φ)
    (hφdist : ∀θ∈Icc (-φ) φ,‖Complex.exp ((θ:ℂ)*Complex.I)-1‖≤r/(2*(1+r)))
    (hH : AnalyticOnNhd ℂ H firstBorelSlit)
    (hα : AnalyticOnNhd ℂ α (closedBall 1 (2*r)))
    (hβ : AnalyticOnNhd ℂ β (closedBall 1 (2*r)))
    (hform : ∀z:ℂ,‖z-1‖ < 2*r → z.im≠0 →
      H z=S*(Complex.sqrt (1-z))⁻¹*α z+β z)
    (hbP : 0≤bP) (hbN : 0≤bN) (hUP : 0≤UP) (hUN : 0≤UN)
    (hiP : IntegrableOn (fun t:ℝ => Real.exp (-(bP*t))*
      ‖H ((t:ℂ)*Complex.exp ((φ:ℂ)*Complex.I))‖) (Ioi 0))
    (hiN : IntegrableOn (fun t:ℝ => Real.exp (-(bN*t))*
      ‖H ((t:ℂ)*Complex.exp (((-φ:ℝ):ℂ)*Complex.I))‖) (Ioi 0))
    (huP : (∫ t in Ioi 0,Real.exp (-(bP*t))*
      ‖H ((t:ℂ)*Complex.exp ((φ:ℂ)*Complex.I))‖)≤UP)
    (huN : (∫ t in Ioi 0,Real.exp (-(bN*t))*
      ‖H ((t:ℂ)*Complex.exp (((-φ:ℝ):ℂ)*Complex.I))‖)≤UN) :
    ∃C ε ξ₀:ℝ,0<C ∧ 0<ε ∧ 0<ξ₀ ∧ ∀ξ:ℝ,ξ₀≤ξ →
      ‖laplaceRayTail H (-φ) ξ 0-laplaceRayTail H φ ξ 0-
        ((-2*Complex.I)*S)*Complex.exp (-(ξ:ℂ))*
          (∫ v in (0:ℝ)..r,Complex.exp (-(ξ:ℂ)*(v:ℂ))*
            (Real.sqrt v:ℂ)⁻¹*α (1+(v:ℂ)))‖≤C*Real.exp (-((1+ε)*ξ)) := by
  let A : ℝ := 1+r
  let κ : ℝ := A*Real.cos φ-1
  have hA : 0<A := by dsimp [A];linarith
  have hκ : 0<κ := by dsimp [κ,A];linarith
  let ε : ℝ := κ/2
  let ξ₀ : ℝ := 1+2*bP*A/κ+2*bN*A/κ
  have hε : 0<ε := by dsimp [ε];positivity
  have hξ₀ : 0<ξ₀ := by dsimp [ξ₀];positivity
  obtain ⟨M,hM,hMB⟩ := sqrt_cut_arc_uniform_bound H α β S r φ hr (by linarith [Real.pi_pos]) hφdist hH hα hβ hform
  let C : ℝ := UN+UP+2*A*M*φ+1
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,ε,ξ₀,hC,hε,hξ₀,?_⟩
  intro ξ hξ
  have hξ0 : 0≤ξ := hξ₀.le.trans hξ
  have hcutP : 2*bP*A/κ≤ξ := by
    have hn : 0≤2*bN*A/κ := by positivity
    dsimp [ξ₀] at hξ
    linarith
  have hcutN : 2*bN*A/κ≤ξ := by
    have hp : 0≤2*bP*A/κ := by positivity
    dsimp [ξ₀] at hξ
    linarith
  have hqP : bP≤ξ*Real.cos φ := by
    have hp := (div_le_iff₀ hκ).mp hcutP
    dsimp [κ] at hp
    nlinarith
  have hqN : bN≤ξ*Real.cos (-φ) := by
    have hn := (div_le_iff₀ hκ).mp hcutN
    dsimp [κ] at hn
    rw [Real.cos_neg]
    nlinarith
  have hsinP : Real.sin φ≠0 := (Real.sin_pos_of_pos_of_lt_pi hφ (by linarith [Real.pi_pos])).ne'
  have hsinN : Real.sin (-φ)≠0 := by rw [Real.sin_neg];exact neg_ne_zero.mpr hsinP
  have hFullP := (laplaceRayTail_of_weighted_L1 H φ ξ 0 bP UP hH hsinP (by norm_num) hqP hiP huP).1
  have hFullN := (laplaceRayTail_of_weighted_L1 H (-φ) ξ 0 bN UN hH hsinN (by norm_num) hqN hiN huN).1
  have hdecP := laplaceRay_decomposition H φ ξ A hA.le hFullP
  have hdecN := laplaceRay_decomposition H (-φ) ξ A hA.le hFullN
  have hcut := finite_slit_local_cut_identity H α β S r ξ φ hr hξ0 hφ hφπ hφdist hH hα hβ hform
  have hTailP : ‖laplaceRayTail H φ ξ A‖≤UP*Real.exp (-((1+ε)*ξ)) := by
    simpa only [ε,κ] using laplaceRayTail_exponential_gap H φ ξ A bP UP hH hsinP hA hbP hUP hκ hξ0 hcutP hiP huP
  have hTailN : ‖laplaceRayTail H (-φ) ξ A‖≤UN*Real.exp (-((1+ε)*ξ)) := by
    simpa only [Real.cos_neg,ε,κ] using laplaceRayTail_exponential_gap H (-φ) ξ A bN UN hH hsinN hA hbN hUN
      (by simpa only [Real.cos_neg] using hκ) hξ0 (by simpa only [Real.cos_neg] using hcutN) hiN huN
  have hExp : Real.exp (-(ξ*(A*Real.cos φ)))≤Real.exp (-((1+ε)*ξ)) := by
    apply Real.exp_le_exp.mpr
    dsimp [ε,κ]
    nlinarith
  have hMB' : ∀θ∈Icc (-φ) φ,‖H ((A:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖≤M := by
    intro θ hθ
    simpa only [A,Complex.ofReal_add,Complex.ofReal_one] using hMB θ hθ
  have hArcP : ‖polarArcIntegral (laplaceSlitFunction H ξ) A 0 φ‖≤
      (A*M*φ)*Real.exp (-((1+ε)*ξ)) := by
    have hp := polarArc_laplace_exp_bound H A φ M ξ 0 φ hA (by linarith [Real.pi_pos]) hM.le hξ0
      ⟨by linarith,hφ.le⟩ ⟨by linarith,le_rfl⟩ hMB'
    have hp' : ‖polarArcIntegral (laplaceSlitFunction H ξ) A 0 φ‖≤
        (A*Real.exp (-(ξ*(A*Real.cos φ)))*M)*φ := by simpa only [sub_zero,abs_of_pos hφ] using hp
    apply hp'.trans
    nlinarith [mul_le_mul_of_nonneg_left hExp (show 0≤A*M*φ by positivity)]
  have hArcN : ‖polarArcIntegral (laplaceSlitFunction H ξ) A (-φ) 0‖≤
      (A*M*φ)*Real.exp (-((1+ε)*ξ)) := by
    have hp := polarArc_laplace_exp_bound H A φ M ξ (-φ) 0 hA (by linarith [Real.pi_pos]) hM.le hξ0
      ⟨le_rfl,by linarith⟩ ⟨by linarith,hφ.le⟩ hMB'
    have hp' : ‖polarArcIntegral (laplaceSlitFunction H ξ) A (-φ) 0‖≤
        (A*Real.exp (-(ξ*(A*Real.cos φ)))*M)*φ := by simpa only [sub_neg_eq_add,zero_add,abs_of_pos hφ] using hp
    apply hp'.trans
    nlinarith [mul_le_mul_of_nonneg_left hExp (show 0≤A*M*φ by positivity)]
  have he : laplaceRayTail H (-φ) ξ 0-laplaceRayTail H φ ξ 0-
      ((-2*Complex.I)*S)*Complex.exp (-(ξ:ℂ))*
        (∫ v in (0:ℝ)..r,Complex.exp (-(ξ:ℂ)*(v:ℂ))*
          (Real.sqrt v:ℂ)⁻¹*α (1+(v:ℂ)))=
      laplaceRayTail H (-φ) ξ A-laplaceRayTail H φ ξ A-
        polarArcIntegral (laplaceSlitFunction H ξ) A (-φ) 0-
        polarArcIntegral (laplaceSlitFunction H ξ) A 0 φ := by
    dsimp [A] at hdecP hdecN ⊢
    linear_combination hdecN-hdecP+hcut
  rw [he]
  have hn : ‖laplaceRayTail H (-φ) ξ A-laplaceRayTail H φ ξ A-
        polarArcIntegral (laplaceSlitFunction H ξ) A (-φ) 0-
        polarArcIntegral (laplaceSlitFunction H ξ) A 0 φ‖≤
      ‖laplaceRayTail H (-φ) ξ A‖+‖laplaceRayTail H φ ξ A‖+
        ‖polarArcIntegral (laplaceSlitFunction H ξ) A (-φ) 0‖+
        ‖polarArcIntegral (laplaceSlitFunction H ξ) A 0 φ‖ := by
    calc
      _ ≤ ‖laplaceRayTail H (-φ) ξ A-laplaceRayTail H φ ξ A-
          polarArcIntegral (laplaceSlitFunction H ξ) A (-φ) 0‖+
          ‖polarArcIntegral (laplaceSlitFunction H ξ) A 0 φ‖ := norm_sub_le _ _
      _ ≤ (‖laplaceRayTail H (-φ) ξ A-laplaceRayTail H φ ξ A‖+
          ‖polarArcIntegral (laplaceSlitFunction H ξ) A (-φ) 0‖)+
          ‖polarArcIntegral (laplaceSlitFunction H ξ) A 0 φ‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
  apply hn.trans
  have hb := add_le_add (add_le_add (add_le_add hTailN hTailP) hArcN) hArcP
  apply hb.trans
  dsimp [C]
  nlinarith [Real.exp_pos (-((1+ε)*ξ))]
end WP.Analysis
