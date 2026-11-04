import WPFormalization.Analysis.BorelOuter
import WPFormalization.Analysis.AnalyticWatson
import Mathlib

/-! The actual rescaled jump of two fixed off-cut Laplace integrals has an
order-uniform Gevrey remainder. This is proved from the raw square-root
Borel germ and fixed-ray L1 hypotheses, finite contour deformation, a single
Cauchy circle and Gamma moments. No uniform jump remainder is an input.
-/
noncomputable section
namespace WP.Analysis
open Complex MeasureTheory Set Filter Metric
open scoped Interval

lemma borel_rescaled_jump_gevrey (H α β : ℂ → ℂ) (S : ℂ) (r φ bP bN UP UN : ℝ)
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
    ∃C B ξ₀:ℝ,0<C ∧ 0<B ∧ 0<ξ₀ ∧ ∀L:ℕ,∀ξ:ℝ,ξ₀≤ξ →
      ‖((ξ^(1/2:ℝ):ℝ):ℂ)*Complex.exp (ξ:ℂ)*
          (laplaceRayTail H (-φ) ξ 0-laplaceRayTail H φ ξ 0)-
        ((-2*Complex.I)*S)*(∑j∈Finset.range L,
          (Real.Gamma ((1/2:ℝ)+(j:ℝ))/ξ^j) • WP.coeff (fun z:ℂ => α (1+z)) j)‖≤
        C*B^L*(L.factorial:ℝ)/ξ^L := by
  let g : ℂ → ℂ := fun z => α (1+z)
  let c : ℂ := (-2*Complex.I)*S
  have hg : DifferentiableOn ℂ g (closedBall 0 (2*r)) := by
    intro z hz
    have hm : 1+z∈closedBall 1 (2*r) := by simpa [Metric.mem_closedBall,dist_eq_norm] using hz
    exact ((hα _ hm).comp (analyticAt_const.add analyticAt_id)).differentiableAt.differentiableWithinAt
  obtain ⟨CL,BL,hCL,hBL,hLocal⟩ := analytic_finite_watson_bound g r (1/2) hr (by norm_num) (by norm_num) hg
  obtain ⟨CO,ε,ξ₀,hCO,hε,hξ₀,hOuter⟩ := borel_local_cut_exponential_outer H α β S r φ bP bN UP UN
    hr hφ hφπ hgap hφdist hH hα hβ hform hbP hbN hUP hUN hiP hiN huP huN
  let B : ℝ := max BL (2/ε)
  let C : ℝ := ‖c‖*CL+CO*(2/ε)+1
  have hB : 0<B := lt_of_lt_of_le hBL (le_max_left _ _)
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,B,max 1 ξ₀,hC,hB,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro L ξ hξ
  have hξone : 1≤ξ := (le_max_left _ _).trans hξ
  have hξpos : 0<ξ := lt_of_lt_of_le zero_lt_one hξone
  have hξO : ξ₀≤ξ := (le_max_right _ _).trans hξ
  let I : ℂ := ∫v in (0:ℝ)..r,Complex.exp (-(ξ:ℂ)*(v:ℂ))*
    (Real.sqrt v:ℂ)⁻¹*α (1+(v:ℂ))
  let P : ℂ := ∑j∈Finset.range L,(Real.Gamma ((1/2:ℝ)+(j:ℝ))/ξ^j) • WP.coeff g j
  let Δ : ℂ := laplaceRayTail H (-φ) ξ 0-laplaceRayTail H φ ξ 0
  let E : ℂ := Δ-c*Complex.exp (-(ξ:ℂ))*I
  have hEI : ‖E‖≤CO*Real.exp (-((1+ε)*ξ)) := hOuter ξ hξO
  have hI : I=(∫v in Ioc (0:ℝ) r,(Real.exp (-(ξ*v))*v^((1/2:ℝ)-1)) • g (v:ℂ)) :=
    sqrt_laplace_integral_real_smul α r ξ hr.le
  have hLI : ‖ξ^(1/2:ℝ) • I-P‖≤CL*BL^L*(L.factorial:ℝ)/ξ^L := by
    rw [hI]
    exact hLocal L ξ hξpos
  have he : ((ξ^(1/2:ℝ):ℝ):ℂ)*Complex.exp (ξ:ℂ)*Δ-c*P=
      c*(ξ^(1/2:ℝ) • I-P)+
        (((ξ^(1/2:ℝ):ℝ):ℂ)*Complex.exp (ξ:ℂ))*E := by
    have hexp : Complex.exp (ξ:ℂ)*Complex.exp (-(ξ:ℂ))=1 := by
      rw [←Complex.exp_add,add_neg_cancel,Complex.exp_zero]
    dsimp only [E]
    rw [Complex.real_smul]
    linear_combination (((ξ^(1/2:ℝ):ℝ):ℂ)*c*I)*hexp
  have hNE : ‖(((ξ^(1/2:ℝ):ℝ):ℂ)*Complex.exp (ξ:ℂ))*E‖≤
      (CO*(2/ε))*(2/ε)^L*(L.factorial:ℝ)/ξ^L := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hξpos _),Complex.norm_exp,Complex.ofReal_re]
    calc
      _ ≤ (ξ^(1/2:ℝ)*Real.exp ξ)*(CO*Real.exp (-((1+ε)*ξ))) :=
        mul_le_mul_of_nonneg_left hEI (by positivity)
      _ = CO*(ξ^(1/2:ℝ)*Real.exp (-(ε*ξ))) := by
        have hh : Real.exp ξ*Real.exp (-((1+ε)*ξ))=Real.exp (-(ε*ξ)) := by
          rw [←Real.exp_add]
          congr 1
          ring
        calc
          _ = CO*ξ^(1/2:ℝ)*(Real.exp ξ*Real.exp (-((1+ε)*ξ))) := by ring
          _ = _ := by rw [hh];ring
      _ ≤ CO*((2/ε)*(2/ε)^L*(L.factorial:ℝ)/ξ^L) :=
        mul_le_mul_of_nonneg_left (normalized_outer_exp_factorial_bound (1/2) ε ξ
          (by norm_num) hε hξone L) hCO.le
      _ = _ := by ring
  have hp1 : BL^L≤B^L := pow_le_pow_left₀ hBL.le (le_max_left _ _) L
  have hp2 : (2/ε)^L≤B^L := pow_le_pow_left₀ (by positivity) (le_max_right _ _) L
  have hScale : ‖c‖*(CL*BL^L*(L.factorial:ℝ)/ξ^L)+
      (CO*(2/ε))*(2/ε)^L*(L.factorial:ℝ)/ξ^L≤C*B^L*(L.factorial:ℝ)/ξ^L := by
    have h₁ := mul_le_mul_of_nonneg_left hp1 (show 0≤‖c‖*CL by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hp2 (show 0≤CO*(2/ε) by positivity)
    have h₃ := mul_le_mul_of_nonneg_right (add_le_add h₁ h₂)
      (show 0≤(L.factorial:ℝ)/ξ^L by positivity)
    have h₄ := mul_le_mul_of_nonneg_right (show ‖c‖*CL+CO*(2/ε)≤C by dsimp [C];linarith)
      (show 0≤B^L*((L.factorial:ℝ)/ξ^L) by positivity)
    calc
      _ = (‖c‖*CL*BL^L+CO*(2/ε)*(2/ε)^L)*((L.factorial:ℝ)/ξ^L) := by ring
      _ ≤ (‖c‖*CL*B^L+CO*(2/ε)*B^L)*((L.factorial:ℝ)/ξ^L) := h₃
      _ = (‖c‖*CL+CO*(2/ε))*(B^L*((L.factorial:ℝ)/ξ^L)) := by ring
      _ ≤ C*(B^L*((L.factorial:ℝ)/ξ^L)) := h₄
      _ = _ := by ring
  change ‖((ξ^(1/2:ℝ):ℝ):ℂ)*Complex.exp (ξ:ℂ)*Δ-c*P‖≤_
  rw [he]
  calc
    _ ≤ ‖c*(ξ^(1/2:ℝ) • I-P)‖+
        ‖(((ξ^(1/2:ℝ):ℝ):ℂ)*Complex.exp (ξ:ℂ))*E‖ := norm_add_le _ _
    _ ≤ ‖c‖*(CL*BL^L*(L.factorial:ℝ)/ξ^L)+
        (CO*(2/ε))*(2/ε)^L*(L.factorial:ℝ)/ξ^L := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hLI (norm_nonneg _)) hNE
    _ ≤ _ := hScale
end WP.Analysis
