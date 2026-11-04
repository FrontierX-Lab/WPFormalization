import WPFormalization.HigherOrder.LogMarkedRegularity
import WPFormalization.Analysis.ComplexPrimitiveGluing
noncomputable section
open Set Filter
open scoped Topology
namespace WP.HigherOrder
lemma logarithmicMarkedCoefficient_common_complex_gevrey_two (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (Ω : Set ℂ) (C B : ℝ), IsOpen Ω ∧ Convex ℝ Ω ∧
      (∀ Y ∈ Icc (0:ℝ) y₀, (Y:ℂ) ∈ Ω) ∧ 0 < C ∧ 0 < B ∧
      ∃ F : ℕ → ℂ → ℂ, ∀ j : ℕ, AnalyticOnNhd ℂ (F j) Ω ∧
        (∀ Y ∈ Icc (0:ℝ) y₀, F j (Y:ℂ)=(logarithmicMarkedCoefficient P p j Y:ℂ)) ∧
        ∀ z ∈ Ω, ‖F j z‖ ≤ C*B^j*(j.factorial:ℝ)^2 := by
  classical
  have hy₀ := y₀_pos
  obtain ⟨V,Cq,Bq,hV,hVconv,hVcover,hCq,hBq,hquot⟩ := ComplexCanonical.common_transport_quotient_gevrey_two P p hp
  obtain ⟨Ce,Be,hCe,hBe,hcont,hderiv,hcoef,hlip⟩ := logarithmicMarkedCoefficient_real_gevrey_regularity P p hp
  let J := {j : ℕ // 1 ≤ j}
  have hF (j : J) : ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F V ∧
      (∀ Y ∈ Ico (0:ℝ) y₀,F (Y:ℂ)=((transportCoefficient P p j Y/(A Y*r Y):ℝ):ℂ)) ∧
      ∀ z ∈ V, ‖F z‖ ≤ Cq*Bq^(j:ℕ)*((j:ℕ).factorial:ℝ)^2 := hquot j j.property
  choose Q hQa hQr hQb using hF
  have hdf (j : J) (Y : ℝ) (hY : Y ∈ Ioo (0:ℝ) y₀) :
      HasDerivAt (fun t : ℝ => (logarithmicMarkedCoefficient P p j t:ℂ)) (Q j (Y:ℂ)) Y := by
    rw [hQr j Y ⟨hY.1.le,hY.2⟩]
    exact (hderiv j j.property Y hY).ofReal_comp
  obtain ⟨U,hU,hUcover,G,hG⟩ := Analysis.real_primitive_family_common_complex_extension 0 y₀ y₀_pos
    (fun j : J => logarithmicMarkedCoefficient P p j) (fun j => hcont j) V hV hVcover Q hQa hdf
  have hopen : IsOpen (U ∩ V ∩ Metric.ball (0:ℂ) (y₀+1)) := (hU.inter hV).inter Metric.isOpen_ball
  have hcover : ∀ Y ∈ Icc (0:ℝ) y₀, (Y:ℂ) ∈ U ∩ V ∩ Metric.ball (0:ℂ) (y₀+1) := by
    intro Y hY
    refine ⟨⟨hUcover Y hY,hVcover Y hY⟩,?_⟩
    rw [Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hY.1]
    linarith [hY.2]
  obtain ⟨Ω,hΩ,hΩconv,hΩcover,hΩsub⟩ := Analysis.exists_convex_physical_neighborhood _ hopen hcover
  have hΩU : Ω ⊆ U := fun z hz => (hΩsub hz).1.1
  have hΩV : Ω ⊆ V := fun z hz => (hΩsub hz).1.2
  have hGa (j : J) : AnalyticOnNhd ℂ (G j) Ω := (hG j).1.mono hΩU
  have hQderiv (j : J) : EqOn (deriv (G j)) (Q j) Ω := by
    have hc : y₀/2 ∈ Ioo (0:ℝ) y₀ := ⟨by linarith [y₀_pos],by linarith [y₀_pos]⟩
    apply Analysis.complex_identity_of_real_germ (deriv (G j)) (Q j) Ω (y₀/2)
      (fun z hz => (hGa j z hz).deriv) ((hQa j).mono hΩV) hΩconv.isPreconnected
      (hΩcover _ ⟨hc.1.le,hc.2.le⟩)
    filter_upwards [isOpen_Ioo.mem_nhds hc] with Y hY
    rw [hQr j Y ⟨hY.1.le,hY.2⟩]
    apply Analysis.complex_deriv_eq_of_real_interval_germ 0 y₀ Y _ (G j)
      (logarithmicMarkedCoefficient P p j) y₀_pos ⟨hY.1.le,hY.2.le⟩
      (hGa j _ (hΩcover Y ⟨hY.1.le,hY.2.le⟩)).differentiableAt (hderiv j j.property Y hY)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hG j).2 t ht
  let B : ℝ := max Bq Be
  let C : ℝ := Ce+Cq*(2*y₀+1)
  have hB : 0 < B := hBq.trans_le (le_max_left _ _)
  have hC : 0 < C := by dsimp [C]; positivity
  have hGb (j : J) (z : ℂ) (hz : z ∈ Ω) : ‖G j z‖ ≤ C*B^(j:ℕ)*((j:ℕ).factorial:ℝ)^2 := by
    have hd : ‖G j z-G j (y₀:ℂ)‖ ≤ (Cq*Bq^(j:ℕ)*((j:ℕ).factorial:ℝ)^2)*‖z-(y₀:ℂ)‖ := by
      apply Convex.norm_image_sub_le_of_norm_deriv_le (𝕜:=ℂ)
        (fun w hw => (hGa j w hw).differentiableAt) _ hΩconv (hΩcover _ ⟨y₀_pos.le,le_rfl⟩) hz
      intro w hw
      rw [hQderiv j hw]
      exact hQb j w (hΩV hw)
    have hdist : ‖z-(y₀:ℂ)‖ ≤ 2*y₀+1 := by
      have hzNorm : ‖z‖ < y₀+1 := by simpa only [Metric.mem_ball,dist_zero_right] using (hΩsub hz).2
      have hyNorm : ‖(y₀:ℂ)‖=y₀ := by simp [Complex.norm_real,abs_of_pos y₀_pos]
      calc _ ≤ ‖z‖+‖(y₀:ℂ)‖ := norm_sub_le _ _
           _ ≤ 2*y₀+1 := by rw [hyNorm];linarith
    have hend : ‖G j (y₀:ℂ)‖ ≤ Ce*Be^(j:ℕ)*((j:ℕ).factorial:ℝ)^2 := by
      rw [(hG j).2 _ ⟨y₀_pos.le,le_rfl⟩,Complex.norm_real,Real.norm_eq_abs]
      exact hcoef j y₀ ⟨y₀_pos.le,le_rfl⟩
    have hqbase : Bq^(j:ℕ) ≤ B^(j:ℕ) := pow_le_pow_left₀ hBq.le (le_max_left _ _) _
    have hebase : Be^(j:ℕ) ≤ B^(j:ℕ) := pow_le_pow_left₀ hBe.le (le_max_right _ _) _
    calc ‖G j z‖ ≤ ‖G j z-G j (y₀:ℂ)‖+‖G j (y₀:ℂ)‖ := by simpa only [add_comm] using (norm_le_insert' (G j z) (G j (y₀:ℂ)))
         _ ≤ (Cq*Bq^(j:ℕ)*((j:ℕ).factorial:ℝ)^2)*(2*y₀+1)+Ce*Be^(j:ℕ)*((j:ℕ).factorial:ℝ)^2 :=
           add_le_add (hd.trans (mul_le_mul_of_nonneg_left hdist (by positivity))) hend
         _ ≤ (Cq*B^(j:ℕ)*((j:ℕ).factorial:ℝ)^2)*(2*y₀+1)+Ce*B^(j:ℕ)*((j:ℕ).factorial:ℝ)^2 := by
           gcongr <;> positivity
         _ = _ := by dsimp [C];ring
  let F : ℕ → ℂ → ℂ := fun j => if hj : 1 ≤ j then G ⟨j,hj⟩ else fun _ => 0
  refine ⟨Ω,C,B,hΩ,hΩconv,hΩcover,hC,hB,F,?_⟩
  intro j
  by_cases hj : 1 ≤ j
  · simpa only [F,dite_eq_left hj] using ⟨hGa ⟨j,hj⟩,(hG ⟨j,hj⟩).2,hGb ⟨j,hj⟩⟩
  · have hj0 : j=0 := by omega
    subst j
    simp only [F,dite_eq_right (by omega : ¬ 1 ≤ (0:ℕ)),logarithmicMarkedCoefficient,ite_true]
    exact ⟨analyticOnNhd_const,fun Y hY => by simp,fun z hz => by simp;positivity⟩
end WP.HigherOrder
