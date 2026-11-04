import WPFormalization.Tight.SeparatingPrefactor
import WPFormalization.Tight.SeparatingGamma
import WPFormalization.Tight.SeparatingUnmarked

noncomputable section
namespace WP.TightSeparating
open Set Filter
open scoped Topology

/-- Exactly the right-hand scale of original (F.7), without a hidden prefactor. -/
def componentScale (g p : ℕ) (Y : ℝ) : ℝ :=
  (4 : ℝ)⁻¹^g * (Z Y)⁻¹^(complexity g p) *
    Real.rpow (r Y) ((p : ℝ)/2) * gammaWeight (complexity g p)

lemma componentScale_pos (g p : ℕ) (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Ico (0 : ℝ) y₀) :
    0 < componentScale g p Y := by
  have hh : 1 ≤ complexity g p := by unfold complexity Stable at *;omega
  dsimp [componentScale]
  exact mul_pos (mul_pos (mul_pos (by positivity)
    (pow_pos (inv_pos.mpr (Analysis.marked_Z_pos Y hY)) _))
    (Real.rpow_pos_of_pos (r_pos Y hY) _)) (gammaWeight_pos _ hh)

lemma markedModel_eq_componentScale (g p : ℕ) (hs : Stable g p) (Y : ℝ) :
    markedModel g p Y = componentScale g p Y *
      (Real.sqrt (A Y*Theta Y)/Real.sqrt Real.pi) := by
  have hh : 0 < (complexity g p : ℝ) := by
    exact_mod_cast (show 0 < complexity g p by unfold complexity Stable at *;omega)
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hh' : Real.sqrt (complexity g p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  unfold markedModel componentScale gammaWeight
  rw [Real.sqrt_mul Real.pi_pos.le]
  field_simp
  <;> ring

lemma kernel_scale_factor_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ Y ∈ Icc (0 : ℝ) y₀,
      c ≤ Real.sqrt (A Y*Theta Y)/Real.sqrt Real.pi ∧
      Real.sqrt (A Y*Theta Y)/Real.sqrt Real.pi ≤ C := by
  have hA : Continuous (fun Y : Icc (0 : ℝ) y₀ => A (Y : ℝ)) :=
    continuousOn_iff_continuous_restrict.mp Analysis.A_continuousOn_closed_parameter
  have hcont : Continuous (fun Y : Icc (0 : ℝ) y₀ =>
      Real.sqrt (A Y*Theta Y)/Real.sqrt Real.pi) :=
    ((hA.mul Theta_continuous_closed).sqrt).div_const _
  have hpos : ∀ Y : Icc (0 : ℝ) y₀,
      0 < Real.sqrt (A Y*Theta Y)/Real.sqrt Real.pi := by
    intro Y
    exact div_pos (Real.sqrt_pos.mpr (mul_pos
      (Analysis.marked_A_pos Y Y.property) (Analysis.marked_Theta_pos Y Y.property)))
      (Real.sqrt_pos.mpr Real.pi_pos)
  obtain ⟨c,C,hc,hC,hbound⟩ := positive_continuous_parameter_bounds _ hcont hpos
  exact ⟨c,C,hc,hC,fun Y hY => hbound ⟨Y,hY⟩⟩

/-- Original F.7 uniformly over every stable genus, including bounded genera. -/
lemma marked_scale_sandwich_all_stable (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ g : ℕ, Stable g p → ∀ Y ∈ Ico (0 : ℝ) y₀,
      c * componentScale g p Y ≤ markedF P g p (XR Y) ∧
      markedF P g p (XR Y) ≤ C * componentScale g p Y := by
  obtain ⟨a,b,ha,hb,hmodel⟩ := marked_model_sandwich_all_stable P p hp
  obtain ⟨c,C,hc,hC,hkernel⟩ := kernel_scale_factor_bounds
  refine ⟨a*c,b*C,mul_pos ha hc,mul_pos hb hC,?_⟩
  intro g hs Y hY
  have he := markedModel_eq_componentScale g p hs Y
  have hm := componentScale_pos g p hs Y hY
  have hh := hmodel g hs Y hY
  have hk := hkernel Y ⟨hY.1,hY.2.le⟩
  rw [he] at hh
  constructor
  · have hl := mul_le_mul_of_nonneg_left hk.1 (mul_pos ha hm).le
    nlinarith only [hl,hh.1]
  · have hu := mul_le_mul_of_nonneg_left hk.2 (mul_pos hb hm).le
    nlinarith only [hu,hh.2]

/-- The unmarked parent needs only sufficiently large genus in F.3.
This is produced by the actual p=0 comparison, not by an unmarked estimate field. -/
lemma unmarked_scale_sandwich_eventually (P : PsiTheory) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ Y ∈ Ico (0 : ℝ) y₀,
      c * componentScale g 0 Y ≤ markedF P g 0 (XR Y) ∧
      markedF P g 0 (XR Y) ≤ C * componentScale g 0 Y := by
  obtain ⟨G,hmodel⟩ := unmarked_model_sandwich_eventually P
  obtain ⟨c,C,hc,hC,hkernel⟩ := kernel_scale_factor_bounds
  refine ⟨c/(2*Real.pi),(2/Real.pi)*C,by positivity,by positivity,G+2,?_⟩
  intro g hg Y hY
  have hs : Stable g 0 := by unfold Stable;omega
  have hh := hmodel g (by omega) Y hY
  rw [markedModel_eq_componentScale g 0 hs Y] at hh
  have hm := componentScale_pos g 0 hs Y hY
  have hk := hkernel Y ⟨hY.1,hY.2.le⟩
  constructor
  · have hl := mul_le_mul_of_nonneg_left hk.1
      (show 0 ≤ (1/(2*Real.pi))*componentScale g 0 Y by positivity)
    calc
      _ = ((1/(2*Real.pi))*componentScale g 0 Y)*c := by ring
      _ ≤ ((1/(2*Real.pi))*componentScale g 0 Y)*
          (Real.sqrt (A Y*Theta Y)/Real.sqrt Real.pi) := hl
      _ = (1/(2*Real.pi))*(componentScale g 0 Y*
          (Real.sqrt (A Y*Theta Y)/Real.sqrt Real.pi)) := by ring
      _ ≤ _ := hh.1
  · have hu := mul_le_mul_of_nonneg_left hk.2
      (show 0 ≤ (2/Real.pi)*componentScale g 0 Y by positivity)
    nlinarith only [hu,hh.2]

end WP.TightSeparating

namespace WP.TightSeparating
open Set Filter
open scoped Topology

/-- The exact scale cancellation before any graph/genera summation. -/
lemma componentScale_product (Q k g : ℕ) (hQ : 1 ≤ Q) (hkQ : Q ≤ k+1)
    (gs ps : Fin Q → ℕ) (hs : ∀ i, Stable (gs i) (ps i))
    (hp : ∑ i, ps i = 2*k)
    (hh : ∑ i, complexity (gs i) (ps i) = complexity g 0)
    (hg : (∑ i, gs i)+k = g+(Q-1))
    (Y : ℝ) (hY : Y ∈ Ico (0 : ℝ) y₀) :
    (∏ i, componentScale (gs i) (ps i) Y) =
      ((4 : ℝ)^(k+1-Q) * (r Y)^k *
        ((∏ i, gammaWeight (complexity (gs i) (ps i))) /
          gammaWeight (complexity g 0))) * componentScale g 0 Y := by
  have hgs : (∑ i, gs i)+(k+1-Q)=g := by omega
  have hr := r_pos Y hY
  have hZ := Analysis.marked_Z_pos Y hY
  have hparent : Stable g 0 := by
    have hpos : 0 < ∑ i, complexity (gs i) (ps i) := by
      apply Finset.sum_pos
      · intro i hi
        unfold complexity
        have hi := hs i
        unfold Stable at hi
        omega
      · exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    rw [hh] at hpos
    unfold complexity Stable at *
    omega
  have hγ : gammaWeight (complexity g 0) ≠ 0 :=
    (gammaWeight_pos _ (by unfold complexity Stable at *;omega)).ne'
  have hpR : (∑ i : Fin Q, (ps i : ℝ)/2) = (k : ℝ) := by
    rw [←Finset.sum_div]
    have hh' : (∑ i : Fin Q, (ps i : ℝ)) = 2*(k : ℝ) := by exact_mod_cast hp
    rw [hh']
    ring
  have hroot : (∏ i : Fin Q, Real.rpow (r Y) ((ps i : ℝ)/2)) = (r Y)^k := by
    simp only [Real.rpow_eq_pow]
    rw [←Real.rpow_sum_of_pos hr,hpR,Real.rpow_natCast]
  have hfour : (4 : ℝ)^(k+1-Q) * (4 : ℝ)⁻¹^g = (4 : ℝ)⁻¹^(∑ i, gs i) := by
    rw [←hgs,pow_add]
    have hcancel : (4 : ℝ)^(k+1-Q) * (4 : ℝ)⁻¹^(k+1-Q) = 1 := by
      rw [←mul_pow]
      norm_num
    calc
      _ = (4 : ℝ)⁻¹^(∑ i, gs i) *
          ((4 : ℝ)^(k+1-Q) * (4 : ℝ)⁻¹^(k+1-Q)) := by ring
      _ = _ := by rw [hcancel,mul_one]
  simp only [componentScale,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [hh,hroot]
  simp only [Nat.cast_zero,zero_div,Real.rpow_eq_pow,Real.rpow_zero,mul_one]
  rw [show ((4 : ℝ)^(k+1-Q) * r Y^k *
        ((∏ i, gammaWeight (complexity (gs i) (ps i))) /
          gammaWeight (complexity g 0))) *
        ((4 : ℝ)⁻¹^g * (Z Y)⁻¹^(complexity g 0) * gammaWeight (complexity g 0)) =
      ((4 : ℝ)^(k+1-Q)*(4 : ℝ)⁻¹^g) * (Z Y)⁻¹^(complexity g 0) * r Y^k *
        (∏ i, gammaWeight (complexity (gs i) (ps i))) by field_simp]
  rw [hfour]

end WP.TightSeparating
