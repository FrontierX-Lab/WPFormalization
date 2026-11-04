import WPFormalization.RandomGeometry.GeneralPlanarCutVolumeBound
import WPFormalization.RandomGeometry.PantsBoxLintegral
import WPFormalization.RandomGeometry.PantsWindowCount

/-! The actual Mirzakhani orthant integral on bounded physical windows is
controlled by its true Jacobian integral (L²/2)^r. -/
noncomputable section
universe u v
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped ENNReal

lemma pantsBox_lintegral_weight (r : ℕ) (L : ℝ) (hL : 0≤L) :
    (∫⁻x : Fin r→ℝ,∏i,ENNReal.ofReal (x i) ∂pantsBoxMeasure r L)=
      ENNReal.ofReal ((L^2/2)^r) := by
  have hi := pantsBoxMeasure_integrable_continuous r L
    (fun x : Fin r→ℝ=>∏i,x i) (by fun_prop)
  have hn : 0≤ᵐ[pantsBoxMeasure r L] (fun x : Fin r→ℝ=>∏i,x i) := by
    filter_upwards [pantsBoxMeasure_ae_mem r L] with x hx
    exact Finset.prod_nonneg (fun i _=>(hx i).1)
  rw [←pantsBoxMeasure_integral_weight r L hL,
    ofReal_integral_eq_lintegral_ofReal hi hn]
  apply lintegral_congr_ae
  filter_upwards [pantsBoxMeasure_ae_mem r L] with x hx
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _=>(hx i).1)).symm

lemma physical_window_lintegral_le_const {r : ℕ} (V : (Fin r→ℝ)→ℝ)
    (I : Fin r→Set ℝ) (L B : ℝ) (hL : 0≤L) (hB : 0≤B)
    (hsub : ∀i,I i⊆Icc 0 L)
    (hV : ∀x,(∀i,0≤x i ∧ x i≤L)→V x≤B) :
    (∫⁻x : Fin r→ℝ in {x | ∀i,0≤x i},
      pantsWindowTest I x*ENNReal.ofReal (V x)*∏i,ENNReal.ofReal (x i))≤
      ENNReal.ofReal (B*(L^2/2)^r) := by
  classical
  have hh : (∫⁻x : Fin r→ℝ in {x | ∀i,0≤x i},
      pantsWindowTest I x*ENNReal.ofReal (V x)*∏i,ENNReal.ofReal (x i))≤
      ∫⁻x : Fin r→ℝ in {x | ∀i,0≤x i},
        (if ∀i,x i≤L then (1:ℝ≥0∞) else 0)*
          (ENNReal.ofReal B*∏i,ENNReal.ofReal (x i)) := by
    apply lintegral_mono
    intro x
    by_cases hx : ∀i,x i∈I i
    · have hbox : ∀i,0≤x i ∧ x i≤L := fun i=>hsub i (hx i)
      have htop : ∀i,x i≤L := fun i=>(hbox i).2
      simp only [pantsWindowTest,if_pos hx,if_pos htop,one_mul]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hV x hbox)) le_rfl
    · simp only [pantsWindowTest,if_neg hx,zero_mul]
      exact bot_le
  calc
    _≤_ := hh
    _=ENNReal.ofReal B*(∫⁻x : Fin r→ℝ,∏i,ENNReal.ofReal (x i) ∂pantsBoxMeasure r L) := by
      rw [pants_lintegral_orthant_upper r L,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _=_ := by rw [pantsBox_lintegral_weight r L hL,ENNReal.ofReal_mul hB]

lemma generalPlanar_cut_window_integral_upper (P : PsiTheory)
    (G : WeilPeterssonGeometry.{u,v} P) {n r : ℕ} (D : MulticurveCutData n r)
    (g B : ℕ) (hg : 1≤g) (hcomp : D.components=r+1) (root : Fin D.components)
    (hroot : D.genus root=g) (hzero : ∀c,c≠root→D.genus c=0)
    (hstable : ∀c,Stable (D.genus c) (D.boundaryCount c))
    (hm : 1≤D.boundaryCount root) (hbound : ∀c,c≠root→D.boundaryCount c≤B)
    (I : Fin r→Set ℝ) (L : ℝ) (hL : 0≤L) (hsub : ∀i,I i⊆Icc 0 L) :
    (∫⁻x : Fin r→ℝ in {x | ∀i,0≤x i},
      pantsWindowTest I x*ENNReal.ofReal (D.volumeProduct G x)*∏i,ENNReal.ofReal (x i))≤
      ENNReal.ofReal (Real.exp ((r:ℝ)*L)*volumeModel P g (D.boundaryCount root)*
        (generalPlanarZeroVolumeCap P B)^r*(L^2/2)^r) := by
  have hnonneg : 0≤Real.exp ((r:ℝ)*L)*volumeModel P g (D.boundaryCount root)*
      (generalPlanarZeroVolumeCap P B)^r := by
    have hv := diagonal_volume_pos_nonempty P g (D.boundaryCount root)
      (by omega) (by unfold Stable;omega)
    have hQ := generalPlanarZeroVolumeCap_pos P B
    positivity
  apply physical_window_lintegral_le_const _ I L _ hL hnonneg hsub
  intro x hx
  have hsum : (∑i,x i)≤(r:ℝ)*L := by
    calc
      _≤∑_i : Fin r,L := Finset.sum_le_sum (fun i _=>(hx i).2)
      _=_ := by simp
  have he := Real.exp_le_exp.mpr hsum
  have hv := (diagonal_volume_pos_nonempty P g (D.boundaryCount root)
    (by omega) (by unfold Stable;omega)).le
  have hQ := (generalPlanarZeroVolumeCap_pos P B).le
  exact (generalPlanar_cut_volume_upper P G D g B hg hcomp root hroot hzero hstable hm hbound
    x (fun i=>(hx i).1)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hv) (pow_nonneg hQ r))

end WP.RandomGeometry
