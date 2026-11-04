import WPFormalization.RandomGeometry.PlanarCutTreeStar
import WPFormalization.RandomGeometry.CutBoundaryProduct
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsBoundary
import WPFormalization.Geometry.Bridge
import WPFormalization.External.BoundaryVolumeComparison
import WPFormalization.External.MirzakhaniIntegration

/-! Uniform physical volume bounds for actual rooted planar cuts. The root
retains its actual growing cusp count; the other components range over a fixed
finite list of stable genus-zero topological types. -/
noncomputable section
universe u v
namespace WP.RandomGeometry
open WP.External MeasureTheory Set

def generalPlanarZeroVolumeCap (P : PsiTheory) (B : ℕ) : ℝ :=
  1+∑m∈Finset.range (B+1),|volumeModel P 0 m|

lemma generalPlanarZeroVolumeCap_pos (P : PsiTheory) (B : ℕ) :
    0<generalPlanarZeroVolumeCap P B := by
  have hs : 0≤∑m∈Finset.range (B+1),|volumeModel P 0 m| :=
    Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  unfold generalPlanarZeroVolumeCap
  linarith

lemma generalPlanar_zero_volume_le_cap (P : PsiTheory) (B m : ℕ) (hm : m≤B) :
    volumeModel P 0 m≤generalPlanarZeroVolumeCap P B := by
  have hs := Finset.single_le_sum (s:=Finset.range (B+1))
    (f:=fun j=>|volumeModel P 0 j|) (fun j _=>abs_nonneg _) (Finset.mem_range.mpr (by omega : m<B+1))
  unfold generalPlanarZeroVolumeCap
  linarith [le_abs_self (volumeModel P 0 m)]

lemma multicurve_boundaryLengths_nonneg {n r : ℕ} (D : MulticurveCutData n r)
    (x : Fin r→ℝ) (hx : ∀i,0≤x i) (c : Fin D.components) :
    ∀j,0≤D.boundaryLengths x c j := by
  intro j
  unfold MulticurveCutData.boundaryLengths
  cases (Fintype.equivFin (D.Boundary c)).symm j with
  | inl j => exact le_rfl
  | inr j => exact hx j.val.1

lemma multicurve_boundary_exp_product {n r : ℕ} (D : MulticurveCutData n r)
    (x : Fin r→ℝ) :
    (∏c : Fin D.components,Real.exp ((∑j,D.boundaryLengths x c j)/2))=
      Real.exp (∑i,x i) := by
  have he : (∏c : Fin D.components,Real.exp ((∑j,D.boundaryLengths x c j)/2))=
      ∏c : Fin D.components,∏j,Real.exp (D.boundaryLengths x c j/2) := by
    apply Finset.prod_congr rfl
    intro c hc
    rw [←Real.exp_sum,Finset.sum_div]
  rw [he,D.boundaryLengths_prod_of_zero_eq_one (fun t=>Real.exp (t/2)) (by simp)]
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [pow_two,←Real.exp_add]
  congr 1
  ring

lemma generalPlanar_root_volume_upper (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g m : ℕ) (hg : 1≤g) (hm : 1 ≤ m) (L : Fin m→ℝ) (hL : ∀i,0≤L i) :
    wpVolume G g m L≤Real.exp ((∑i,L i)/2)*volumeModel P g m := by
  have hs : Stable g m := by unfold Stable;omega
  have hv := diagonal_volume_pos_nonempty P g m (by omega) hs
  rw [WP.Geometry.wpVolume_eq_boundaryVolumeModel P G g m L hs hL]
  exact (div_le_iff₀ hv).mp (pants_boundary_volume_bounds P g m hg hm L hL).2

lemma generalPlanar_cut_volume_upper (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    {n r : ℕ} (D : MulticurveCutData n r) (g B : ℕ) (hg : 1≤g)
    (hcomp : D.components=r+1) (root : Fin D.components)
    (hroot : D.genus root=g) (hzero : ∀c,c≠root→D.genus c=0)
    (hstable : ∀c,Stable (D.genus c) (D.boundaryCount c))
    (hm : 1≤D.boundaryCount root) (hbound : ∀c,c≠root→D.boundaryCount c≤B)
    (x : Fin r→ℝ) (hx : ∀i,0≤x i) :
    D.volumeProduct G x≤Real.exp (∑i,x i)*volumeModel P g (D.boundaryCount root)*
      (generalPlanarZeroVolumeCap P B)^r := by
  classical
  let V := volumeModel P g (D.boundaryCount root)
  let Q := generalPlanarZeroVolumeCap P B
  let W : Fin D.components→ℝ := fun c=>if c=root then V else Q
  have hV : 0≤V := (diagonal_volume_pos_nonempty P g (D.boundaryCount root)
    (by omega) (by unfold Stable;omega)).le
  have hQ : 0≤Q := (generalPlanarZeroVolumeCap_pos P B).le
  have hw : ∀c,0≤W c := by intro c;dsimp [W];split_ifs <;> assumption
  have hb : ∀c,wpVolume G (D.genus c) (D.boundaryCount c) (D.boundaryLengths x c)≤
      Real.exp ((∑j,D.boundaryLengths x c j)/2)*W c := by
    intro c
    by_cases hc : c=root
    · subst c
      simpa only [hroot,W,if_pos rfl,V] using
        generalPlanar_root_volume_upper P G g (D.boundaryCount root) hg hm _
          (multicurve_boundaryLengths_nonneg D x hx root)
    · have hgc := hzero c hc
      have hbc : 3≤D.boundaryCount c := by
        have hs := hstable c
        unfold Stable at hs
        omega
      have hu := wpVolume_genus_zero_boundary_upper P G (D.boundaryCount c) hbc
        (D.boundaryLengths x c) (multicurve_boundaryLengths_nonneg D x hx c)
      rw [WP.Geometry.cuspVolume_eq_volumeModel P G 0 (D.boundaryCount c)
        (by unfold Stable;omega)] at hu
      simp only [hgc,W,if_neg hc]
      exact hu.trans (mul_le_mul_of_nonneg_left
        (generalPlanar_zero_volume_le_cap P B _ (hbound c hc)) (Real.exp_pos _).le)
  have hprod : (∏c : Fin D.components,W c)=V*Q^r := by
    have he : (∏c : Fin D.components,W c)=W root*∏c∈Finset.univ.erase root,W c := by
      exact (Finset.mul_prod_erase _ _ (Finset.mem_univ root)).symm
    rw [he]
    have hcard : (Finset.univ.erase root).card=r := by
      have hh := Finset.card_erase_add_one (Finset.mem_univ root)
      simp only [Finset.card_univ,Fintype.card_fin,hcomp] at hh
      omega
    simp only [W,if_pos rfl]
    rw [Finset.prod_congr rfl (fun c hc=>if_neg (Finset.mem_erase.mp hc).1),
      Finset.prod_const,hcard]
  calc
    _≤∏c : Fin D.components,Real.exp ((∑j,D.boundaryLengths x c j)/2)*W c := by
      unfold MulticurveCutData.volumeProduct
      exact Finset.prod_le_prod₀ (fun c _=>ENNReal.toReal_nonneg) (fun c _=>hb c)
    _=(∏c : Fin D.components,Real.exp ((∑j,D.boundaryLengths x c j)/2))*
        ∏c : Fin D.components,W c := Finset.prod_mul_distrib
    _=_ := by rw [multicurve_boundary_exp_product D x,hprod];dsimp [V,Q];ring

end WP.RandomGeometry
