import WPFormalization.RandomGeometry.PrimitiveSeparatingVolumes
import WPFormalization.RandomGeometry.PrimitiveSeparatingLabels
import WPFormalization.RandomGeometry.PrimitiveSeparatingVolumeSum

/-! The actual orbit sum injects into all ordered genus/cusp allocations.
Every empty cusp fiber and every positive-genus split is kept. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Critical Finset
open scoped BigOperators

def primitiveSeparatingAllocationWeight (P : PsiTheory) (g n : ℕ)
    (a : Fin (g-1)×(Fin n→Fin 2)) : ℝ :=
  let i:=a.1.val+1
  let k:=cutCuspHistogram a.2 0
  volumeModel P i (k+1)*volumeModel P (g-i) (n-k+1)

lemma primitiveSeparatingAllocationWeight_nonneg (P : PsiTheory) (g n : ℕ)
    (a : Fin (g-1)×(Fin n→Fin 2)) : 0≤primitiveSeparatingAllocationWeight P g n a := by
  have ha:=a.1.isLt
  have h1 := (diagonal_volume_pos_nonempty P (a.1.val+1) (cutCuspHistogram a.2 0+1)
    (by omega) (by unfold Stable;omega)).le
  have h2 := (diagonal_volume_pos_nonempty P (g-(a.1.val+1)) (n-cutCuspHistogram a.2 0+1)
    (by omega) (by unfold Stable;omega)).le
  exact mul_nonneg h1 h2

lemma primitiveSeparatingAllocationWeight_sum (P : PsiTheory) (g n : ℕ) :
    (∑a : Fin (g-1)×(Fin n→Fin 2),primitiveSeparatingAllocationWeight P g n a)=
      ∑i∈range (g-1),∑k∈range (n+1),
        (n.choose k:ℝ)*volumeModel P (i+1) (k+1)*volumeModel P (g-(i+1)) (n-k+1) := by
  rw [Fintype.sum_prod_type]
  have he (i : Fin (g-1)) :
      (∑σ : Fin n→Fin 2,primitiveSeparatingAllocationWeight P g n (i,σ))=
        ∑k∈range (n+1),(n.choose k:ℝ)*volumeModel P (i.val+1) (k+1)*volumeModel P (g-(i.val+1)) (n-k+1) := by
    have hl := separating_cusp_assignment_sum n (fun k=>
      volumeModel P (i.val+1) (k+1)*volumeModel P (g-(i.val+1)) (n-k+1))
    simpa only [primitiveSeparatingAllocationWeight,nsmul_eq_mul,mul_assoc] using hl
  simp_rw [he]
  exact Fin.sum_univ_eq_sum_range (fun i=>∑k∈range (n+1),
    (n.choose k:ℝ)*volumeModel P (i+1) (k+1)*volumeModel P (g-(i+1)) (n-k+1)) (g-1)

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    {g n : ℕ}

lemma primitiveSeparatingAllocationWeight_of_orbit (o : PrimitiveSeparatingOrbit T g n) :
    primitiveSeparatingAllocationWeight P g n (primitiveSeparatingOrbitAllocation T o)=
      volumeModel P (primitiveSeparatingOrbitGenus T o) (primitiveSeparatingOrbitCuspCount T o+1)*
        volumeModel P (g-primitiveSeparatingOrbitGenus T o) (n-primitiveSeparatingOrbitCuspCount T o+1) := by
  unfold primitiveSeparatingAllocationWeight
  rw [primitiveSeparatingOrbitAllocation_genus]
  rfl

lemma primitiveSeparatingOrbit_weight_sum_le :
    (∑o : PrimitiveSeparatingOrbit T g n,
      volumeModel P (primitiveSeparatingOrbitGenus T o) (primitiveSeparatingOrbitCuspCount T o+1)*
        volumeModel P (g-primitiveSeparatingOrbitGenus T o) (n-primitiveSeparatingOrbitCuspCount T o+1))≤
      ∑i∈range (g-1),∑k∈range (n+1),
        (n.choose k:ℝ)*volumeModel P (i+1) (k+1)*volumeModel P (g-(i+1)) (n-k+1) := by
  simp_rw [←primitiveSeparatingAllocationWeight_of_orbit T]
  rw [←primitiveSeparatingAllocationWeight_sum]
  rw [←sum_image (primitiveSeparatingOrbitAllocation_finite_injective T).injOn]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _=>primitiveSeparatingAllocationWeight_nonneg P g n a)

lemma primitiveSeparatingOrbit_weight_ratio_sum_le (hV : 0<volumeModel P g n) :
    (∑o : PrimitiveSeparatingOrbit T g n,
      volumeModel P (primitiveSeparatingOrbitGenus T o) (primitiveSeparatingOrbitCuspCount T o+1)*
        volumeModel P (g-primitiveSeparatingOrbitGenus T o) (n-primitiveSeparatingOrbitCuspCount T o+1))/volumeModel P g n≤
      primitiveSeparatingVolumeSum P g n := by
  have he := div_le_div_of_nonneg_right (primitiveSeparatingOrbit_weight_sum_le T (g:=g) (n:=n)) hV.le
  simpa only [primitiveSeparatingVolumeSum,Finset.sum_div] using he

end WP.RandomGeometry
