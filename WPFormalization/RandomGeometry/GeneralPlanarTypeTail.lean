import WPFormalization.RandomGeometry.GeneralPlanarSingleCurveMoments
import WPFormalization.RandomGeometry.GeneralPlanarOneStarUpper
import WPFormalization.RandomGeometry.PrimitivePlanarScale

/-! Actual all-type planar tails. The sum includes every possible cusp side
size from K+2 through n; its moment bound is obtained from the actual one-curve
integration formula, not supplied as an additional assumption. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T) {g n : ℕ}

def generalPlanarTypeTailCount (X : G.Moduli g n (fun _ => 0)) (K : ℕ) (L : ℝ) : ℕ :=
  ∑j∈Finset.range (n-K-1),H.planarCount X (j+K+2) L

lemma generalPlanar_type_above_cusps_zero (X : G.Moduli g n (fun _ => 0))
    (k : ℕ) (hk : n<k) (L : ℝ) : H.planarCount X k L=0 := by
  rw [H.planarCount_eq_card]
  have hz : H.shortPlanar X k L=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro γ hγ
    obtain ⟨_,S,_,hS⟩ := (H.mem_shortPlanar X k L γ).mp hγ
    have hs := Finset.card_le_univ S
    simp only [Fintype.card_fin] at hs
    omega
  rw [hz,Finset.card_empty]

lemma generalPlanar_type_tail_measurable (K : ℕ) (L : ℝ) :
    Measurable (fun X : G.Moduli g n (fun _ => 0)=>generalPlanarTypeTailCount H X K L) := by
  classical
  exact Finset.measurable_sum _ (fun j _ => H.measurable_planarCount g n (j+K+2) L)

include C MI in
lemma generalPlanar_single_count_integrable (hg : 1≤g) (k : ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) :
    Integrable (fun X : G.Moduli g n (fun _ => 0)=>(H.planarCount X k L:ℝ))
      (wpProbability G g n) := by
  letI := wpProbability_isFinite G g n
  simpa only [generalPlanar_single_count_eq_planarCount H] using
    generalPlanarWindowCount_integrable H T C MI hg (fun _ : Fin 1=>k) L hL
      (fun _=>Icc 0 L) (fun _=>measurableSet_Icc) (fun _=>Subset.rfl) (wpProbability G g n)

include C MI in
lemma generalPlanar_type_tail_integrable (hg : 1≤g) (K : ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) :
    Integrable (fun X : G.Moduli g n (fun _ => 0)=>(generalPlanarTypeTailCount H X K L:ℝ))
      (wpProbability G g n) := by
  classical
  simp only [generalPlanarTypeTailCount,Nat.cast_sum]
  exact integrable_finsetSum _ (fun j _=>generalPlanar_single_count_integrable H T C MI hg _ L hL)

include C MI in
lemma generalPlanar_single_curve_mean_upper (hg : 2≤g) (hn : 2≤n)
    (k : ℕ) (hk : 2≤k) (hkn : k≤n) (L : ℝ) (hL0 : 0≤L)
    (hL : L<2*Real.arsinh 1) :
    (∫X : G.Moduli g n (fun _ => 0),(H.planarCount X k L:ℝ) ∂wpProbability G g n)≤
      Real.exp L*primitivePlanarFirstBase P g n k L := by
  rw [generalPlanar_single_curve_moment H T C MI hg k hk hkn L hL]
  exact general_planar_one_star_window_cut_upper P G g n k hg hn hk hkn L hL0

include C MI in
lemma generalPlanar_type_tail_mean_upper (hg : 2≤g) (hn : 2≤n)
    (K : ℕ) (L : ℝ) (hL0 : 0≤L) (hL : L<2*Real.arsinh 1) :
    (∫X : G.Moduli g n (fun _ => 0),(generalPlanarTypeTailCount H X K L:ℝ)
        ∂wpProbability G g n)≤
      Real.exp L*(∑j∈Finset.range (n-K-1),primitivePlanarFirstBase P g n (j+K+2) L) := by
  classical
  simp only [generalPlanarTypeTailCount,Nat.cast_sum]
  rw [integral_finsetSum _ (fun j _=>generalPlanar_single_count_integrable H T C MI (by omega) _ L hL),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact generalPlanar_single_curve_mean_upper H T C MI hg hn _ (by omega)
    (by have hh:=Finset.mem_range.mp hj;omega) L hL0 hL

include C MI in
lemma generalPlanar_type_tail_probability_le_mean (hg : 1≤g) (K : ℕ) (L : ℝ)
    (hL : L<2*Real.arsinh 1) :
    (wpProbability G g n).real {X | 0<generalPlanarTypeTailCount H X K L}≤
      ∫X : G.Moduli g n (fun _ => 0),(generalPlanarTypeTailCount H X K L:ℝ)
        ∂wpProbability G g n := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ:=wpProbability G g n)
    (f:=fun X=>(generalPlanarTypeTailCount H X K L:ℝ))
    (ae_of_all _ (fun _=>Nat.cast_nonneg _))
    (generalPlanar_type_tail_integrable H T C MI hg K L hL) 1
  have he : {X : G.Moduli g n (fun _ => 0) | (1:ℝ)≤(generalPlanarTypeTailCount H X K L:ℝ)}=
      {X | 0<generalPlanarTypeTailCount H X K L} := by
    ext X
    simp only [mem_setOf_eq,Nat.one_le_cast,Nat.one_le_iff_ne_zero,Nat.pos_iff_ne_zero]
  simpa only [he,one_mul] using h

end WP.RandomGeometry
