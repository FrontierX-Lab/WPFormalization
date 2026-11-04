import WPFormalization.Tight.SeparatingOrbitCatalogue
import WPFormalization.Tight.SeparatingGenusSum

/-! The actual separating tight orbit amplitude sum follows from the locally
proved fixed-skeleton genus-family injection, the exact skeleton partition,
and the previously proved uniform F.8 genus-allocation bound. -/

noncomputable section
universe u v w z
namespace WP.TightSeparating.Orbit
open WP.External WP.Critical Finset Set
open scoped BigOperators
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Qgeom : TightGeodesicGeometry G T H}
  (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
lemma fixed_amplitude_sum (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ g ≥ N, ∀ Q : ℕ,
      2 ≤ Q → Q ≤ k+1 → ∀ S : CutSkeleton k Q,
      ∀ s : Finset (Fixed A S (g:=g)), ∀ Y ∈ Ico (0 : ℝ) y₀,
      (∑ o ∈ s, ∏ c, markedF P ((A.cut o.val).genus c)
        ((A.cut o.val).boundaryCount c) (XR Y)) / markedF P g 0 (XR Y) ≤
        C*(r Y)^k/(g : ℝ)^(Q-1) := by
  obtain ⟨C,hC,N,hbound⟩ := separating_amplitude_genus_sum P k
  refine ⟨C,hC,N,?_⟩
  intro g hg Q hQ hkQ S s Y hY
  by_cases hempty : s = ∅
  · simp only [hempty,sum_empty,zero_div]
    exact div_nonneg (mul_nonneg hC.le (pow_nonneg (r_pos Y hY).le _)) (by positivity)
  obtain ⟨o,ho⟩ := nonempty_iff_ne_empty.mpr hempty
  have hp (c : Fin Q) : 1 ≤ S.degree c := by
    have hc := CutGraphData.boundaryCount_pos (A.cut o.val) hk (A.cut_connected o.val)
      ((realization A S o).vertices.symm c)
    rwa [boundary_eq A S o,(realization A S o).vertices.apply_symm_apply] at hc
  rw [sum_actual_eq_genusFamily A S s]
  exact hbound g hg Q hQ hkQ S.degree hp S.sum_degree
    (genusFamily A S s) (genusFamily_spec A S s) Y hY
end WP.TightSeparating.Orbit
namespace WP.TightSeparating
open WP.External WP.Critical Finset Set
open scoped BigOperators
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  {Qgeom : TightGeodesicGeometry G T H}
  (A : TightMulticurveTopology.{u,v,w,z} G T H Qgeom)
/-- The actual finite separating orbit sum satisfies F.8 after summing all
connected skeletons. The constant depends on k, not on g or the density Y. -/
lemma separating_orbit_amplitude_sum (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ g ≥ N, ∀ Y ∈ Ico (0 : ℝ) y₀,
      (∑ o ∈ (univ : Finset (A.Orbit g 0 k)).filter
        (fun o => 2 ≤ (A.cut o).components),
        ∏ c, markedF P ((A.cut o).genus c) ((A.cut o).boundaryCount c) (XR Y)) /
        markedF P g 0 (XR Y) ≤ C*(r Y)^k/(g : ℝ) := by
  classical
  obtain ⟨C,hC,N,hfixed⟩ := Orbit.fixed_amplitude_sum A k hk
  let M := Fintype.card (SkeletonCatalogue k)+1
  have hM : 0 < (M : ℝ) := by dsimp [M];positivity
  refine ⟨(M : ℝ)*C,mul_pos hM hC,max N 2,?_⟩
  intro g hg Y hY
  have hgR : 0 < (g : ℝ) := by exact_mod_cast (show 0<g by omega)
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (show 1≤g by omega)
  have hval : 0 ≤ C*(r Y)^k/(g : ℝ) := by
    exact div_nonneg (mul_nonneg hC.le (pow_nonneg (r_pos Y hY).le _)) hgR.le
  have hfiber (K : SkeletonCatalogue k) :
      (∑ o ∈ Orbit.fiberFixed A (g:=g) K, ∏ c,
        markedF P ((A.cut o.val).genus c) ((A.cut o.val).boundaryCount c) (XR Y)) /
        markedF P g 0 (XR Y) ≤ C*(r Y)^k/(g : ℝ) := by
    by_cases hQ : 2 ≤ K.1.val
    · have hkQ : K.1.val ≤ k+1 := by have := K.1.isLt;omega
      have hb := hfixed g (le_of_max_le_left hg) K.1.val hQ hkQ K.2
        (Orbit.fiberFixed A (g:=g) K) Y hY
      have hpow : (g : ℝ) ≤ (g : ℝ)^(K.1.val-1) :=
        le_self_pow₀ hg1 (by omega)
      exact hb.trans (div_le_div_of_nonneg_left
        (mul_nonneg hC.le (pow_nonneg (r_pos Y hY).le _)) hgR hpow)
    · have hempty : Orbit.fiberFixed A (g:=g) K = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro o ho
        obtain ⟨p,hp,rfl⟩ := mem_image.mp ho
        have he := congrArg (fun J : SkeletonCatalogue k => J.1.val) p.property
        have hc := p.val.property
        rw [Orbit.skeletonKey_vertices] at he
        omega
      simp only [hempty,sum_empty,zero_div]
      exact hval
  rw [sum_subtype (p:=fun o : A.Orbit g 0 k => 2 ≤ (A.cut o).components) ((univ : Finset (A.Orbit g 0 k)).filter
    (fun o => 2 ≤ (A.cut o).components)) (by simp)]
  rw [Orbit.sum_partition_by_skeleton A, sum_div]
  calc
    _ ≤ ∑ _K : SkeletonCatalogue k, C*(r Y)^k/(g : ℝ) :=
      sum_le_sum (fun K _ => hfiber K)
    _ = (Fintype.card (SkeletonCatalogue k) : ℝ)*(C*(r Y)^k/(g : ℝ)) := by simp
    _ ≤ (M : ℝ)*(C*(r Y)^k/(g : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hval
      exact_mod_cast (Nat.le_succ (Fintype.card (SkeletonCatalogue k)))
    _ = _ := by ring
end WP.TightSeparating
