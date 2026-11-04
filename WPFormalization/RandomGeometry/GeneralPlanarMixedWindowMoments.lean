import WPFormalization.RandomGeometry.GeneralPlanarFixedWindowMoments
import WPFormalization.RandomGeometry.GeneralPlanarWindowCutoff
import WPFormalization.RandomGeometry.GeneralPlanarMixedFactorialCount

/-! Mixed factorial moments of the actual fixed family of planar type/window
counts. The family cutoff is independent of the multi-index of the moment. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped Topology ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

def generalPlanarFamilyWindowCap {ι : Type*} [Fintype ι] (g n : ℕ) (hi : ι→ℝ) : ℝ :=
  (1+∑j,hi j)/Real.sqrt (primitivePlanarEffectiveScale g n)

def generalPlanarFamilyWindows {ι : Type*} (g n : ℕ) (lo hi : ι→ℝ) : ι→Set ℝ :=
  fun j=>Ioc (lo j/Real.sqrt (primitivePlanarEffectiveScale g n))
    (hi j/Real.sqrt (primitivePlanarEffectiveScale g n))

def generalPlanarFamilyMovingWeight {ι : Type*} [Fintype ι] (P : PsiTheory)
    (k : ι→ℕ) (lo hi : ι→ℝ) (a : ι→ℕ) (x : ℝ) : ℝ :=
  ∏j,(2*volumeModel P 0 (k j+1)/((k j).factorial:ℝ)*
    (x/(2*Real.pi^2))^(k j-2)*((hi j)^2-(lo j)^2))^(a j)

lemma generalPlanar_family_window_subset_cap {ι : Type*} [Fintype ι]
    (g n : ℕ) (lo hi : ι→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j) :
    ∀j,generalPlanarFamilyWindows g n lo hi j⊆Icc 0 (generalPlanarFamilyWindowCap g n hi) := by
  intro j x hx
  have hhi : ∀l,0≤hi l := fun l=>(hlo l).trans (hab l)
  have hs : hi j≤∑l,hi l := Finset.single_le_sum (fun l _=>hhi l) (Finset.mem_univ j)
  refine ⟨(div_nonneg (hlo j) (Real.sqrt_nonneg _)).trans hx.1.le,?_⟩
  exact hx.2.trans (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

lemma generalPlanar_scaled_type_windows_disjoint {ι : Type*} (g n : ℕ)
    (hq : 0<primitivePlanarEffectiveScale g n) (k : ι→ℕ) (lo hi : ι→ℝ)
    (hdis : Pairwise (fun j l=>k j≠k l ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo l) (hi l)))) :
    Pairwise (fun j l=>k j≠k l ∨ Disjoint
      (generalPlanarFamilyWindows g n lo hi j) (generalPlanarFamilyWindows g n lo hi l)) := by
  intro j l hjl
  rcases hdis hjl with hne|hset
  · exact Or.inl hne
  · right
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hs := Real.sqrt_pos.mpr hq
    apply Set.disjoint_left.mp hset
      (show x*Real.sqrt (primitivePlanarEffectiveScale g n)∈Ioc (lo j) (hi j) from
        ⟨(div_lt_iff₀ hs).mp hx.1,(le_div_iff₀ hs).mp hx.2⟩)
      (show x*Real.sqrt (primitivePlanarEffectiveScale g n)∈Ioc (lo l) (hi l) from
        ⟨(div_lt_iff₀ hs).mp hy.1,(le_div_iff₀ hs).mp hy.2⟩)

include C MI in
theorem generalPlanar_fixed_mixed_windows_moving_moments {ι : Type*} [Fintype ι]
    (k : ι→ℕ) (hk : ∀j,2≤k j) (a : ι→ℕ) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : ι→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j l=>k j≠k l ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo l) (hi l)))) :
    Tendsto (fun g=>(∫X : G.Moduli g (n g) (fun _=>0),
      ∏j,((generalPlanarWindowCount H X (fun _ : Fin 1=>k j)
        (generalPlanarFamilyWindowCap g (n g) hi)
        (fun _=>generalPlanarFamilyWindows g (n g) lo hi j)).descFactorial (a j):ℝ)
          ∂wpProbability G g (n g))-
      generalPlanarFamilyMovingWeight P k lo hi a (primitiveSaddleX g (n g))) atTop (𝓝 0) := by
  let R := ∑j,a j
  let lo' : Fin R→ℝ := fun i=>lo ((mixedSlotsEquiv a).symm i).1
  let hi' : Fin R→ℝ := fun i=>hi ((mixedSlotsEquiv a).symm i).1
  have hprod (x : ℝ) : generalPlanarStarWeight P R (expandedTypes a k) lo' hi' x=
      generalPlanarFamilyMovingWeight P k lo hi a x := by
    unfold generalPlanarStarWeight generalPlanarFamilyMovingWeight
    simpa only [expandedTypes,lo',hi'] using mixedSlots_prod (M:=ℝ) a R (mixedSlotsEquiv a)
      (fun j=>2*volumeModel P 0 (k j+1)/((k j).factorial:ℝ)*
        (x/(2*Real.pi^2))^(k j-2)*((hi j)^2-(lo j)^2))
  have hm := generalPlanar_fixed_windows_moving_moments H T C MI R (expandedTypes a k)
    (fun i=>hk _) n hn lo' hi' (fun i=>hlo _) (fun i=>hab _)
  simp_rw [hprod] at hm
  apply hm.congr'
  filter_upwards [(primitive_planar_scale_tendsto_atTop n hn).eventually_gt_atTop (0:ℝ)] with g hqg
  have hdisg := generalPlanar_scaled_type_windows_disjoint g (n g) hqg k lo hi hdis
  have he : ∀X : G.Moduli g (n g) (fun _=>0),
      (∏j,((generalPlanarWindowCount H X (fun _ : Fin 1=>k j)
        (generalPlanarFamilyWindowCap g (n g) hi)
        (fun _=>generalPlanarFamilyWindows g (n g) lo hi j)).descFactorial (a j):ℝ))=
      (generalPlanarWindowCount H X (expandedTypes a k)
        (generalPlanarFixedWindowCap g (n g) R hi')
        (generalPlanarStarScaledWindows R (primitivePlanarEffectiveScale g (n g)) lo' hi'):ℝ) := by
    intro X
    rw [generalPlanar_mixed_factorial_eq_expandedWindowCount_real H X k _ _ a hdisg]
    congr 1
    exact generalPlanarWindowCount_cutoff_eq H X (expandedTypes a k) _ _ _
      (fun i=>generalPlanar_family_window_subset_cap g (n g) lo hi hlo hab _)
      (generalPlanar_scaled_windows_subset_cap g (n g) R lo' hi' (fun i=>hlo _) (fun i=>hab _))
  simp_rw [he]

include C MI in
lemma generalPlanarWindowCount_lintegral_eq_ofReal_integral {g n r : ℕ}
    (hg : 1≤g) (k : Fin r→ℕ) (L : ℝ) (hL : L<2*Real.arsinh 1)
    (I : Fin r→Set ℝ) (hI : ∀i,MeasurableSet (I i)) (hsub : ∀i,I i⊆Icc 0 L) :
    (∫⁻X : G.Moduli g n (fun _=>0),(generalPlanarWindowCount H X k L I:ℝ≥0∞)
        ∂wpProbability G g n)=
      ENNReal.ofReal (∫X : G.Moduli g n (fun _=>0),(generalPlanarWindowCount H X k L I:ℝ)
        ∂wpProbability G g n) := by
  letI := wpProbability_isFinite G g n
  rw [ofReal_integral_eq_lintegral_ofReal
    (generalPlanarWindowCount_integrable H T C MI hg k L hL I hI hsub _)
    (ae_of_all _ (fun _=>Nat.cast_nonneg _))]
  simp

end WP.RandomGeometry
