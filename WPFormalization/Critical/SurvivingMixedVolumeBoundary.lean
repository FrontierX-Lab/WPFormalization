import WPFormalization.Critical.SurvivingMixedVolumeRatios
import WPFormalization.Statements.Boundary
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsIntegrals

/-! Physical boundary factors of the actual root in the surviving mixed cut.
The slots are s,t,t followed by the original remaining zero cusp lengths. -/
noncomputable section
set_option maxHeartbeats 200000
namespace WP.Critical
open Filter Set MeasureTheory
open scoped Topology

/-- The first r physical variables are pants waists; the last k are loop cuts.
Each loop contributes the same physical length to two root boundary slots. -/
def survivingBoundaryCore (r k : ℕ) (x : Fin (r+k) → ℝ) : Fin (r+(k+k)) → ℝ :=
  Fin.append (fun j => x (Fin.castAdd k j))
    (Fin.append (fun i => x (Fin.natAdd r i)) (fun i => x (Fin.natAdd r i)))

/-- Zero-padding, totalized even before there are enough cusp labels. -/
def survivingZeroPad (p m : ℕ) (x : Fin p → ℝ) : Fin m → ℝ :=
  fun i => if h : i.val < p then x ⟨i.val,h⟩ else 0

def survivingBoundaryLengths (r k n : ℕ) (x : Fin (r+k) → ℝ) : Fin (n-r+2*k) → ℝ :=
  survivingZeroPad (r+(k+k)) (n-r+2*k) (survivingBoundaryCore r k x)

def survivingBoundaryFactor (r k : ℕ) (Y : ℝ) (x : Fin (r+k) → ℝ) : ℝ :=
  (∏ j : Fin r, boundaryFactor Y (x (Fin.castAdd k j))) *
    ∏ i : Fin k, boundaryFactor Y (x (Fin.natAdd r i))^2

lemma survivingBoundaryCore_mem (r k : ℕ) (x : Fin (r+k) → ℝ) (L : ℝ)
    (hx : ∀ i, x i ∈ Icc 0 L) : ∀ i, survivingBoundaryCore r k x i ∈ Icc 0 L := by
  intro i
  refine Fin.addCases (m := r) (n := k+k) (fun j => ?_) (fun j => ?_) i
  · simpa only [survivingBoundaryCore,Fin.append_left] using hx (Fin.castAdd k j)
  · simp only [survivingBoundaryCore,Fin.append_right]
    refine Fin.addCases (m := k) (n := k) (fun l => ?_) (fun l => ?_) j
    · simpa only [Fin.append_left] using hx (Fin.natAdd r l)
    · simpa only [Fin.append_right] using hx (Fin.natAdd r l)

lemma survivingZeroPad_mem (p m : ℕ) (x : Fin p → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hx : ∀ i, x i ∈ Icc 0 L) : ∀ i, survivingZeroPad p m x i ∈ Icc 0 L := by
  intro i
  unfold survivingZeroPad
  split_ifs
  · exact hx _
  · exact ⟨le_rfl,hL⟩

lemma survivingZeroPad_prod (p m : ℕ) (hpm : p ≤ m) (x : Fin p → ℝ)
    (f : ℝ → ℝ) (hf : f 0=1) :
    (∏ i, f (survivingZeroPad p m x i)) = ∏ j, f (x j) := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hpm
  have hh : survivingZeroPad p (p+q) x=Fin.append x (fun _ : Fin q => 0) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [survivingZeroPad]
    · simp [survivingZeroPad]
  rw [hh,Fin.prod_univ_add]
  simp [hf]

lemma survivingBoundaryLengths_prod (r k n : ℕ) (hn : 2*r ≤ n)
    (Y : ℝ) (x : Fin (r+k) → ℝ) :
    (∏ i, boundaryFactor Y (survivingBoundaryLengths r k n x i)) =
      survivingBoundaryFactor r k Y x := by
  rw [survivingBoundaryLengths,survivingZeroPad_prod _ _ (by omega) _ _
    (boundaryFactor_zero_length Y)]
  simp only [survivingBoundaryCore,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    survivingBoundaryFactor]
  rw [Finset.prod_pow]
  ring

lemma survivingBoundaryLengths_continuous (r k n : ℕ) :
    Continuous (survivingBoundaryLengths r k n) := by
  apply continuous_pi
  intro i
  unfold survivingBoundaryLengths survivingZeroPad
  split_ifs
  · unfold survivingBoundaryCore
    fun_prop
  · fun_prop

set_option backward.isDefEq.respectTransparency false in
lemma survivingBoundaryFactor_continuous (r k : ℕ) (x : Fin (r+k) → ℝ) :
    Continuous (fun Y : Icc (0:ℝ) y₀ => survivingBoundaryFactor r k Y x) := by
  have hf (a : ℝ) : Continuous (fun Y : Icc (0:ℝ) y₀ => boundaryFactor (Y:ℝ) a) := by
    have hh : Continuous (fun Y : Icc (0:ℝ) y₀ =>
        ((Y,a) : (Icc (0:ℝ) y₀) × ℝ)) :=
      continuous_id.prodMk continuous_const
    have hh' := boundaryFactor_joint_continuous.comp hh
    change Continuous (fun Y : Icc (0:ℝ) y₀ => boundaryFactor (Y:ℝ) a) at hh'
    exact hh'
  unfold survivingBoundaryFactor
  exact (continuous_finsetProd _ (fun j _ => hf (x (Fin.castAdd k j)))).mul
    (continuous_finsetProd _ (fun i _ => (hf (x (Fin.natAdd r i))).pow 2))

lemma survivingBoundaryFactor_pos (r k : ℕ) (Y : ℝ) (x : Fin (r+k) → ℝ) :
    0 < survivingBoundaryFactor r k Y x := by
  apply mul_pos
  · exact Finset.prod_pos (fun _ _ => boundaryFactor_pos _ _)
  · exact Finset.prod_pos (fun _ _ => sq_pos_of_pos (boundaryFactor_pos _ _))

/-- The actual root boundary-volume ratio converges to the canonical b_0
product, for every bounded physical point. The dummy zero slot makes this
include r=k=0 without invoking a positive-dimensional boundary premise. -/
lemma surviving_mixed_boundary_ratio (P : PsiTheory) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop)
    (hd : Tendsto (fun g => (n g:ℝ)/g) atTop (𝓝 0)) (r k : ℕ)
    (L : ℝ) (hL : 0 ≤ L) (x : Fin (r+k) → ℝ) (hx : ∀ i, x i ∈ Icc 0 L) :
    Tendsto (fun g => boundaryVolumeModel P (g-k) (n g-r+2*k)
      (survivingBoundaryLengths r k (n g) x)/volumeModel P (g-k) (n g-r+2*k))
      atTop (𝓝 (survivingBoundaryFactor r k 0 x)) := by
  let d : ℕ → ℝ := fun g => ((n g-r+2*k:ℕ):ℝ)/((g-k:ℕ):ℝ)
  have hdz : Tendsto d atTop (𝓝 0) :=
    surviving_shifted_density (fun g => n g-r) (surviving_sub_density n hd r) k (2*k)
  have hY : Tendsto (fun g => densityY (d g)) atTop (𝓝 0) := by
    apply Analysis.densityY_tendsto_zero_right.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨hdz,Eventually.of_forall (fun g => by
      change (0:ℝ) ≤ ((n g-r+2*k:ℕ):ℝ)/((g-k:ℕ):ℝ)
      positivity)⟩
  let Y0 : Icc (0:ℝ) y₀ := ⟨0,le_rfl,y₀_pos.le⟩
  let Yg : ℕ → Icc (0:ℝ) y₀ := fun g => ⟨densityY (d g),
    (Analysis.densityY_spec _ (by dsimp [d]; positivity)).1.1,
    (Analysis.densityY_spec _ (by dsimp [d]; positivity)).1.2.le⟩
  have hYs : Tendsto Yg atTop (𝓝 Y0) := tendsto_subtype_rng.mpr hY
  have hfactor := (survivingBoundaryFactor_continuous r k x).continuousAt.tendsto.comp hYs
  have hrel : Tendsto (fun g => boundaryVolumeModel P (g-k) (n g-r+2*k)
      (survivingBoundaryLengths r k (n g) x)/
      (volumeModel P (g-k) (n g-r+2*k)*survivingBoundaryFactor r k (densityY (d g)) x))
      atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨G,hG⟩ := bounded_boundaries P (r+(k+k)+1) (by omega) L hL (ε/2) (by positivity)
    filter_upwards [(tendsto_sub_atTop_nat k).eventually_ge_atTop G,
      hn.eventually_ge_atTop (2*r+1)] with g hg hng
    have hlen := survivingZeroPad_mem (r+(k+k)) (n g-r+2*k) _ L hL (survivingBoundaryCore_mem r k x L hx)
    have hz : ∀ i : Fin (n g-r+2*k), r+(k+k)+1 ≤ i.val →
        survivingBoundaryLengths r k (n g) x i=0 := by
      intro i hi
      simp only [survivingBoundaryLengths,survivingZeroPad]
      exact dif_neg (by omega)
    have hh := hG (g-k) hg (n g-r+2*k) (by omega)
      (survivingBoundaryLengths r k (n g) x) (fun i => (hlen i).1) (fun i => (hlen i).2) hz
    rw [survivingBoundaryLengths_prod r k (n g) (by omega)] at hh
    exact (by simpa only [Real.dist_eq] using hh.trans_lt (half_lt_self hε))
  have hh := hrel.mul hfactor
  simp only [one_mul] at hh
  apply hh.congr
  intro g
  change _/(_*survivingBoundaryFactor r k (densityY (d g)) x)*
    survivingBoundaryFactor r k (densityY (d g)) x = _
  rw [div_mul_eq_div_div,div_mul_cancel₀ _ (survivingBoundaryFactor_pos r k _ x).ne']

end WP.Critical
