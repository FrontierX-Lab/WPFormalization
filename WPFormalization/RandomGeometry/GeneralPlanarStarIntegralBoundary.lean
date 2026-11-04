import WPFormalization.RandomGeometry.GeneralPlanarStarIntegralDefinitions

/-! Fixed planar leaf bounds use the actual finite polynomial, including g=0. -/
noncomputable section
namespace WP.RandomGeometry
open MeasureTheory Set Filter
open scoped Topology

lemma general_planar_mixedBracket_nonneg (P : PsiTheory) (g n : ℕ) (hn : 1 ≤ n)
    (d : Fin n → ℕ) : 0 ≤ mixedBracket P g (List.ofFn d) := by
  rw [mixedBracket_eq_scaled_normalized_zero]
  apply mul_nonneg (by positivity)
  exact normalized_nonneg_nonempty P g _ (by simpa only [List.length_ofFn] using hn)
    0 ⟨le_rfl,y₀_pos.le⟩

/-- The genuine finite WP boundary polynomial is monotone in nonnegative
lengths, for every nonempty boundary vector, also in genus zero. -/
lemma general_planar_boundary_mono (P : PsiTheory) (g n : ℕ) (hn : 1 ≤ n)
    (L M : Fin n → ℝ) (hL : ∀i,0 ≤ L i) (hLM : ∀i,L i ≤ M i) :
    boundaryVolumeModel P g n L ≤ boundaryVolumeModel P g n M := by
  unfold boundaryVolumeModel
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (general_planar_mixedBracket_nonneg P g n hn d)
  apply Finset.prod_le_prod₀
  · intro i _
    exact div_nonneg (pow_nonneg (hL i) _) (by positivity)
  · intro i _
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (hL i) (hLM i) _) (by positivity)

lemma generalPlanarStarLeafLengths_nonneg (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∀j,0 ≤ generalPlanarStarLeafLengths k x j := by
  intro j
  refine Fin.addCases (fun a => ?_) (fun i => ?_) j
  · simp [generalPlanarStarLeafLengths]
  · simpa [generalPlanarStarLeafLengths] using hx

lemma generalPlanarStarLeafLengths_mono (k : ℕ) (x y : ℝ) (hxy : x ≤ y) :
    ∀j,generalPlanarStarLeafLengths k x j ≤ generalPlanarStarLeafLengths k y j := by
  intro j
  refine Fin.addCases (fun a => ?_) (fun i => ?_) j
  · simp [generalPlanarStarLeafLengths]
  · simpa [generalPlanarStarLeafLengths] using hxy

lemma generalPlanarStarRootLengths_nonneg (n r : ℕ) (k : Fin r → ℕ)
    (x : Fin r → ℝ) (hx : ∀i,0 ≤ x i) :
    ∀j,0 ≤ generalPlanarStarRootLengths n r k x j := by
  intro j
  refine Fin.addCases (fun a => ?_) (fun i => ?_) j
  · simp [generalPlanarStarRootLengths]
  · simpa [generalPlanarStarRootLengths] using hx i

lemma generalPlanarStarRootLengths_sum (n r : ℕ) (k : Fin r → ℕ) (x : Fin r → ℝ) :
    (∑j,generalPlanarStarRootLengths n r k x j) = ∑i,x i := by
  simp [generalPlanarStarRootLengths,Fin.sum_univ_add]

lemma general_planar_star_leaf_bounds (P : PsiTheory) (k : ℕ) (x L : ℝ)
    (hx : 0 ≤ x) (hxL : x ≤ L) :
    volumeModel P 0 (k+1) ≤ boundaryVolumeModel P 0 (k+1) (generalPlanarStarLeafLengths k x) ∧
    boundaryVolumeModel P 0 (k+1) (generalPlanarStarLeafLengths k x) ≤
      boundaryVolumeModel P 0 (k+1) (generalPlanarStarLeafLengths k L) := by
  constructor
  · rw [← WP.Geometry.boundaryVolumeModel_zero P 0 (k+1)]
    exact general_planar_boundary_mono P 0 (k+1) (by omega) _ _ (fun _ => le_rfl)
      (generalPlanarStarLeafLengths_nonneg k x hx)
  · exact general_planar_boundary_mono P 0 (k+1) (by omega) _ _
      (generalPlanarStarLeafLengths_nonneg k x hx) (generalPlanarStarLeafLengths_mono k x L hxL)

def generalPlanarStarLeafCorrection (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ) (L : ℝ) : ℝ :=
  (∏i,boundaryVolumeModel P 0 (k i+1) (generalPlanarStarLeafLengths (k i) L)) /
    ∏i,volumeModel P 0 (k i+1)

lemma general_planar_star_leaf_correction_tendsto (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (hk : ∀i,2 ≤ k i) (L : ℕ → ℝ) (hL : Tendsto L atTop (𝓝 0)) :
    Tendsto (fun g => generalPlanarStarLeafCorrection P r k (L g)) atTop (𝓝 1) := by
  have hv (i : Fin r) : 0 < volumeModel P 0 (k i+1) :=
    diagonal_volume_pos_nonempty P 0 _ (by omega) (by unfold Stable;have := hk i;omega)
  have hprod : (∏i,volumeModel P 0 (k i+1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hv i).ne')
  have hf : Continuous (fun x : ℝ => ∏i,boundaryVolumeModel P 0 (k i+1)
      (generalPlanarStarLeafLengths (k i) x)) := by
    apply continuous_finset_prod
    intro i _
    exact (general_planar_boundary_polynomial_continuous P 0 _).comp
      (generalPlanarStarLeafLengths_continuous (k i))
  have ht := (hf.tendsto 0).comp hL
  have he : (∏i,boundaryVolumeModel P 0 (k i+1) (generalPlanarStarLeafLengths (k i) 0)) =
      ∏i,volumeModel P 0 (k i+1) := by
    apply Finset.prod_congr rfl
    intro i _
    have hz : generalPlanarStarLeafLengths (k i) 0 = (fun _ => 0) := by
      funext j
      refine Fin.addCases (fun a => ?_) (fun t => ?_) j <;> simp [generalPlanarStarLeafLengths]
    rw [hz,WP.Geometry.boundaryVolumeModel_zero]
  rw [he] at ht
  simpa only [generalPlanarStarLeafCorrection,Function.comp_def,div_self hprod] using ht.div_const (∏i,volumeModel P 0 (k i+1))

def generalPlanarStarBoundaryCorrection (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (L : ℝ) : ℝ := Real.exp (r*L/2)*generalPlanarStarLeafCorrection P r k L

lemma general_planar_star_boundary_correction_tendsto (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (hk : ∀i,2 ≤ k i) (L : ℕ → ℝ) (hL : Tendsto L atTop (𝓝 0)) :
    Tendsto (fun g => generalPlanarStarBoundaryCorrection P r k (L g)) atTop (𝓝 1) := by
  have he : Tendsto (fun g => Real.exp (r*L g/2)) atTop (𝓝 1) := by
    simpa only [mul_zero,zero_div,Real.exp_zero,Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp ((hL.const_mul (r:ℝ)).div_const 2)
  simpa only [generalPlanarStarBoundaryCorrection,one_mul] using
    he.mul (general_planar_star_leaf_correction_tendsto P r k hk L hL)

lemma general_planar_star_root_bounds (P : PsiTheory) (g n r : ℕ) (k : Fin r → ℕ)
    (hg : 1 ≤ g) (hm : 1 ≤ n-(∑i,k i)+r) (x : Fin r → ℝ) (L : ℝ)
    (hx : ∀i,0 ≤ x i) (hxL : ∀i,x i ≤ L) :
    volumeModel P g (n-(∑i,k i)+r) ≤
      boundaryVolumeModel P g (n-(∑i,k i)+r) (generalPlanarStarRootLengths n r k x) ∧
    boundaryVolumeModel P g (n-(∑i,k i)+r) (generalPlanarStarRootLengths n r k x) ≤
      Real.exp (r*L/2)*volumeModel P g (n-(∑i,k i)+r) := by
  have hv : 0 < volumeModel P g (n-(∑i,k i)+r) :=
    diagonal_volume_pos_nonempty P g _ hm (by unfold Stable;omega)
  have hb := pants_boundary_volume_bounds P g _ hg hm _
    (generalPlanarStarRootLengths_nonneg n r k x hx)
  have hsum : (∑j,generalPlanarStarRootLengths n r k x j) ≤ (r:ℝ)*L := by
    rw [generalPlanarStarRootLengths_sum]
    exact (Finset.sum_le_sum (fun i _ => hxL i)).trans_eq (by simp)
  refine ⟨by simpa only [one_mul] using (le_div_iff₀ hv).mp hb.1,?_⟩
  exact ((div_le_iff₀ hv).mp hb.2).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right hsum (by norm_num))) hv.le)

lemma general_planar_star_integrand_bounds (P : PsiTheory) (g n r : ℕ) (k : Fin r → ℕ)
    (hg : 1 ≤ g) (hm : 1 ≤ n-(∑i,k i)+r) (hk : ∀i,2 ≤ k i)
    (x : Fin r → ℝ) (L : ℝ) (hx : ∀i,0 ≤ x i) (hxL : ∀i,x i ≤ L) :
    (volumeModel P g (n-(∑i,k i)+r)*∏i,volumeModel P 0 (k i+1)) ≤
      generalPlanarStarVolumeIntegrand P g n r k x ∧
    generalPlanarStarVolumeIntegrand P g n r k x ≤
      generalPlanarStarBoundaryCorrection P r k L *
        (volumeModel P g (n-(∑i,k i)+r)*∏i,volumeModel P 0 (k i+1)) := by
  have hvroot : 0 < volumeModel P g (n-(∑i,k i)+r) :=
    diagonal_volume_pos_nonempty P g _ hm (by unfold Stable;omega)
  have hvleaf (i : Fin r) : 0 < volumeModel P 0 (k i+1) :=
    diagonal_volume_pos_nonempty P 0 _ (by omega) (by unfold Stable;have := hk i;omega)
  have hprod0 : 0 < ∏i,volumeModel P 0 (k i+1) := Finset.prod_pos (fun i _ => hvleaf i)
  have hbroot := general_planar_star_root_bounds P g n r k hg hm x L hx hxL
  have hbleaf (i : Fin r) := general_planar_star_leaf_bounds P (k i) (x i) L (hx i) (hxL i)
  have hxleaf (i : Fin r) : 0 ≤
      boundaryVolumeModel P 0 (k i+1) (generalPlanarStarLeafLengths (k i) (x i)) :=
    (hvleaf i).le.trans (hbleaf i).1
  have hlow := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => (hvleaf i).le) (fun i _ => (hbleaf i).1)
  have hhigh := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => hxleaf i) (fun i _ => (hbleaf i).2)
  constructor
  · exact mul_le_mul hbroot.1 hlow hprod0.le (hvroot.le.trans hbroot.1)
  · have he := mul_le_mul hbroot.2 hhigh (Finset.prod_nonneg (fun i _ => hxleaf i))
      (mul_nonneg (Real.exp_pos _).le hvroot.le)
    apply he.trans_eq
    unfold generalPlanarStarBoundaryCorrection generalPlanarStarLeafCorrection
    field_simp [hprod0.ne']

end WP.RandomGeometry
