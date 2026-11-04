import WPFormalization.RandomGeometry.GeneralPlanarOriginalScaleCountLimits

/-! Zero-type coordinates are handled locally, so the marked-space criterion
can quantify every integer type, including the absent types zero and one. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Set Filter
open scoped Topology ENNReal NNReal Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)

lemma generalPlanarWindowCount_zero_small_type {g n r : ℕ}
    (X : G.Moduli g n (fun _=>0)) (k : Fin r→ℕ) (L : ℝ) (I : Fin r→Set ℝ)
    (i : Fin r) (hk : k i<2) : generalPlanarWindowCount H X k L I=0 := by
  letI : IsEmpty (OrderedGeneralPlanarTuple (H:=H) X k L) := by
    constructor
    intro γ
    obtain ⟨_,S,hS,hcard⟩ := (H.mem_shortPlanar X (k i) L (γ.val i)).mp (γ.property.2 i)
    have hs := H.planar_stable (γ.val i) S hS
    omega
  unfold generalPlanarWindowCount
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

lemma generalPlanar_original_family_count_zero_small_type {ι : Type*} [Fintype ι]
    {g n : ℕ} (X : G.Moduli g n (fun _=>0)) (k : ι→ℕ) (lo hi : ι→ℝ)
    (j : ι) (hk : k j<2) : generalPlanarOriginalFamilyCounts H g n k lo hi X j=0 :=
  generalPlanarWindowCount_zero_small_type H X (fun _ : Fin 1=>k j) _ _ 0 hk

lemma generalPlanar_original_family_counts_restrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    {g n : ℕ} (X : G.Moduli g n (fun _=>0)) (k : ι→ℕ) (lo hi : ι→ℝ)
    (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j) (e : κ→ι) (j : κ) :
    generalPlanarOriginalFamilyCounts H g n (k∘e) (lo∘e) (hi∘e) X j=
      generalPlanarOriginalFamilyCounts H g n k lo hi X (e j) := by
  unfold generalPlanarOriginalFamilyCounts
  exact generalPlanarWindowCount_cutoff_eq H X (fun _ : Fin 1=>k (e j)) _ _ _
    (fun _=>pants_scaled_window_subset_cap _ (lo∘e) (hi∘e) (fun j=>hlo _) (fun j=>hab _) j)
    (fun _=>pants_scaled_window_subset_cap _ lo hi hlo hab (e j))

lemma finite_prod_eq_valid_prod {ι M : Type*} [Fintype ι] [CommMonoid M]
    (p : ι→Prop) [DecidablePred p] (f : ι→M) (h : ∀j,¬p j→f j=1) :
    ∏j,f j=∏j : {j //p j},f j.val := by
  rw [←Fintype.prod_subtype_mul_prod_subtype p f]
  have he : (∏j : {j //¬p j},f j.val)=1 := Finset.prod_eq_one (fun j _=>h j.val j.property)
  rw [he,mul_one]

include C MI in
theorem generalPlanar_original_all_type_mixed_factorial_limits {d : ℕ}
    (k : Fin d→ℕ) (n : ℕ→ℕ)
    (hn : Tendsto (fun g : ℕ=>(n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin d→ℝ) (hlo : ∀j,0≤lo j) (hab : ∀j,lo j≤hi j)
    (hdis : Pairwise (fun j m=>k j≠k m ∨ Disjoint (Ioc (lo j) (hi j)) (Ioc (lo m) (hi m))))
    (l : ℝ≥0∞) (hl : Tendsto (fun g : ℕ=>ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    MixedFactorialMomentLimit (fun g=>wpProbability G g (n g))
      (fun g=>generalPlanarOriginalFamilyCounts H g (n g) k lo hi)
      (generalPlanarDensityWindowRates P k lo hi l) := by
  intro a
  by_cases hbad : ∃j,k j<2 ∧ 0<a j
  · obtain ⟨j,hkj,haj⟩ := hbad
    have hz (g : ℕ) (X : G.Moduli g (n g) (fun _=>0)) :
        (∏i,(((generalPlanarOriginalFamilyCounts H g (n g) k lo hi X i).descFactorial (a i):ℕ):ℝ≥0∞))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [generalPlanar_original_family_count_zero_small_type H X k lo hi j hkj]
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr haj]
      simp
    have hr : (∏i,((generalPlanarDensityWindowRates P k lo hi l i:ℝ≥0∞)^(a i)))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [generalPlanarDensityWindowRates,generalPlanarTypeWeight,not_le.mpr hkj,haj.ne']
    simp_rw [hz,lintegral_zero,hr]
    exact tendsto_const_nhds
  · have ha (j : Fin d) (hj : ¬2≤k j) : a j=0 := by
      by_contra hne
      exact hbad ⟨j,by omega,Nat.pos_of_ne_zero hne⟩
    let V := {j : Fin d //2≤k j}
    have hd : Pairwise (fun j m : V=>k j.val≠k m.val ∨
        Disjoint (Ioc (lo j.val) (hi j.val)) (Ioc (lo m.val) (hi m.val))) := by
      intro j m hjm
      exact hdis (fun h=>hjm (Subtype.ext h))
    have hm := generalPlanar_original_fixed_mixed_lintegral_moments H T C MI
      (fun j : V=>k j.val) (fun j=>j.property) (fun j=>a j.val) n hn
      (fun j=>lo j.val) (fun j=>hi j.val) (fun j=>hlo _) (fun j=>hab _) hd
      _ (planar_density_saddle_mem l).1 (primitive_saddle_tendsto_density_fast n hn l hl)
    have hrate := generalPlanar_density_window_rates_eq P (fun j : V=>k j.val) (fun j=>j.property)
      (fun j=>lo j.val) (fun j=>hi j.val) l
    rw [←hrate] at hm
    have hprod (g : ℕ) (X : G.Moduli g (n g) (fun _=>0)) :
        (∏j,(((generalPlanarOriginalFamilyCounts H g (n g) k lo hi X j).descFactorial (a j):ℕ):ℝ≥0∞))=
        ∏j : V,(((generalPlanarOriginalFamilyCounts H g (n g) (fun j : V=>k j.val)
          (fun j=>lo j.val) (fun j=>hi j.val) X j).descFactorial (a j.val):ℕ):ℝ≥0∞) := by
      rw [finite_prod_eq_valid_prod (fun j=>2≤k j) _ (fun j hj=>by simp [ha j hj])]
      apply Finset.prod_congr rfl
      intro j _
      exact congrArg (fun z : ℕ=>(z.descFactorial (a j.val):ℝ≥0∞))
        (generalPlanar_original_family_counts_restrict H X k lo hi hlo hab Subtype.val j).symm
    have hprodRate : (∏j,((generalPlanarDensityWindowRates P k lo hi l j:ℝ≥0∞)^(a j)))=
        ∏j : V,((generalPlanarDensityWindowRates P (fun j : V=>k j.val)
          (fun j=>lo j.val) (fun j=>hi j.val) l j:ℝ≥0∞)^(a j.val)) := by
      exact finite_prod_eq_valid_prod (fun j=>2≤k j) _ (fun j hj=>by simp [ha j hj])
    rw [hprodRate]
    simpa only [hprod] using hm

end WP.RandomGeometry
