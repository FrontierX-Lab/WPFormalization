import WPFormalization.RandomGeometry.GeneralPlanarRemainderBudgets

/-! A real finite-sum form of the actual nonstar expectation, with termwise
bounds from the genuine physical cut integral. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set Filter
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    {g n r : ℕ} {k : Fin r→ℕ}

def generalPlanarRemainderMomentTerm (o : GeneralPlanarRemainderOrbit T g n r k)
    (I : Fin r→Set ℝ) : ℝ :=
  (T.coefficient o.val.val).toReal*
    (generalPlanarCutWindowIntegral (G:=G) (T.cut o.val.val) I).toReal/volumeModel P g n

lemma generalPlanarRemainder_cut_integral_ne_top (hg : 1≤g) (hn : (∑i,k i)<n)
    (o : GeneralPlanarRemainderOrbit T g n r k)
    (I : Fin r→Set ℝ) (L : ℝ) (hL : 0≤L) (hsub : ∀i,I i⊆Icc 0 L) :
    generalPlanarCutWindowIntegral (G:=G) (T.cut o.val.val) I≠⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (generalPlanarRemainder_cut_integral_upper T hg hn o I L hL hsub)

include C MI in
lemma generalPlanarRemainder_real_moment_eq_sum (hg : 2≤g) (hn : (∑i,k i)<n)
    (I : Fin r→Set ℝ) (hI : ∀i,MeasurableSet (I i)) (L : ℝ)
    (hL0 : 0≤L) (hL : L<2*Real.arsinh 1) (hsub : ∀i,I i⊆Icc 0 L) :
    (∫X : G.Moduli g n (fun _=>0),
      (generalPlanarRemainderWindowSum T g n r k (pantsWindowTest I) X).toReal
        ∂wpProbability G g n)=
      ∑o : GeneralPlanarRemainderOrbit T g n r k,generalPlanarRemainderMomentTerm T o I := by
  have hfinite : ∀X : G.Moduli g n (fun _=>0),
      generalPlanarRemainderWindowSum T g n r k (pantsWindowTest I) X≠⊤ := by
    intro X
    exact ne_top_of_le_ne_top (by simp : (generalPlanarWindowCount H X k L I:ℝ≥0∞)≠⊤)
      (generalPlanar_remainder_le_count H T C (by omega) X k L hL I hsub)
  have hterms : ∀o : GeneralPlanarRemainderOrbit T g n r k,
      T.coefficient o.val.val*generalPlanarCutWindowIntegral (G:=G) (T.cut o.val.val) I≠⊤ := by
    intro o
    apply ENNReal.mul_ne_top
    · exact ne_top_of_le_ne_top (by simp) (multicurve_coefficient_le_one T o.val.val)
    · exact generalPlanarRemainder_cut_integral_ne_top T (by omega) hn o I L hL0 hsub
  have hmass : (G.wpMeasure g n (fun _=>0) univ).toReal=volumeModel P g n :=
    WP.Geometry.cuspVolume_eq_volumeModel P G g n (by unfold Stable;omega)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _=>ENNReal.toReal_nonneg))
    (generalPlanarRemainderWindowSum_measurable H T MI k I hI).ennreal_toReal.aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_toReal (hfinite _)]
  rw [generalPlanarRemainder_probability_lintegral T MI hg (by
    intro h;have hh:=congrArg Prod.snd h;simp only at hh;omega) k _ (pantsWindowTest_measurable I hI),
    ENNReal.toReal_mul,ENNReal.toReal_inv,hmass,tsum_fintype]
  change (volumeModel P g n)⁻¹*
    (∑o : GeneralPlanarRemainderOrbit T g n r k,
      T.coefficient o.val.val*generalPlanarCutWindowIntegral (G:=G) (T.cut o.val.val) I).toReal=_
  rw [ENNReal.toReal_sum (fun o _=>hterms o),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o ho
  rw [ENNReal.toReal_mul,generalPlanarRemainderMomentTerm]
  ring

lemma generalPlanarRemainderMomentTerm_nonneg (hg : 2≤g) (hn : 1≤n)
    (o : GeneralPlanarRemainderOrbit T g n r k) (I : Fin r→Set ℝ) :
    0≤generalPlanarRemainderMomentTerm T o I := by
  have hv := (diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)).le
  exact div_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hv

lemma generalPlanarRemainderMomentTerm_upper (hg : 1≤g) (hn : (∑i,k i)<n)
    (o : GeneralPlanarRemainderOrbit T g n r k) (I : Fin r→Set ℝ)
    (L : ℝ) (hL : 0≤L) (hsub : ∀i,I i⊆Icc 0 L) :
    generalPlanarRemainderMomentTerm T o I≤
      Real.exp ((r:ℝ)*L)*(generalPlanarZeroVolumeCap P ((∑i,k i)+2*r))^r*
        (volumeModel P g (n-generalPlanarOrbitCusps T hg o.val+generalPlanarOrbitDegree T hg o.val)/
          volumeModel P g n)*(L^2/2)^r := by
  have hn1 : 1≤n := by omega
  have ha := generalPlanarOrbit_cusps_upper T hg o.val
  have hv := (diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)).le
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (generalPlanarRemainder_cut_integral_upper T hg hn o I L hL hsub)
  have hvr := (diagonal_volume_pos_nonempty P g
    (n-generalPlanarOrbitCusps T hg o.val+generalPlanarOrbitDegree T hg o.val)
    (by omega) (by unfold Stable;omega)).le
  have hcap := (generalPlanarZeroVolumeCap_pos P ((∑i,k i)+2*r)).le
  rw [ENNReal.toReal_ofReal (by positivity)] at hu
  have hc : (T.coefficient o.val.val).toReal≤1 := by
    simpa using ENNReal.toReal_mono (by simp : (1:ℝ≥0∞)≠⊤)
      (multicurve_coefficient_le_one T o.val.val)
  unfold generalPlanarRemainderMomentTerm
  calc
    _≤(generalPlanarCutWindowIntegral (G:=G) (T.cut o.val.val) I).toReal/volumeModel P g n := by
      apply div_le_div_of_nonneg_right _ hv
      simpa using mul_le_mul_of_nonneg_right hc
        (ENNReal.toReal_nonneg : 0≤(generalPlanarCutWindowIntegral (G:=G) (T.cut o.val.val) I).toReal)
    _≤_ := (div_le_div_of_nonneg_right hu hv).trans_eq (by ring)

end WP.RandomGeometry
