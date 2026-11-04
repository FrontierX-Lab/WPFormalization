import WPFormalization.Critical.PrimitiveCountPacking
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.PrimitivePacking
open Set MeasureTheory Finset
open WP.External.HyperbolicPacking
open scoped Classical ENNReal

lemma epsilon_pos : 0 < epsilon := by norm_num [epsilon]
lemma diskArea_pos {r : ℝ} (hr : 0 < r) : 0 < diskArea r := by
  unfold diskArea
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (sub_pos.mpr (Real.one_lt_cosh.mpr hr.ne'))

/-- A positive lower area for every standard collar at the fixed thin cutoff,
derived from the actual sinh formula rather than assumed as a count. -/
lemma collar_area_lower (l : ℝ) (hl : 0 < l) (hsmall : l < 2*epsilon) :
    4/Real.cosh epsilon ≤ 2*l/Real.sinh (l/2) := by
  have hx : 0 < l/2 := half_pos hl
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh hx
    Real.continuous_sinh.continuousOn (fun x _ => Real.hasDerivAt_sinh x)
  have hcε : c ≤ epsilon := by linarith [hc.2]
  have hcosh : Real.cosh c ≤ Real.cosh epsilon :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_pos hc.1,abs_of_pos epsilon_pos];exact hcε)
  simp only [Real.sinh_zero,sub_zero] at he
  have hbound : Real.sinh (l/2) ≤ (l/2)*Real.cosh epsilon := by
    have hh : Real.sinh (l/2)/(l/2) ≤ Real.cosh epsilon := by rw [←he];exact hcosh
    simpa [mul_comm] using (div_le_iff₀ hx).mp hh
  apply (div_le_div_iff₀ (Real.cosh_pos _) (Real.sinh_pos_iff.mpr hx)).mpr
  nlinarith

lemma thinCores_card_area_bound {S : QuotientSurface} (C : PrimitiveGeometry S)
    (H : PackingClassics S C) :
    ((thinCores C).card:ℝ)*(4/Real.cosh epsilon) ≤ (S.area univ).toReal := by
  apply finite_packing_card_mul_le S.area (thinCores C) (coreCollar C) univ S.finite_area
    H.collars_measurable H.collars_disjoint (fun _ _ => subset_univ _) _ (by have := epsilon_pos; positivity)
  intro γ hγ
  rw [H.collar_area γ hγ]
  apply ENNReal.ofReal_le_ofReal
  exact collar_area_lower _ (C.representative γ).period_pos (mem_filter.mp hγ).2

lemma thick_separated_card_area_bound {S : QuotientSurface} {C : PrimitiveGeometry S}
    (H : PackingClassics S C) (s : Finset S.Point)
    (ht : ∀ p ∈ s, Thick S p)
    (hsep : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → epsilon/2 ≤ dist p q) :
    (s.card:ℝ)*diskArea (epsilon/4) ≤ (S.area univ).toReal := by
  have hd := separated_balls_disjoint s (epsilon/4) (fun p hp q hq hne => by
    convert hsep p hp q hq hne using 1 <;>ring)
  apply finite_packing_card_mul_le S.area s (fun p => Metric.ball p (epsilon/4)) univ
    S.finite_area (fun _ _ => measurableSet_ball) hd (fun _ _ => subset_univ _) _
    (diskArea_pos (by have := epsilon_pos; positivity)).le
  intro p hp
  exact (H.embedded_disk_area p (ht p hp) _ (by have := epsilon_pos; positivity) (by linarith [epsilon_pos])).ge

/-- An actual finite separated net in the complete thick part, constructed by
area packing and maximal cardinality, uniformly from an area upper bound. -/
lemma thick_finite_net {S : QuotientSurface} {C : PrimitiveGeometry S}
    (H : PackingClassics S C) (A : ℝ) (hA : (S.area univ).toReal ≤ A) :
    ∃ s : Finset S.Point, (∀ p ∈ s, Thick S p) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → epsilon/2 ≤ dist p q) ∧
      s.card ≤ Nat.ceil (A/diskArea (epsilon/4)) ∧
      ∀ p, Thick S p → ∃ q ∈ s, dist p q < epsilon/2 := by
  apply finite_net_of_separated_card_bound (fun p => Thick S p) _ (by have := epsilon_pos; positivity)
  intro s ht hs
  have hp := (thick_separated_card_area_bound H s ht hs).trans hA
  have hc := diskArea_pos (show 0 < epsilon/4 by have := epsilon_pos; positivity)
  have hdiv : (s.card:ℝ) ≤ A/diskArea (epsilon/4) := (le_div_iff₀ hc).mpr hp
  exact_mod_cast hdiv.trans (Nat.le_ceil _)

end WP.Critical.PrimitivePacking
