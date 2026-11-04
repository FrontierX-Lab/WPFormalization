import WPFormalization.Critical.PrimitiveCountNet
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.PrimitivePacking
open Set MeasureTheory Finset
open WP.External.HyperbolicPacking
open scoped Classical ENNReal

lemma deck_orbit_separated {S : QuotientSurface} (p : S.Point) (hp : Thick S p)
    (z : UpperHalfPlane) (hz : S.project z=p) (η η' : S.Γ) (hne : η≠η') :
    2*epsilon ≤ dist (η.val z) (η'.val z) := by
  have hn : η⁻¹*η'≠1 := by
    intro he
    apply hne
    calc
      η=η*1 := by simp
      _=η*(η⁻¹*η') := congrArg (fun x : S.Γ => η*x) he.symm
      _=η' := by group
  have ht := hp z hz (η⁻¹*η') hn
  have hd : dist z ((η⁻¹*η').val z) = dist (η.val z) (η'.val z) := by
    rw [←η.val.isometry.dist_eq z ((η⁻¹*η').val z)]
    change dist (η.val z) ((η*(η⁻¹*η')).val z) = _
    rw [show η*(η⁻¹*η')=η' by group]
  exact hd ▸ ht

lemma deck_ball_card_area_bound {S : QuotientSurface} {C : PrimitiveGeometry S}
    (H : PackingClassics S C) (p : S.Point) (hp : Thick S p)
    (z : UpperHalfPlane) (hz : S.project z=p) (R : ℝ) (hR : 0≤R)
    (s : Finset S.Γ) (hs : ∀η∈s,dist z (η.val z)≤R) :
    (s.card:ℝ)*diskArea (epsilon/2) ≤ diskArea (R+epsilon/2) := by
  have hd : Set.PairwiseDisjoint (s:Set S.Γ) (fun η => Metric.ball (η.val z) (epsilon/2)) := by
    intro η hη η' hη' hne
    apply Metric.ball_disjoint_ball
    have hh := deck_orbit_separated p hp z hz η η' hne
    linarith [epsilon_pos]
  have ha : 0<diskArea (epsilon/2) := diskArea_pos (by have := epsilon_pos;positivity)
  have hb : 0≤R+epsilon/2 := by have := epsilon_pos;positivity
  have hmeasure := finite_packing_card_mul_le volume s
    (fun η => Metric.ball (η.val z) (epsilon/2)) (Metric.ball z (R+epsilon/2))
    (by rw [H.plane_disk_area z _ hb];exact ENNReal.ofReal_ne_top)
    (fun _ _ => measurableSet_ball) hd
    (fun η hη => Metric.ball_subset_ball' (by rw [dist_comm];linarith [hs η hη]))
    (diskArea (epsilon/2)) ha.le
    (fun η _ => (H.plane_disk_area (η.val z) _ (by have := epsilon_pos;positivity)).ge)
  rw [H.plane_disk_area z _ hb,ENNReal.toReal_ofReal (diskArea_pos (by have := epsilon_pos;positivity)).le] at hmeasure
  exact hmeasure

lemma deck_ball_card_bound {S : QuotientSurface} {C : PrimitiveGeometry S}
    (H : PackingClassics S C) (p : S.Point) (hp : Thick S p)
    (z : UpperHalfPlane) (hz : S.project z=p) (R : ℝ) (hR : 0≤R)
    (s : Finset S.Γ) (hs : ∀η∈s,dist z (η.val z)≤R) :
    s.card ≤ Nat.ceil (diskArea (R+epsilon/2)/diskArea (epsilon/2)) := by
  have ha : 0<diskArea (epsilon/2) := diskArea_pos (by have := epsilon_pos;positivity)
  have hh := (le_div_iff₀ ha).mpr (deck_ball_card_area_bound H p hp z hz R hR s hs)
  exact_mod_cast hh.trans (Nat.le_ceil _)

end WP.Critical.PrimitivePacking
