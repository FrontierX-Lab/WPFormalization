import WPFormalization.Critical.PrimitiveCountNet
import WPFormalization.Critical.PrimitiveCountEncoding
import WPFormalization.Critical.PrimitiveCountLoops
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.PrimitivePacking
open Set MeasureTheory Finset
open WP.External.HyperbolicPacking
open scoped Classical ENNReal

lemma noncore_short_card_bound {S : QuotientSurface} (C : PrimitiveGeometry S)
    (H : PackingClassics S C) (A L : ℝ) (hA : (S.area univ).toReal≤A) (hL : 0≤L) :
    ((C.short L) \ thinCores C).card ≤ Nat.ceil (A/diskArea (epsilon/4)) *
      Nat.ceil (diskArea (L+epsilon+epsilon/2)/diskArea (epsilon/2)) := by
  obtain ⟨s,ht,hsep,hcard,hcover⟩ := thick_finite_net H A hA
  let t := (C.short L) \ thinCores C
  let loops : (p : {p // p∈s}) → Finset S.Γ := fun p =>
    (S.proper_orbit (surfaceLift S p.val) (L+epsilon)).toFinset
  have hc : ∀γ : {γ // γ∈t}, ∃p : {p // p∈s}, ∃η : S.Γ,
      BasedRep C γ.val η ∧ dist (surfaceLift S p.val) (η.val (surfaceLift S p.val))≤L+epsilon := by
    intro γ
    have hγ := mem_sdiff.mp γ.property
    obtain ⟨q,hq,hqt⟩ := H.thin_classification γ.val hγ.2
    obtain ⟨p,hp,hpq⟩ := hcover q hqt
    obtain ⟨η,hη,hd⟩ := exists_basedRep_close C γ.val p (epsilon/2)
      ⟨q,hq,by simpa [dist_comm] using hpq⟩
    refine ⟨⟨p,hp⟩,η,hη,?_⟩
    have hl := (C.mem_short L γ.val).mp hγ.1
    change (C.representative γ.val).period≤L at hl
    change dist _ _ < (C.representative γ.val).period+2*(epsilon/2) at hd
    linarith
  choose center code hbased hdist using hc
  let encode : {γ // γ∈t} → (Σp : {p // p∈s}, {η // η∈loops p}) :=
    fun γ => ⟨center γ,⟨code γ,by simpa [loops] using hdist γ⟩⟩
  have henc : Function.Injective encode := by
    intro γ γ' he
    have hcode : code γ=code γ' := congrArg (fun x : Σp : {p // p∈s}, {η // η∈loops p} => x.2.val) he
    apply Subtype.ext
    exact primitive_eq_of_basedRep C (hbased γ) (hcode ▸ hbased γ')
  have hbound := Fintype.card_le_of_injective encode henc
  have hloop : ∀p : {p // p∈s}, (loops p).card ≤
      Nat.ceil (diskArea (L+epsilon+epsilon/2)/diskArea (epsilon/2)) := by
    intro p
    apply deck_ball_card_bound H p.val (ht p.val p.property) _ (project_surfaceLift S p.val)
      (L+epsilon) (by have := epsilon_pos;positivity)
    intro η hη
    simpa [loops] using hη
  calc
    t.card ≤ Fintype.card (Σp : {p // p∈s}, {η // η∈loops p}) := by simpa using hbound
    _ = ∑p : {p // p∈s}, (loops p).card := by simp [Fintype.card_sigma]
    _ ≤ ∑_p : {p // p∈s}, Nat.ceil (diskArea (L+epsilon+epsilon/2)/diskArea (epsilon/2)) :=
      Finset.sum_le_sum (fun p _ => hloop p)
    _ = s.card * Nat.ceil (diskArea (L+epsilon+epsilon/2)/diskArea (epsilon/2)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hcard

end WP.Critical.PrimitivePacking
