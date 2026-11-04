import WPFormalization.RandomGeometry.GeneralPlanarRemainderRealIntegration

/-! Exhaustive finite grouping of actual nonstar orbits by (a,d), keeping
the uniform n^a cusp-label cost separate from the finitely many patterns. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory Set
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    {g n r : ℕ} {k : Fin r→ℕ}

lemma generalPlanarRemainder_sum_by_budget (hg : 1≤g)
    (f : GeneralPlanarRemainderOrbit T g n r k→ℝ) :
    (∑o : GeneralPlanarRemainderOrbit T g n r k,f o)=
      ∑a∈Finset.range ((∑i,k i)+1),∑d∈Finset.range r,
        ∑o∈Finset.univ.filter (fun o : GeneralPlanarRemainderOrbit T g n r k=>
          generalPlanarOrbitCusps T hg o.val=a ∧ generalPlanarOrbitDegree T hg o.val=d),f o := by
  classical
  let key := fun o : GeneralPlanarRemainderOrbit T g n r k=>
    (generalPlanarOrbitCusps T hg o.val,generalPlanarOrbitDegree T hg o.val)
  have hmap : ∀o∈(Finset.univ : Finset (GeneralPlanarRemainderOrbit T g n r k)),
      key o∈(Finset.range ((∑i,k i)+1)).product (Finset.range r) := by
    intro o ho
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_of_le (generalPlanarOrbit_cusps_upper T hg o.val)),
      Finset.mem_range.mpr (generalPlanarRemainder_degree_lt T hg o)⟩
  have hs := Finset.sum_fiberwise_of_maps_to hmap f
  simp only [Finset.product_eq_sprod] at hs
  have hp := Finset.sum_product (Finset.range ((∑i,k i)+1)) (Finset.range r)
    (fun p : ℕ×ℕ=>∑o∈Finset.univ.filter (fun o=>key o=p),f o)
  exact hs.symm.trans (by simpa only [key,Prod.mk.injEq] using hp)

lemma generalPlanarRemainder_fiber_card_le (hg : 1≤g) (a d : ℕ) :
    (Finset.univ.filter (fun o : GeneralPlanarRemainderOrbit T g n r k=>
      generalPlanarOrbitCusps T hg o.val=a ∧ generalPlanarOrbitDegree T hg o.val=d)).card≤
        (r+1)^(2*r)*n^a*(r+1)^a := by
  classical
  simpa only [GeneralPlanarRemainderAtBudget,Fintype.card_subtype] using
    generalPlanarRemainderAtBudget_card_le T (n:=n) (k:=k) hg a d

lemma generalPlanarRemainder_fiber_card_uniform (hg : 1≤g) (a d : ℕ) (ha : a≤∑i,k i) :
    (Finset.univ.filter (fun o : GeneralPlanarRemainderOrbit T g n r k=>
      generalPlanarOrbitCusps T hg o.val=a ∧ generalPlanarOrbitDegree T hg o.val=d)).card≤
        (r+1)^(2*r+(∑i,k i))*n^a := by
  have hp : (r+1)^a≤(r+1)^(∑i,k i) := Nat.pow_le_pow_right (by omega) ha
  calc
    _≤(r+1)^(2*r)*n^a*(r+1)^a := generalPlanarRemainder_fiber_card_le T hg a d
    _≤(r+1)^(2*r)*n^a*(r+1)^(∑i,k i) := Nat.mul_le_mul_left _ hp
    _=_ := by rw [pow_add];ring

lemma generalPlanarRemainder_fiber_empty (hg : 1≤g) (a d : ℕ) (hbad : ¬r+d≤a) :
    (Finset.univ.filter (fun o : GeneralPlanarRemainderOrbit T g n r k=>
      generalPlanarOrbitCusps T hg o.val=a ∧ generalPlanarOrbitDegree T hg o.val=d))=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro o ho
  obtain ⟨ha,hd⟩ := (Finset.mem_filter.mp ho).2
  have hh := generalPlanarOrbit_cusps_lower T hg o.val
  rw [ha,hd] at hh
  exact hbad hh

lemma generalPlanarRemainder_fiber_term_upper (hg : 2≤g) (hn : (∑i,k i)<n)
    (a d : ℕ) (ha : a≤∑i,k i) (I : Fin r→Set ℝ)
    (L : ℝ) (hL : 0≤L) (hsub : ∀i,I i⊆Icc 0 L) :
    (∑o∈Finset.univ.filter (fun o : GeneralPlanarRemainderOrbit T g n r k=>
      generalPlanarOrbitCusps T (by omega : 1≤g) o.val=a ∧
        generalPlanarOrbitDegree T (by omega : 1≤g) o.val=d),generalPlanarRemainderMomentTerm T o I)≤
      ((r+1)^(2*r+(∑i,k i)) : ℕ)*
        (Real.exp ((r:ℝ)*L)*(generalPlanarZeroVolumeCap P ((∑i,k i)+2*r))^r)*
        (if r+d≤a then (n:ℝ)^a*volumeModel P g (n-a+d)/volumeModel P g n*(L^2/2)^r else 0) := by
  classical
  by_cases hgood : r+d≤a
  · rw [if_pos hgood]
    let B : ℝ := Real.exp ((r:ℝ)*L)*(generalPlanarZeroVolumeCap P ((∑i,k i)+2*r))^r*
      (volumeModel P g (n-a+d)/volumeModel P g n)*(L^2/2)^r
    have hV := (diagonal_volume_pos_nonempty P g (n-a+d) (by omega) (by unfold Stable;omega)).le
    have hVp := (diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)).le
    have hQ := (generalPlanarZeroVolumeCap_pos P ((∑i,k i)+2*r)).le
    have hB : 0≤B := by dsimp [B];positivity
    have hterm : (∑o∈Finset.univ.filter (fun o : GeneralPlanarRemainderOrbit T g n r k=>
        generalPlanarOrbitCusps T (by omega : 1≤g) o.val=a ∧
          generalPlanarOrbitDegree T (by omega : 1≤g) o.val=d),generalPlanarRemainderMomentTerm T o I)≤
        (Finset.univ.filter (fun o : GeneralPlanarRemainderOrbit T g n r k=>
          generalPlanarOrbitCusps T (by omega : 1≤g) o.val=a ∧
            generalPlanarOrbitDegree T (by omega : 1≤g) o.val=d)).card*B := by
      calc
        _≤∑_o∈Finset.univ.filter (fun o : GeneralPlanarRemainderOrbit T g n r k=>
          generalPlanarOrbitCusps T (by omega : 1≤g) o.val=a ∧
            generalPlanarOrbitDegree T (by omega : 1≤g) o.val=d),B := by
          apply Finset.sum_le_sum
          intro o ho
          obtain ⟨hca,hde⟩ := (Finset.mem_filter.mp ho).2
          have hu := generalPlanarRemainderMomentTerm_upper T (by omega) hn o I L hL hsub
          simpa only [hca,hde,B] using hu
        _=_ := by simp [nsmul_eq_mul]
    have hc : ((Finset.univ.filter (fun o : GeneralPlanarRemainderOrbit T g n r k=>
      generalPlanarOrbitCusps T (by omega : 1≤g) o.val=a ∧
        generalPlanarOrbitDegree T (by omega : 1≤g) o.val=d)).card:ℝ)≤
          ((r+1)^(2*r+(∑i,k i)):ℕ)*(n:ℝ)^a := by
      exact_mod_cast generalPlanarRemainder_fiber_card_uniform T (n:=n) (k:=k) (by omega) a d ha
    exact hterm.trans ((mul_le_mul_of_nonneg_right hc hB).trans_eq (by dsimp [B];ring))
  · rw [generalPlanarRemainder_fiber_empty T (by omega) a d hgood,Finset.sum_empty,if_neg hgood]
    simp

end WP.RandomGeometry
