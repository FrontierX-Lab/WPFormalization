import WPFormalization.Intersection.NormalizedContinuity
/-! Actual stable admissible states at fixed complexity form a finite set.
The actual ratio, divided by any fixed degree-dependent weight, attains its
maximum jointly over those states and the closed parameter interval. The
maximizing state and parameter are certified witnesses; no supremum or
maximum existence assumption is used. This module stays independent of
Comparison so its construction applies directly to the actual clipped
weight there without a circular import. -/
noncomputable section
open Set

namespace WP

def complexityStates (h : ℕ) : Set (ℕ × List ℕ) :=
  {q | 1 ≤ q.2.length ∧ Stable q.1 q.2.length ∧
    q.2.sum ≤ dimension q.1 q.2.length ∧ complexity q.1 q.2.length = h}

lemma complexityState_bounds {h : ℕ} {q : ℕ × List ℕ} (hq : q ∈ complexityStates h) :
    q.1 ≤ h+1 ∧ q.2.length ≤ h+2 ∧ ∀ a ∈ q.2, a ≤ 4*h+2 := by
  obtain ⟨hn,hs,hd,he⟩ := hq
  have hraw : 2*q.1+q.2.length = h+2 := by
    unfold complexity at he
    unfold Stable at hs
    omega
  have hg : q.1 ≤ h+1 := by omega
  have hlen : q.2.length ≤ h+2 := by omega
  refine ⟨hg,hlen,?_⟩
  intro a ha
  have hle : a ≤ q.2.sum := List.le_sum_of_mem ha
  unfold dimension at hd
  omega

lemma complexityStates_finite (h : ℕ) : (complexityStates h).Finite := by
  let Code := Σ g : Fin (h+2), Σ p : Fin (h+3), Fin p.val → Fin (4*h+3)
  let decode : Code → ℕ × List ℕ := fun c =>
    (c.1.val,List.ofFn (fun i => (c.2.2 i).val))
  have hf : (Set.range decode).Finite := Set.finite_range decode
  apply hf.subset
  intro q hq
  obtain ⟨hg,hlen,hm⟩ := complexityState_bounds hq
  let gs : Fin (h+2) := ⟨q.1,by omega⟩
  let ps : Fin (h+3) := ⟨q.2.length,by omega⟩
  let v : Fin ps.val → Fin (4*h+3) := fun i =>
    ⟨q.2[i.val],by have := hm _ (List.getElem_mem (l:=q.2) (n:=i.val) i.isLt);omega⟩
  refine ⟨⟨gs,ps,v⟩,?_⟩
  dsimp only [decode,gs,ps,v]
  congr 1
  exact List.ofFn_getElem

lemma complexityStates_zero : complexityStates 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨hn,hs,hd,he⟩ := hq
  unfold complexity at he
  unfold Stable at hs
  omega

lemma complexityStates_nonempty (h : ℕ) (hh : 1 ≤ h) : (complexityStates h).Nonempty := by
  refine ⟨(0,List.replicate (h+2) 0),?_⟩
  dsimp only [complexityStates]
  simp only [Set.mem_ofPred_eq,List.length_replicate,List.sum_replicate]
  constructor
  · omega
  constructor
  · unfold Stable;omega
  constructor
  · exact Nat.zero_le _
  · unfold complexity;omega

lemma ratio_weight_fixed_attains_max (P : PsiTheory) (w : List ℕ → ℝ)
    (q : ℕ × List ℕ) (hs : Stable q.1 q.2.length) :
    ∃ Ymax : Icc (0:ℝ) y₀, ∀ Y : Icc (0:ℝ) y₀,
      ratio P q.1 q.2 Y / w q.2 ≤ ratio P q.1 q.2 Ymax / w q.2 := by
  have hne : (Set.univ : Set (Icc (0:ℝ) y₀)).Nonempty :=
    ⟨⟨0,le_rfl,y₀_pos.le⟩,Set.mem_univ _⟩
  have hc := (ratio_continuous P q.1 q.2 hs).div_const (w q.2)
  obtain ⟨Ymax,hYmax,hm⟩ := isCompact_univ.exists_isMaxOn hne hc.continuousOn
  exact ⟨Ymax,fun Y => hm (Set.mem_univ Y)⟩

lemma ratio_weight_complexity_attains_max (P : PsiTheory) (w : List ℕ → ℝ)
    (h : ℕ) (hh : 1 ≤ h) :
    ∃ q ∈ complexityStates h, ∃ Ymax : Icc (0:ℝ) y₀,
      ∀ q' ∈ complexityStates h, ∀ Y : Icc (0:ℝ) y₀,
        ratio P q'.1 q'.2 Y / w q'.2 ≤ ratio P q.1 q.2 Ymax / w q.2 := by
  classical
  let State := {q : ℕ × List ℕ // q ∈ complexityStates h}
  haveI : Finite State := (complexityStates_finite h).to_subtype
  letI : Fintype State := Fintype.ofFinite State
  haveI : Nonempty State := by
    obtain ⟨q,hq⟩ := complexityStates_nonempty h hh
    exact ⟨⟨q,hq⟩⟩
  have hy : ∀ q : State, ∃ Ymax : Icc (0:ℝ) y₀, ∀ Y : Icc (0:ℝ) y₀,
      ratio P q.val.1 q.val.2 Y / w q.val.2 ≤ ratio P q.val.1 q.val.2 Ymax / w q.val.2 :=
    fun q => ratio_weight_fixed_attains_max P w q.val q.property.2.1
  choose ymax hymax using hy
  obtain ⟨q,hq,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun q : State => ratio P q.val.1 q.val.2 (ymax q) / w q.val.2) Finset.univ_nonempty
  refine ⟨q.val,q.property,ymax q,?_⟩
  intro q' hq' Y
  exact (hymax (⟨q',hq'⟩:State) Y).trans (hmax _ (Finset.mem_univ _))
end WP

namespace WP
structure RatioComplexityMaximizer (P : PsiTheory) (w : List ℕ → ℝ) (h : ℕ) where
  state : ℕ × List ℕ
  valid : state ∈ complexityStates h
  parameter : Icc (0:ℝ) y₀
  bounds : ∀ q ∈ complexityStates h, ∀ Y : Icc (0:ℝ) y₀,
    ratio P q.1 q.2 Y / w q.2 ≤ ratio P state.1 state.2 parameter / w state.2

noncomputable def ratioComplexityMaximizer (P : PsiTheory) (w : List ℕ → ℝ)
    (h : ℕ) (hh : 1 ≤ h) : RatioComplexityMaximizer P w h :=
  Classical.choice (by
    obtain ⟨q,hq,Ymax,hm⟩ := ratio_weight_complexity_attains_max P w h hh
    exact ⟨⟨q,hq,Ymax,hm⟩⟩)

noncomputable def ratioComplexityMaximum (P : PsiTheory) (w : List ℕ → ℝ)
    (h : ℕ) : ℝ :=
  if hh : 1 ≤ h then
    let M := ratioComplexityMaximizer P w h hh
    ratio P M.state.1 M.state.2 M.parameter / w M.state.2
  else 0

lemma ratioComplexityMaximum_zero (P : PsiTheory) (w : List ℕ → ℝ) :
    ratioComplexityMaximum P w 0 = 0 := by simp [ratioComplexityMaximum]

lemma ratioComplexityMaximum_attained (P : PsiTheory) (w : List ℕ → ℝ)
    (h : ℕ) (hh : 1 ≤ h) :
    ∃ q ∈ complexityStates h, ∃ Ymax : Icc (0:ℝ) y₀,
      ratioComplexityMaximum P w h = ratio P q.1 q.2 Ymax / w q.2 := by
  let M := ratioComplexityMaximizer P w h hh
  refine ⟨M.state,M.valid,M.parameter,?_⟩
  simp only [ratioComplexityMaximum,dite_eq_left hh]
  rfl

lemma ratioComplexityMaximum_bounds (P : PsiTheory) (w : List ℕ → ℝ)
    (h : ℕ) (q : ℕ × List ℕ) (hq : q ∈ complexityStates h)
    (Y : Icc (0:ℝ) y₀) :
    ratio P q.1 q.2 Y / w q.2 ≤ ratioComplexityMaximum P w h := by
  have hh : 1 ≤ h := by
    obtain ⟨hn,hs,hd,he⟩ := hq
    unfold complexity at he
    unfold Stable at hs
    omega
  simp only [ratioComplexityMaximum,dite_eq_left hh]
  exact (ratioComplexityMaximizer P w h hh).bounds q hq Y

lemma ratio_le_complexityMaximum_mul (P : PsiTheory) (w : List ℕ → ℝ)
    (h : ℕ) (q : ℕ × List ℕ) (hq : q ∈ complexityStates h)
    (Y : Icc (0:ℝ) y₀) (hw : 0 < w q.2) :
    ratio P q.1 q.2 Y ≤ ratioComplexityMaximum P w h * w q.2 :=
  (div_le_iff₀ hw).mp (ratioComplexityMaximum_bounds P w h q hq Y)
end WP
