import Mathlib
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.ShortConfiguration
open Set Finset
open scoped Classical

def subdivisionStart (s : Finset ℝ) (j : Fin s.card) : ℝ := s.orderEmbOfFin rfl j

def subdivisionEnd (ell : ℝ) (s : Finset ℝ) (j : Fin s.card) : ℝ :=
  if hj : j.val+1<s.card then s.orderEmbOfFin rfl ⟨j.val+1,hj⟩ else ell

lemma subdivision_start_mem (s : Finset ℝ) (j : Fin s.card) : subdivisionStart s j∈s :=
  s.orderEmbOfFin_mem rfl j

lemma subdivision_start_lt_end (ell : ℝ) (s : Finset ℝ)
    (hs : ∀t∈s,t<ell) (j : Fin s.card) : subdivisionStart s j<subdivisionEnd ell s j := by
  unfold subdivisionEnd
  split_ifs with hj
  · exact (s.orderEmbOfFin rfl).strictMono (by change j.val<j.val+1;omega)
  · exact hs _ (subdivision_start_mem s j)

lemma subdivision_end_le_of_lt (ell : ℝ) (s : Finset ℝ) {j k : Fin s.card} (hjk : j<k) :
    subdivisionEnd ell s j≤ subdivisionStart s k := by
  have hj : j.val+1<s.card := by have := k.isLt;change j.val<k.val at hjk;omega
  simp only [subdivisionEnd,dif_pos hj,subdivisionStart]
  exact (s.orderEmbOfFin rfl).monotone (by change j.val+1≤k.val;exact hjk)

lemma subdivision_no_breakpoint_inside (ell : ℝ) (s : Finset ℝ)
    (j : Fin s.card) {t : ℝ} (ht : t∈s) : t∉Ioo (subdivisionStart s j) (subdivisionEnd ell s j) := by
  let k : Fin s.card := (s.orderIsoOfFin rfl).symm ⟨t,ht⟩
  have hk : subdivisionStart s k=t := congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨t,ht⟩)
  intro h
  have hjk : j<k := by
    by_contra hnot
    have hh : subdivisionStart s k≤ subdivisionStart s j := (s.orderEmbOfFin rfl).monotone (le_of_not_gt hnot)
    rw [hk] at hh
    linarith [h.1]
  have hle := subdivision_end_le_of_lt ell s hjk
  rw [hk] at hle
  linarith [h.2]

lemma subdivision_covers (ell : ℝ) (s : Finset ℝ) (hzero : 0∈s)
    {t : ℝ} (ht : t∈Ico 0 ell) :
    ∃j:Fin s.card,t∈Ico (subdivisionStart s j) (subdivisionEnd ell s j) := by
  let p := s.filter (fun a=>a≤t)
  have hne : p.Nonempty := ⟨0,mem_filter.mpr ⟨hzero,ht.1⟩⟩
  let a := p.max' hne
  have ha : a∈s ∧ a≤t := mem_filter.mp (max'_mem p hne)
  let j := (s.orderIsoOfFin rfl).symm ⟨a,ha.1⟩
  have hj : subdivisionStart s j=a := congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨a,ha.1⟩)
  refine ⟨j,by simpa [hj] using ha.2,?_⟩
  unfold subdivisionEnd
  split_ifs with hnext
  · by_contra hbad
    have hle : s.orderEmbOfFin rfl ⟨j.val+1,hnext⟩≤t := le_of_not_gt hbad
    have hm : s.orderEmbOfFin rfl ⟨j.val+1,hnext⟩∈p := mem_filter.mpr
      ⟨s.orderEmbOfFin_mem rfl _,hle⟩
    have hh := le_max' p _ hm
    have hh' : subdivisionStart s j<s.orderEmbOfFin rfl ⟨j.val+1,hnext⟩ :=
      (s.orderEmbOfFin rfl).strictMono (by change j.val<j.val+1;omega)
    rw [hj] at hh'
    exact (not_lt_of_ge hh) hh'
  · exact ht.2

lemma subdivision_interval_unique (ell : ℝ) (s : Finset ℝ) {t : ℝ} {j k : Fin s.card}
    (hj : t∈Ico (subdivisionStart s j) (subdivisionEnd ell s j))
    (hk : t∈Ico (subdivisionStart s k) (subdivisionEnd ell s k)) : j=k := by
  rcases lt_trichotomy j k with h|h|h
  · have hh := subdivision_end_le_of_lt ell s h
    linarith [hj.2,hk.1]
  · exact h
  · have hh := subdivision_end_le_of_lt ell s h
    linarith [hk.2,hj.1]

end WP.Critical.ShortConfiguration
