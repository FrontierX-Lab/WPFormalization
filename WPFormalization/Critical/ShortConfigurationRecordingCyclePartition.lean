import WPFormalization.Critical.ShortConfigurationRecordingLoopLength
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.ShortConfiguration
open Set

def cyclePartitionNode (m:ℕ) (hm:0 < m) (j:ℕ) : unitInterval :=
  ⟨((min j m:ℕ):ℝ)/(m:ℝ),⟨div_nonneg (by positivity) (by positivity),
    (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.min_le_right j m)⟩⟩

lemma cyclePartitionNode_monotone (m:ℕ) (hm:0 < m) : Monotone (cyclePartitionNode m hm) := by
  intro a b hab
  change ((min a m:ℕ):ℝ)/(m:ℝ)≤((min b m:ℕ):ℝ)/(m:ℝ)
  exact div_le_div_of_nonneg_right (by exact_mod_cast min_le_min_right m hab) (by positivity)

lemma cyclePartitionNode_zero (m:ℕ) (hm:0 < m) : cyclePartitionNode m hm 0=0 := by
  apply Subtype.ext
  simp [cyclePartitionNode]

lemma cyclePartitionNode_last (m:ℕ) (hm:0 < m) : cyclePartitionNode m hm m=1 := by
  apply Subtype.ext
  simp [cyclePartitionNode,ne_of_gt hm]

def cyclePartitionSegment (m:ℕ) (hm:0 < m) (j:Fin m) (s:unitInterval) : unitInterval :=
  ⟨((j.val:ℝ)+(s:ℝ))/(m:ℝ),⟨div_nonneg (add_nonneg (Nat.cast_nonneg _) s.property.1) (by positivity),
    (div_le_one (by positivity)).mpr (by
      have hjs:(j.val:ℝ)+1≤(m:ℝ):=by exact_mod_cast j.isLt
      linarith [s.property.2])⟩⟩

lemma cyclePartitionSegment_monotone (m:ℕ) (hm:0 < m) (j:Fin m) :
    Monotone (cyclePartitionSegment m hm j) := by
  intro a b hab
  change ((j.val:ℝ)+(a:ℝ))/(m:ℝ)≤((j.val:ℝ)+(b:ℝ))/(m:ℝ)
  exact div_le_div_of_nonneg_right (by linarith [show (a:ℝ)≤(b:ℝ) from hab]) (by positivity)

lemma cyclePartitionSegment_range (m:ℕ) (hm:0 < m) (j:Fin m) :
    range (cyclePartitionSegment m hm j)=
      Icc (cyclePartitionNode m hm j.val) (cyclePartitionNode m hm (j.val+1)) := by
  have hreal:(0:ℝ) < m:=by exact_mod_cast hm
  have hmin0:min j.val m=j.val:=Nat.min_eq_left j.isLt.le
  have hmin1:min (j.val+1) m=j.val+1:=Nat.min_eq_left j.isLt
  ext t
  constructor
  · rintro ⟨s,rfl⟩
    constructor
    · change ((min j.val m:ℕ):ℝ)/(m:ℝ)≤((j.val:ℝ)+(s:ℝ))/(m:ℝ)
      rw [hmin0]
      exact div_le_div_of_nonneg_right (by linarith [s.property.1]) hreal.le
    · change ((j.val:ℝ)+(s:ℝ))/(m:ℝ)≤((min (j.val+1) m:ℕ):ℝ)/(m:ℝ)
      rw [hmin1]
      push_cast
      exact div_le_div_of_nonneg_right (by linarith [s.property.2]) hreal.le
  · intro ht
    change ((min j.val m:ℕ):ℝ)/(m:ℝ)≤(t:ℝ) ∧ (t:ℝ)≤((min (j.val+1) m:ℕ):ℝ)/(m:ℝ) at ht
    rw [hmin0,hmin1] at ht
    push_cast at ht
    have hl:(0:ℝ)≤ m*(t:ℝ)-j.val:=by have hh:=(div_le_iff₀ hreal).mp ht.1;linarith
    have hu:(m:ℝ)*(t:ℝ)-j.val≤1:=by have hh:=(le_div_iff₀ hreal).mp ht.2;linarith
    refine ⟨⟨m*(t:ℝ)-j.val,⟨hl,hu⟩⟩,?_⟩
    apply Subtype.ext
    change ((j.val:ℝ)+((m:ℝ)*(t:ℝ)-j.val))/(m:ℝ)=(t:ℝ)
    field_simp
    ring
end WP.Critical.ShortConfiguration
