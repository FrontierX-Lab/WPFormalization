import WPFormalization.External.MulticurveCutData
import WPFormalization.RandomGeometry.PantsLabels

/-! The actual star cut topology: a genus-g root and r two-cusp pants leaves.
Ordered curve slots and unordered cusp pairs have their original meanings. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External

def pantsCutGraph (g n r : ℕ) (f : PantsLabels n r) : MulticurveCutData n r where
  components := r+1
  genus c := if c = 0 then g else 0
  cuspVertex j := by
    classical
    exact if h : ∃ p : Fin r × Fin 2, f.val p = j then h.choose.1.succ else 0
  edgeVertex p := if p.2 = 0 then 0 else p.1.succ

lemma pantsCutGraph_root_fixed (g n r : ℕ) (f : PantsLabels n r) (hg : 0 < g)
    (v : Equiv.Perm (Fin (r+1)))
    (hv : ∀ c, (pantsCutGraph g n r f).genus (v c) = (pantsCutGraph g n r f).genus c) :
    v 0 = 0 := by
  have he := hv 0
  by_contra h
  simp only [pantsCutGraph, h, if_false, if_true] at he
  omega

lemma pantsCutGraph_flip_eq_false (g n r : ℕ) (f : PantsLabels n r) (hg : 0 < g)
    (b : Fin r → Bool) (hb : (pantsCutGraph g n r f).FlipPreserves b) :
    b = fun _ => false := by
  rcases hb with ⟨v, hv, _, he⟩
  have hv0 := pantsCutGraph_root_fixed g n r f hg v hv
  funext i
  have h := he i 0
  cases hb : b i
  · rfl
  · have heq : v (0 : Fin (r+1)) = i.succ := by
      simpa [pantsCutGraph, hb] using h
    have hz := congrArg Fin.val (hv0.symm.trans heq)
    simp at hz

/-- The exact orientation-stabilizer index is one for an ordered pants star.
No label permutation or curve-slot r! is introduced. -/
lemma pantsCutGraph_orientation_index (g n r : ℕ) (f : PantsLabels n r) (hg : 0 < g) :
    (pantsCutGraph g n r f).orientationStabilizerIndex = 1 := by
  classical
  unfold MulticurveCutData.orientationStabilizerIndex
  have hd : (pantsCutGraph g n r f).FlipPreserves (fun _ => false) := by
    refine ⟨Equiv.refl _, ?_, ?_, ?_⟩ <;> simp
  letI : Unique {b : Fin r → Bool // (pantsCutGraph g n r f).FlipPreserves b} :=
    ⟨⟨fun _ => false, hd⟩, fun b => Subtype.ext
      (pantsCutGraph_flip_eq_false g n r f hg b.val b.property)⟩
  exact Nat.card_unique

end WP.RandomGeometry
