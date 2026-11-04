import WPFormalization.Critical.MixedGeometricTuples
import WPFormalization.Critical.NonseparatingPointCounts
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical
open WP.External WP.RandomGeometry
open scoped Classical

abbrev ColoredSlots {ι : Type*} (a : ι→ℕ) := Σi,Fin (a i)
abbrev PantsColoredSlots {ι : Type*} (a : ι→ℕ) (color : ι→Bool) :=
  {s : ColoredSlots a // color s.1=true}
abbrev NonsepColoredSlots {ι : Type*} (a : ι→ℕ) (color : ι→Bool) :=
  {s : ColoredSlots a // ¬color s.1=true}
abbrev pantsSlotsCount {ι : Type*} [Fintype ι] (a : ι→ℕ) (color : ι→Bool) :=
  Fintype.card (PantsColoredSlots a color)
abbrev nonsepSlotsCount {ι : Type*} [Fintype ι] (a : ι→ℕ) (color : ι→Bool) :=
  Fintype.card (NonsepColoredSlots a color)

def coloredSlotsEquiv {ι : Type*} [Fintype ι] (a : ι→ℕ) (color : ι→Bool) :
    ColoredSlots a ≃ Fin (pantsSlotsCount a color+nonsepSlotsCount a color) :=
  (Equiv.sumCompl (fun s : ColoredSlots a => color s.1=true)).symm.trans
    ((Equiv.sumCongr (Fintype.equivFin (PantsColoredSlots a color))
      (Fintype.equivFin (NonsepColoredSlots a color))).trans finSumFinEquiv)

lemma coloredSlotsEquiv_pants {ι : Type*} [Fintype ι] (a : ι→ℕ) (color : ι→Bool)
    (j : Fin (pantsSlotsCount a color)) :
    color ((coloredSlotsEquiv a color).symm (j.castAdd (nonsepSlotsCount a color))).1=true := by
  simp only [coloredSlotsEquiv,Equiv.symm_trans_apply,finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_symm,Equiv.sumCongr_apply,Equiv.trans_apply,Sum.map_inl,Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin (PantsColoredSlots a color)).symm j).property

lemma coloredSlotsEquiv_nonsep {ι : Type*} [Fintype ι] (a : ι→ℕ) (color : ι→Bool)
    (j : Fin (nonsepSlotsCount a color)) :
    color ((coloredSlotsEquiv a color).symm (Fin.natAdd (pantsSlotsCount a color) j)).1=false := by
  have h : ¬color ((coloredSlotsEquiv a color).symm (Fin.natAdd (pantsSlotsCount a color) j)).1=true := by
    simp only [coloredSlotsEquiv,Equiv.symm_trans_apply,finSumFinEquiv_symm_apply_natAdd,
      Equiv.sumCongr_symm,Equiv.sumCongr_apply,Equiv.trans_apply,Sum.map_inr,Equiv.sumCompl_apply_inr]
    exact ((Fintype.equivFin (NonsepColoredSlots a color)).symm j).property
  exact Bool.eq_false_iff.mpr h
end WP.Critical
