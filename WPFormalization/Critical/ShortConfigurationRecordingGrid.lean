import Mathlib
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.ShortConfiguration
open Set
open scoped Classical

/- Elementary grid packing used to derive the local-intersection bound from
Basmajian's two-segment inequality. No intersection cardinal bound is assumed. -/
lemma abs_sub_lt_of_floor_div_eq {a x y : ℝ} (ha : 0<a) (hx : 0≤x) (hy : 0≤y)
    (he : Nat.floor (x/a)=Nat.floor (y/a)) : |x-y|<a := by
  have hxl := Nat.floor_le (div_nonneg hx ha.le)
  have hxu := Nat.lt_floor_add_one (x/a)
  have hyl := Nat.floor_le (div_nonneg hy ha.le)
  have hyu := Nat.lt_floor_add_one (y/a)
  rw [he] at hxl hxu
  have h1 : x/a-y/a<1 := by linarith
  have h2 : y/a-x/a<1 := by linarith
  apply abs_lt.mpr
  constructor
  · have hh := (div_lt_iff₀ ha).mp (show (y-x)/a<1 by convert h2 using 1 <;>ring)
    linarith
  · have hh := (div_lt_iff₀ ha).mp (show (x-y)/a<1 by convert h1 using 1 <;>ring)
    linarith

lemma grid_code_injective (a L : ℝ) (ha : 0<a) (E : Set (ℝ×ℝ))
    (hbox : ∀p∈E, p.1∈Icc 0 L ∧ p.2∈Icc 0 L)
    (hsep : ∀p∈E,∀q∈E,p≠q→2*a≤|p.1-q.1|+|p.2-q.2|) :
    Function.Injective (fun p : E => (Nat.floor (p.val.1/a),Nat.floor (p.val.2/a))) := by
  intro p q he
  by_contra hne
  have hh := hsep p.val p.property q.val q.property (fun he=>hne (Subtype.ext he))
  have h1 := abs_sub_lt_of_floor_div_eq ha (hbox p.val p.property).1.1
    (hbox q.val q.property).1.1 (congrArg Prod.fst he)
  have h2 := abs_sub_lt_of_floor_div_eq ha (hbox p.val p.property).2.1
    (hbox q.val q.property).2.1 (congrArg Prod.snd he)
  linarith

lemma grid_finite_card_bound (a L : ℝ) (ha : 0<a) (E : Set (ℝ×ℝ))
    (hbox : ∀p∈E, p.1∈Icc 0 L ∧ p.2∈Icc 0 L)
    (hsep : ∀p∈E,∀q∈E,p≠q→2*a≤|p.1-q.1|+|p.2-q.2|) :
    E.Finite ∧ Nat.card E≤(Nat.floor (L/a)+1)^2 := by
  let code : E→Fin (Nat.floor (L/a)+1)×Fin (Nat.floor (L/a)+1) := fun p=>
    (⟨Nat.floor (p.val.1/a),by
      have hh := Nat.floor_mono ((div_le_div_iff_of_pos_right ha).mpr (hbox p.val p.property).1.2)
      omega⟩,⟨Nat.floor (p.val.2/a),by
      have hh := Nat.floor_mono ((div_le_div_iff_of_pos_right ha).mpr (hbox p.val p.property).2.2)
      omega⟩)
  have hi : Function.Injective code := by
    intro p q he
    apply grid_code_injective a L ha E hbox hsep
    exact congrArg (fun p : Fin (Nat.floor (L/a)+1)×Fin (Nat.floor (L/a)+1)=>(p.1.val,p.2.val)) he
  haveI : Finite E := Finite.of_injective code hi
  refine ⟨Set.toFinite E,?_⟩
  have hh := Nat.card_le_card_of_injective code hi
  simpa [Nat.card_prod,Nat.card_fin,pow_two] using hh

end WP.Critical.ShortConfiguration
