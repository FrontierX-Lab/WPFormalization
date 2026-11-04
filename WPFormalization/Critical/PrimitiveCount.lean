import WPFormalization.Critical.PrimitiveCountCount
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.PrimitivePacking
open Set MeasureTheory Finset
open WP.External.HyperbolicPacking
open scoped Classical ENNReal

def primitiveCountBound (A L : ℝ) : ℕ :=
  Nat.ceil (A/(4/Real.cosh epsilon)) + Nat.ceil (A/diskArea (epsilon/4)) *
    Nat.ceil (diskArea (max L 0+epsilon+epsilon/2)/diskArea (epsilon/2))

lemma thinCores_card_bound {S : QuotientSurface} (C : PrimitiveGeometry S)
    (H : PackingClassics S C) (A : ℝ) (hA : (S.area univ).toReal≤A) :
    (thinCores C).card ≤ Nat.ceil (A/(4/Real.cosh epsilon)) := by
  have ha : 0<4/Real.cosh epsilon := by positivity
  have hh := (le_div_iff₀ ha).mpr ((thinCores_card_area_bound C H).trans hA)
  exact_mod_cast hh.trans (Nat.le_ceil _)

lemma complete_short_card_bound {S : QuotientSurface} (C : PrimitiveGeometry S)
    (H : PackingClassics S C) (A L : ℝ) (hA : (S.area univ).toReal≤A) :
    (C.short L).card ≤ primitiveCountBound A L := by
  have hsub : C.short L ⊆ C.short (max L 0) := by
    intro γ hγ
    apply (C.mem_short _ _).mpr
    exact ((C.mem_short _ _).mp hγ).trans (le_max_left _ _)
  have hthin := thinCores_card_bound C H A hA
  have hnon := noncore_short_card_bound C H A (max L 0) hA (le_max_right _ _)
  have hsplit : (C.short (max L 0)).card ≤
      ((C.short (max L 0)) \ thinCores C).card+(thinCores C).card := card_le_card_sdiff_add_card
  have hmono := Finset.card_le_card hsub
  unfold primitiveCountBound
  omega

lemma double_area_bound (B : BorderedGeometry) (D : DoublingClassics B)
    (K : ℝ) (hK : (B.negativeEuler:ℝ)≤K) :
    (D.complete.area univ).toReal≤4*Real.pi*K := by
  have hfinite : 2*B.surface.area univ ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) B.surface.finite_area
  have hh := ENNReal.toReal_mono hfinite D.area_double
  rw [ENNReal.toReal_mul,B.gauss_bonnet,
    ENNReal.toReal_ofReal (by positivity)] at hh
  norm_num at hh
  have hπ := Real.pi_pos
  nlinarith

lemma short_card_le_double (B : BorderedGeometry) (D : DoublingClassics B) (L : ℝ) :
    (B.curves.short L).card≤(D.curves.short L).card := by
  apply Finset.card_le_card_of_injOn D.includePrimitive
  · intro γ hγ
    apply (D.curves.mem_short L _).mpr
    have he := D.length_preserved γ
    change (D.curves.representative (D.includePrimitive γ)).period=
      (B.curves.representative γ).period at he
    rw [he]
    exact (B.curves.mem_short L γ).mp hγ
  · intro γ _ γ' _ he
    exact D.primitive_injective he

/- Lemma G.2: the constant is chosen before the intrinsic finite-area surface
and its metric. Classical inputs contain only actual quotient/local geometry
and geodesic-boundary doubling, not this count or a net/loop cardinal bound. -/
@[blueprint "lem:primitive-count"]
theorem bounded_primitive_count (K L : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ B : BorderedGeometry, ∀ D : DoublingClassics B,
      0<(B.negativeEuler:ℝ) → (B.negativeEuler:ℝ)≤K →
      ((B.curves.short L).card:ℝ)≤C := by
  refine ⟨(primitiveCountBound (4*Real.pi*K) L:ℝ)+1,by positivity,?_⟩
  intro B D hpositive hK
  have hh := (short_card_le_double B D L).trans
    (complete_short_card_bound D.curves D.packing (4*Real.pi*K) L (double_area_bound B D K hK))
  exact (show ((B.curves.short L).card:ℝ)≤(primitiveCountBound (4*Real.pi*K) L:ℝ) by exact_mod_cast hh).trans (by linarith)

end WP.Critical.PrimitivePacking
