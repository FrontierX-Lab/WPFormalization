import WPFormalization.RandomGeometry.PantsFixedOrderAsymptoticsScaledWindows
import WPFormalization.RandomGeometry.PantsMixedFactorialCount

/-! Regrouping the genuine fixed-window cut asymptotics into a finite
multiindex. Zero blocks and zero-width windows are included. -/
noncomputable section
namespace WP.RandomGeometry
open Set Filter
open scoped Topology

/-- Fixed rescaled windows repeated according to any enumeration of a finite
multiindex have the product intensity, with no extra combinatorial factor. -/
lemma pants_mixed_scaled_window_cut_tendsto {ι : Type*} [Fintype ι]
    (P : PsiTheory) (a : ι → ℕ) (R : ℕ)
    (e : (Σ j, Fin (a j)) ≃ Fin R) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : ι → ℝ) (hlo : ∀ j, 0 ≤ lo j) (horder : ∀ j, lo j ≤ hi j) :
    Tendsto (fun g => pantsFixedOrderWindowCut P g (n g) R
      (fun i => Ioc (lo (e.symm i).1/Real.sqrt (pantsScale g (n g)))
        (hi (e.symm i).1/Real.sqrt (pantsScale g (n g))))) atTop
      (𝓝 (∏ j, ((hi j)^2-(lo j)^2)^(a j))) := by
  have h := pants_fixed_scaled_Ioc_windows_of_fast_cusps P R n hnfast
    (fun i => lo (e.symm i).1) (fun i => hi (e.symm i).1)
    (fun i => hlo (e.symm i).1) (fun i => horder (e.symm i).1)
  simpa only [mixedSlots_prod a R e (fun j => (hi j)^2-(lo j)^2)] using h

/-- Canonical expanded-window version of the fixed-multiindex cut limit. -/
lemma pants_mixed_expanded_window_cut_tendsto {ι : Type*} [Fintype ι]
    (P : PsiTheory) (a : ι → ℕ) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : ι → ℝ) (hlo : ∀ j, 0 ≤ lo j) (horder : ∀ j, lo j ≤ hi j) :
    Tendsto (fun g => pantsFixedOrderWindowCut P g (n g) (∑ j, a j)
      (expandedWindows a (fun j => Ioc (lo j/Real.sqrt (pantsScale g (n g)))
        (hi j/Real.sqrt (pantsScale g (n g)))))) atTop
      (𝓝 (∏ j, ((hi j)^2-(lo j)^2)^(a j))) := by
  exact pants_mixed_scaled_window_cut_tendsto P a _ (mixedSlotsEquiv a) n
    hnfast lo hi hlo horder

end WP.RandomGeometry
