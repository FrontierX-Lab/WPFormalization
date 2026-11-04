import WPFormalization.Statements.Basic

/-! BESSEL-J0: classical zero distribution for the standard order-zero series.
NIST DLMF10.21(i), https://dlmf.nist.gov/10.21#i, states that for real nu≥-1
all zeros of J_nu are real and that there are infinitely many positive zeros.
Here nu=0, with the explicit standard J0 series already defined in Basic.
Only these mature J0 facts are deferred. The target paper's deformed kernel K_Y,
its zero enumeration, simplicity, products and compact uniform bounds are not
assumed. The bridge from deriv X to J0 is proved in Analysis/BesselZeros.
-/
noncomputable section
namespace WP.External

theorem besselJ0_zeros_real (z : ℂ) (hz : besselJ₀ z = 0) : z.im = 0 := by
  sorry

/-- Every nonzero zero of the classical order-zero Bessel function is simple.
DLMF §10.21(i), first paragraph; this assertion concerns the standard J0 series only. -/
theorem besselJ0_zero_simple (z : ℂ) (hz0 : z ≠ 0) (hz : besselJ₀ z = 0) :
    deriv besselJ₀ z ≠ 0 := by
  sorry

end WP.External
