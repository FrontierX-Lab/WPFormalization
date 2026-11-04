import WPFormalization.Coefficients.UnscaledLegendreDefect
import WPFormalization.Statements.UniformSaddle
/-! The actual fixed-radius tilted mass has a quadratic logarithmic lower estimate. -/
set_option autoImplicit false
noncomputable section
namespace WP.Coefficients
open Set
lemma tiltedKernelMass_fixed_radius_log_bound:
    ∃C B:ℝ,0 < C∧0 < B∧∀h m:ℕ,1 ≤ h →2*m ≤ 3*h →
      -Real.log (tiltedKernelMass (r 0) h m) ≤
        C*Real.log ((h:ℝ)+1)+B*(h:ℝ)*(3/2-(m:ℝ)/h)^2:=by
  obtain ⟨C,hC,hb⟩:=uniform_saddle
  obtain ⟨B,hB,hD⟩:=unscaled_logarithmic_legendre_defect_bound
  refine ⟨C,B,hC,hB,?_⟩
  intro h m hh hm
  have hhR:0 < (h:ℝ):=by exact_mod_cast (show 0 < h by omega)
  have hν:(m:ℝ)/h∈Icc (0:ℝ) (3/2):=by
    refine ⟨div_nonneg (Nat.cast_nonneg m) hhR.le,?_⟩
    apply (div_le_iff₀ hhR).mpr
    have H:(2:ℝ)*m ≤ 3*h:=by exact_mod_cast hm
    nlinarith only[H]
  have hs:=saddleZeta_spec ((m:ℝ)/h) hν
  have hr:0 < r 0:=r_pos 0 ⟨le_rfl,y₀_pos⟩
  have hid:=tiltedKernelMass_log_identity (r 0) hr le_rfl h m (by omega)
  have hd:=hD _ hs.1
  rw[hs.2] at hd
  have hd':(h:ℝ)*(unscaledLogPotential (r 0)-unscaledLogPotential (saddleZeta ((m:ℝ)/h))-
      ((m:ℝ)/h)*(Real.log (r 0)-Real.log (saddleZeta ((m:ℝ)/h)))) ≤
      B*(h:ℝ)*(3/2-(m:ℝ)/h)^2:=by
    convert mul_le_mul_of_nonneg_left hd hhR.le using 1 <;>ring
  have ht:-(Real.log (unscaledCoeff h m)+(h:ℝ)*Real.log (H 0 (saddleZeta ((m:ℝ)/h))).re+
      (m:ℝ)*Real.log (saddleZeta ((m:ℝ)/h))) ≤ C*Real.log ((h:ℝ)+1):=
    (neg_le_abs _).trans (hb h hh m hm)
  have hcancel:(h:ℝ)*((m:ℝ)/h)=m:=by field_simp
  dsimp[unscaledLogPotential] at hd'
  have he:(h:ℝ)*(-Real.log (H 0 (r 0)).re- -Real.log (H 0 (saddleZeta ((m:ℝ)/h))).re-
      ((m:ℝ)/h)*(Real.log (r 0)-Real.log (saddleZeta ((m:ℝ)/h))))=
      -(h:ℝ)*Real.log (H 0 (r 0)).re+(h:ℝ)*Real.log (H 0 (saddleZeta ((m:ℝ)/h))).re-
        (m:ℝ)*(Real.log (r 0)-Real.log (saddleZeta ((m:ℝ)/h))):=by
    calc
      _ = -(h:ℝ)*Real.log (H 0 (r 0)).re+(h:ℝ)*Real.log (H 0 (saddleZeta ((m:ℝ)/h))).re-
        ((h:ℝ)*((m:ℝ)/h))*(Real.log (r 0)-Real.log (saddleZeta ((m:ℝ)/h))):=by ring
      _ = _:=by rw[hcancel]
  rw[he] at hd'
  rw[hid]
  linarith only[hd',ht]
end WP.Coefficients
