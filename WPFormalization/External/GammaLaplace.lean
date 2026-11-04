import WPFormalization.External.SpecialFunctions

/-! SF-BINET: exact positive-real shifted log-Gamma Laplace formula.
This is the integrated classical consequence of NIST DLMF 5.9.12
(https://dlmf.nist.gov/5.9.E12), Frullani's logarithm integral, the fundamental
theorem for log Gamma and absolutely convergent Fubini on the finite shift
interval. It is not a verbatim DLMF formula. Parent and independent review
check the joint cancellation near zero, the positive-real domain and the
normalization. No Taylor coefficient, truncation order, Gevrey bound or WP
quantity appears in this input; those remain local proof obligations. -/
noncomputable section
namespace WP.External

/- At zero the raw totalized quotient has value zero; only its Ioi integral is
used. The genuine analytic removable germ is constructed separately. -/
@[blueprint "ext:stirling"]
def gammaLogRatioKernel (a t : ℝ) : ℝ :=
  (a-(1-Real.exp (-a*t))/(1-Real.exp (-t)))/t

@[blueprint "ext:stirling"]
theorem log_gamma_ratio_laplace (h a : ℝ) (hh : 0<h) (ha : 0<a) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-h*t)*gammaLogRatioKernel a t)
      (Set.Ioi 0) ∧
      Real.log (Real.Gamma (h+a))-Real.log (Real.Gamma h)-a*Real.log h=
        ∫ t in Set.Ioi (0:ℝ),Real.exp (-h*t)*gammaLogRatioKernel a t := by
  sorry

end WP.External
