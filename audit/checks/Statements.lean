import WPFormalization.Statements

-- Task2: every linked declaration is resolved by Lean; inspect explicit PsiTheory binders too.
#check WP.A
#print axioms WP.A
#check WP.Analysis.instanton_contour_coefficient_dictionary
#print axioms WP.Analysis.instanton_contour_coefficient_dictionary
#check WP.Analysis.jt_critical_action
#print axioms WP.Analysis.jt_critical_action
#check WP.BoltzmannWp.tight_boltzmann
#print axioms WP.BoltzmannWp.tight_boltzmann
#check WP.Coefficients.instanton_correspondence
#print axioms WP.Coefficients.instanton_correspondence
#check WP.Critical.PantsCluster.critical_cluster_overdispersion
#print axioms WP.Critical.PantsCluster.critical_cluster_overdispersion
#check WP.Critical.PantsCluster.critical_primitive_length_spectrum
#print axioms WP.Critical.PantsCluster.critical_primitive_length_spectrum
#check WP.Critical.PrimitivePacking.bounded_primitive_count
#print axioms WP.Critical.PrimitivePacking.bounded_primitive_count
#check WP.Critical.ShortConfiguration.activeSupport_negativeEuler_le
#print axioms WP.Critical.ShortConfiguration.activeSupport_negativeEuler_le
#check WP.Critical.ShortConfiguration.actual_cluster_selected_indices
#print axioms WP.Critical.ShortConfiguration.actual_cluster_selected_indices
#check WP.Critical.ShortConfiguration.cut_masked_selected_curve_count_le
#print axioms WP.Critical.ShortConfiguration.cut_masked_selected_curve_count_le
#check WP.Critical.ShortConfiguration.exists_actual_intersecting_masked_record
#print axioms WP.Critical.ShortConfiguration.exists_actual_intersecting_masked_record
#check WP.Critical.ShortConfiguration.exists_actual_short_simple_tuple_cut
#print axioms WP.Critical.ShortConfiguration.exists_actual_short_simple_tuple_cut
#check WP.Critical.ShortConfiguration.exists_actual_single_nonpants_masked_record
#print axioms WP.Critical.ShortConfiguration.exists_actual_single_nonpants_masked_record
#check WP.Critical.ShortConfiguration.masked_tuple_recording_fiber_card_le
#print axioms WP.Critical.ShortConfiguration.masked_tuple_recording_fiber_card_le
#check WP.Critical.ShortConfiguration.supporting_piece_boundaryLength_le
#print axioms WP.Critical.ShortConfiguration.supporting_piece_boundaryLength_le
#check WP.Critical.complex_short_configurations
#print axioms WP.Critical.complex_short_configurations
#check WP.Critical.critical_cut_estimate
#print axioms WP.Critical.critical_cut_estimate
#check WP.Critical.critical_cut_estimate_regime
#print axioms WP.Critical.critical_cut_estimate_regime
#check WP.Critical.critical_cut_expectation_regime
#print axioms WP.Critical.critical_cut_expectation_regime
#check WP.Critical.critical_cut_marked_estimate
#print axioms WP.Critical.critical_cut_marked_estimate
#check WP.Critical.critical_cut_marked_estimate_regime
#print axioms WP.Critical.critical_cut_marked_estimate_regime
#check WP.Critical.critical_cut_marked_expectation_regime
#print axioms WP.Critical.critical_cut_marked_expectation_regime
#check WP.Critical.critical_unordered_cut_estimate
#print axioms WP.Critical.critical_unordered_cut_estimate
#check WP.Critical.critical_unordered_cut_estimate_regime
#print axioms WP.Critical.critical_unordered_cut_estimate_regime
#check WP.Critical.critical_unordered_cut_marked_estimate
#print axioms WP.Critical.critical_unordered_cut_marked_estimate
#check WP.Critical.critical_unordered_cut_marked_estimate_regime
#print axioms WP.Critical.critical_unordered_cut_marked_estimate_regime
#check WP.Critical.joint_nonseparating_pants_poisson_limit
#print axioms WP.Critical.joint_nonseparating_pants_poisson_limit
#check WP.Delta
#print axioms WP.Delta
#check WP.External.BuddLionsTightGeometry
#print axioms WP.External.BuddLionsTightGeometry
#check WP.External.BuddLionsTightIntegration
#print axioms WP.External.BuddLionsTightIntegration
#check WP.External.BuddZonneveldTransform
#print axioms WP.External.BuddZonneveldTransform
#check WP.External.CollarGeometry
#print axioms WP.External.CollarGeometry
#check WP.External.DMClasses
#print axioms WP.External.DMClasses
#check WP.External.HigherKappaRealization
#print axioms WP.External.HigherKappaRealization
#check WP.External.IntersectionRealization
#print axioms WP.External.IntersectionRealization
#check WP.External.MirzakhaniIntegration
#print axioms WP.External.MirzakhaniIntegration
#check WP.External.PainleveAnalytic.CCHData
#print axioms WP.External.PainleveAnalytic.CCHData
#check WP.External.PainleveAnalytic.GIKMData
#print axioms WP.External.PainleveAnalytic.GIKMData
#check WP.External.PainleveAnalytic.exists_cch_data
#print axioms WP.External.PainleveAnalytic.exists_cch_data
#check WP.External.PainleveAnalytic.exists_gikm_data
#print axioms WP.External.PainleveAnalytic.exists_gikm_data
#check WP.External.ShenWuPantsBound
#print axioms WP.External.ShenWuPantsBound
#check WP.External.ShortFillingGeometry.SingleCurvePieceClassics
#print axioms WP.External.ShortFillingGeometry.SingleCurvePieceClassics
#check WP.External.ShortFullFillingGeometry.FullSingleCurveFillingClassics
#print axioms WP.External.ShortFullFillingGeometry.FullSingleCurveFillingClassics
#check WP.External.SpectralGeometry
#print axioms WP.External.SpectralGeometry
#check WP.External.WeilPeterssonGeometry
#print axioms WP.External.WeilPeterssonGeometry
#check WP.External.classical_onepoint_nef_realization
#print axioms WP.External.classical_onepoint_nef_realization
#check WP.External.first_kdv_descendants
#print axioms WP.External.first_kdv_descendants
#check WP.External.fixed_genus_normalized_volume_logarithm
#print axioms WP.External.fixed_genus_normalized_volume_logarithm
#check WP.External.gammaLogRatioKernel
#print axioms WP.External.gammaLogRatioKernel
#check WP.External.gammaStirlingMain
#print axioms WP.External.gammaStirlingMain
#check WP.External.gamma_finite_product
#print axioms WP.External.gamma_finite_product
#check WP.External.gamma_ratio_error
#print axioms WP.External.gamma_ratio_error
#check WP.External.gamma_ratio_first_correction_error
#print axioms WP.External.gamma_ratio_first_correction_error
#check WP.External.gamma_stirling_error
#print axioms WP.External.gamma_stirling_error
#check WP.External.gaussian_integral
#print axioms WP.External.gaussian_integral
#check WP.External.geometricBracket
#print axioms WP.External.geometricBracket
#check WP.External.integrated_first_kdv
#print axioms WP.External.integrated_first_kdv
#check WP.External.itzykson_zuber
#print axioms WP.External.itzykson_zuber
#check WP.External.logStirlingPartial
#print axioms WP.External.logStirlingPartial
#check WP.External.log_gamma_ratio_laplace
#print axioms WP.External.log_gamma_ratio_laplace
#check WP.External.log_gamma_stirling_remainder
#print axioms WP.External.log_gamma_stirling_remainder
#check WP.External.mixedIntegral
#print axioms WP.External.mixedIntegral
#check WP.External.normalizedZeroInstanton
#print axioms WP.External.normalizedZeroInstanton
#check WP.External.painleveAction
#print axioms WP.External.painleveAction
#check WP.External.painleve_first_correction_error
#print axioms WP.External.painleve_first_correction_error
#check WP.External.painleve_leading
#print axioms WP.External.painleve_leading
#check WP.External.painleve_leading_error
#print axioms WP.External.painleve_leading_error
#check WP.External.phiCoefficient
#print axioms WP.External.phiCoefficient
#check WP.External.shenWu_volume_critical_lower
#print axioms WP.External.shenWu_volume_critical_lower
#check WP.External.shenWu_volume_upper
#print axioms WP.External.shenWu_volume_upper
#check WP.External.stokesAmplitude
#print axioms WP.External.stokesAmplitude
#check WP.External.wpVolume
#print axioms WP.External.wpVolume
#check WP.H
#print axioms WP.H
#check WP.HigherOrder.absoluteCoefficient
#print axioms WP.HigherOrder.absoluteCoefficient
#check WP.HigherOrder.canonicalUnmarkedSeries
#print axioms WP.HigherOrder.canonicalUnmarkedSeries
#check WP.HigherOrder.canonical_expansion
#print axioms WP.HigherOrder.canonical_expansion
#check WP.HigherOrder.criticalExtractedCoefficient
#print axioms WP.HigherOrder.criticalExtractedCoefficient
#check WP.HigherOrder.endpointInsertionFactor
#print axioms WP.HigherOrder.endpointInsertionFactor
#check WP.HigherOrder.exactEndpoint
#print axioms WP.HigherOrder.exactEndpoint
#check WP.HigherOrder.exactEndpoint_formula
#print axioms WP.HigherOrder.exactEndpoint_formula
#check WP.HigherOrder.extractedCoefficient
#print axioms WP.HigherOrder.extractedCoefficient
#check WP.HigherOrder.extractionDenominator
#print axioms WP.HigherOrder.extractionDenominator
#check WP.HigherOrder.extractionNumerator
#print axioms WP.HigherOrder.extractionNumerator
#check WP.HigherOrder.extraction_large_indices
#print axioms WP.HigherOrder.extraction_large_indices
#check WP.HigherOrder.extraction_small_indices
#print axioms WP.HigherOrder.extraction_small_indices
#check WP.HigherOrder.firstEndpointConstant
#print axioms WP.HigherOrder.firstEndpointConstant
#check WP.HigherOrder.firstMarkedCorrection
#print axioms WP.HigherOrder.firstMarkedCorrection
#check WP.HigherOrder.first_correction
#print axioms WP.HigherOrder.first_correction
#check WP.HigherOrder.first_extracted_correction
#print axioms WP.HigherOrder.first_extracted_correction
#check WP.HigherOrder.first_extracted_correction_critical
#print axioms WP.HigherOrder.first_extracted_correction_critical
#check WP.HigherOrder.formalCusp
#print axioms WP.HigherOrder.formalCusp
#check WP.HigherOrder.formalGenus
#print axioms WP.HigherOrder.formalGenus
#check WP.HigherOrder.formalProfile
#print axioms WP.HigherOrder.formalProfile
#check WP.HigherOrder.full_expansion
#print axioms WP.HigherOrder.full_expansion
#check WP.HigherOrder.intro_absolute
#print axioms WP.HigherOrder.intro_absolute
#check WP.HigherOrder.local_comparison
#print axioms WP.HigherOrder.local_comparison
#check WP.HigherOrder.rawExtractedCoefficient
#print axioms WP.HigherOrder.rawExtractedCoefficient
#check WP.HigherOrder.secondIncrement
#print axioms WP.HigherOrder.secondIncrement
#check WP.HigherOrder.secondProfile
#print axioms WP.HigherOrder.secondProfile
#check WP.HigherOrder.second_profile_path_independent
#print axioms WP.HigherOrder.second_profile_path_independent
#check WP.HigherOrder.unmarkedCoefficient
#print axioms WP.HigherOrder.unmarkedCoefficient
#check WP.HigherOrder.unmarked_first_exact
#print axioms WP.HigherOrder.unmarked_first_exact
#check WP.JT.jt_abel_critical_edge
#print axioms WP.JT.jt_abel_critical_edge
#check WP.JT.string_normalization
#print axioms WP.JT.string_normalization
#check WP.K
#print axioms WP.K
#check WP.Phi
#print axioms WP.Phi
#check WP.PivotChoice
#print axioms WP.PivotChoice
#check WP.Probability.bounded_optional_stopping
#print axioms WP.Probability.bounded_optional_stopping
#check WP.PsiTheory
#print axioms WP.PsiTheory
#check WP.RandomGeometry.pants_ordered_window_moments
#print axioms WP.RandomGeometry.pants_ordered_window_moments
#check WP.RandomGeometry.pants_poisson_theorem
#print axioms WP.RandomGeometry.pants_poisson_theorem
#check WP.RandomGeometry.short_pants_concentration
#print axioms WP.RandomGeometry.short_pants_concentration
#check WP.Spectral.many_small_eigenvalues
#print axioms WP.Spectral.many_small_eigenvalues
#check WP.Spectral.vanishing_spectral_gap
#print axioms WP.Spectral.vanishing_spectral_gap
#check WP.Stable
#print axioms WP.Stable
#check WP.T
#print axioms WP.T
#check WP.Theta
#print axioms WP.Theta
#check WP.Tight.tight_length_spectrum
#print axioms WP.Tight.tight_length_spectrum
#check WP.TightConnected.tight_connected
#print axioms WP.TightConnected.tight_connected
#check WP.TightConnected.tight_connected_original_bounded
#print axioms WP.TightConnected.tight_connected_original_bounded
#check WP.TightConnected.tight_connected_original_bounded_scale
#print axioms WP.TightConnected.tight_connected_original_bounded_scale
#check WP.TightConnected.tight_connected_original_saddle
#print axioms WP.TightConnected.tight_connected_original_saddle
#check WP.TightConnected.tight_connected_original_scale
#print axioms WP.TightConnected.tight_connected_original_scale
#check WP.TightSeparating.actual_tight_separating_expectation_uniform
#print axioms WP.TightSeparating.actual_tight_separating_expectation_uniform
#check WP.TightSeparating.actual_tight_separating_lintegral_uniform
#print axioms WP.TightSeparating.actual_tight_separating_lintegral_uniform
#check WP.W
#print axioms WP.W
#check WP.X
#print axioms WP.X
#check WP.XR
#print axioms WP.XR
#check WP.Xdiv
#print axioms WP.Xdiv
#check WP.Z
#print axioms WP.Z
#check WP.a
#print axioms WP.a
#check WP.absolute_prefactor
#print axioms WP.absolute_prefactor
#check WP.absolute_volume
#print axioms WP.absolute_volume
#check WP.action
#print axioms WP.action
#check WP.adjacent_endpoint_limits
#print axioms WP.adjacent_endpoint_limits
#check WP.adjacent_limit
#print axioms WP.adjacent_limit
#check WP.analytic_majorant
#print axioms WP.analytic_majorant
#check WP.analytic_phase_change
#print axioms WP.analytic_phase_change
#check WP.backgroundDegrees
#print axioms WP.backgroundDegrees
#check WP.backgrounds
#print axioms WP.backgrounds
#check WP.barH
#print axioms WP.barH
#check WP.barK
#print axioms WP.barK
#check WP.besselJ₀
#print axioms WP.besselJ₀
#check WP.besselJ₁
#print axioms WP.besselJ₁
#check WP.bessel_branches
#print axioms WP.bessel_branches
#check WP.bessel_dictionary
#print axioms WP.bessel_dictionary
#check WP.bottom_log_bound
#print axioms WP.bottom_log_bound
#check WP.boundaryA
#print axioms WP.boundaryA
#check WP.boundaryFactor
#print axioms WP.boundaryFactor
#check WP.boundaryVolumeModel
#print axioms WP.boundaryVolumeModel
#check WP.boundary_factor_endpoints
#print axioms WP.boundary_factor_endpoints
#check WP.bounded_boundaries
#print axioms WP.bounded_boundaries
#check WP.bracketB
#print axioms WP.bracketB
#check WP.bracket_differences
#print axioms WP.bracket_differences
#check WP.centralCoefficient
#print axioms WP.centralCoefficient
#check WP.chainProfile
#print axioms WP.chainProfile
#check WP.clippedWeight
#print axioms WP.clippedWeight
#check WP.coefficient_bounds
#print axioms WP.coefficient_bounds
#check WP.comparison_lower
#print axioms WP.comparison_lower
#check WP.comparison_upper
#print axioms WP.comparison_upper
#check WP.complexity
#print axioms WP.complexity
#check WP.convolutionR
#print axioms WP.convolutionR
#check WP.criticalIntensity
#print axioms WP.criticalIntensity
#check WP.criticalIntensityDensity
#print axioms WP.criticalIntensityDensity
#check WP.critical_kernel_limits
#print axioms WP.critical_kernel_limits
#check WP.critical_kernels
#print axioms WP.critical_kernels
#check WP.cuspCorrection
#print axioms WP.cuspCorrection
#check WP.cuspMass
#print axioms WP.cuspMass
#check WP.cusp_local_limit
#print axioms WP.cusp_local_limit
#check WP.deficit
#print axioms WP.deficit
#check WP.degreeCorrection
#print axioms WP.degreeCorrection
#check WP.density
#print axioms WP.density
#check WP.diagonal_chain
#print axioms WP.diagonal_chain
#check WP.dilatonCoeff
#print axioms WP.dilatonCoeff
#check WP.dilaton_coefficient
#print axioms WP.dilaton_coefficient
#check WP.dimension
#print axioms WP.dimension
#check WP.endpoint_pure_limit
#print axioms WP.endpoint_pure_limit
#check WP.endpoint_ratio
#print axioms WP.endpoint_ratio
#check WP.endpoint_string
#print axioms WP.endpoint_string
#check WP.extractionB
#print axioms WP.extractionB
#check WP.extractionQ
#print axioms WP.extractionQ
#check WP.extractionS
#print axioms WP.extractionS
#check WP.extraction_factorization
#print axioms WP.extraction_factorization
#check WP.firstJ₀Zero
#print axioms WP.firstJ₀Zero
#check WP.first_degree
#print axioms WP.first_degree
#check WP.first_degree_all_degrees
#print axioms WP.first_degree_all_degrees
#check WP.formalFixedPoint
#print axioms WP.formalFixedPoint
#check WP.genusCorrection
#print axioms WP.genusCorrection
#check WP.growing_boundary_factor
#print axioms WP.growing_boundary_factor
#check WP.growing_marking_first_order
#print axioms WP.growing_marking_first_order
#check WP.harmonicCoeff
#print axioms WP.harmonicCoeff
#check WP.harmonicMass
#print axioms WP.harmonicMass
#check WP.harmonicPGF
#print axioms WP.harmonicPGF
#check WP.harmonicVariance
#print axioms WP.harmonicVariance
#check WP.harmonic_comparison
#print axioms WP.harmonic_comparison
#check WP.harmonic_law
#print axioms WP.harmonic_law
#check WP.harmonic_local_limit
#print axioms WP.harmonic_local_limit
#check WP.inactive
#print axioms WP.inactive
#check WP.initial_amplitudes
#print axioms WP.initial_amplitudes
#check WP.inverseY
#print axioms WP.inverseY
#check WP.kernel_action_moments
#print axioms WP.kernel_action_moments
#check WP.kernel_differential
#print axioms WP.kernel_differential
#check WP.kernel_positivity
#print axioms WP.kernel_positivity
#check WP.kernel_series
#print axioms WP.kernel_series
#check WP.kernel_zeros
#print axioms WP.kernel_zeros
#check WP.leadingVolume
#print axioms WP.leadingVolume
#check WP.linearQ
#print axioms WP.linearQ
#check WP.linearS₀
#print axioms WP.linearS₀
#check WP.linear_mass_bounds
#print axioms WP.linear_mass_bounds
#check WP.logComparisonG
#print axioms WP.logComparisonG
#check WP.logDegreeProfile
#print axioms WP.logDegreeProfile
#check WP.logKernelCoeff
#print axioms WP.logKernelCoeff
#check WP.log_kernel_series
#print axioms WP.log_kernel_series
#check WP.logarithmic_comparison
#print axioms WP.logarithmic_comparison
#check WP.markedModel
#print axioms WP.markedModel
#check WP.marked_cusp
#print axioms WP.marked_cusp
#check WP.marked_cusp_all
#print axioms WP.marked_cusp_all
#check WP.marked_genus
#print axioms WP.marked_genus
#check WP.marked_genus_all
#print axioms WP.marked_genus_all
#check WP.marked_ratios
#print axioms WP.marked_ratios
#check WP.mass_identity
#print axioms WP.mass_identity
#check WP.mixedJ
#print axioms WP.mixedJ
#check WP.mixed_log_concavity
#print axioms WP.mixed_log_concavity
#check WP.mixed_transform
#print axioms WP.mixed_transform
#check WP.model
#print axioms WP.model
#check WP.moment₁
#print axioms WP.moment₁
#check WP.normalized
#print axioms WP.normalized
#check WP.normalized_kernel_identity
#print axioms WP.normalized_kernel_identity
#check WP.one_point
#print axioms WP.one_point
#check WP.pantsScale
#print axioms WP.pantsScale
#check WP.parameter_analytic_expansions
#print axioms WP.parameter_analytic_expansions
#check WP.parameter_critical
#print axioms WP.parameter_critical
#check WP.parameter_cusp_weight
#print axioms WP.parameter_cusp_weight
#check WP.parameter_regular
#print axioms WP.parameter_regular
#check WP.phaseAmplitude
#print axioms WP.phaseAmplitude
#check WP.phaseQuotient
#print axioms WP.phaseQuotient
#check WP.point_mass_bound
#print axioms WP.point_mass_bound
#check WP.poissonCenter
#print axioms WP.poissonCenter
#check WP.poissonCorrection
#print axioms WP.poissonCorrection
#check WP.poissonOperator
#print axioms WP.poissonOperator
#check WP.poisson_central_expansion
#print axioms WP.poisson_central_expansion
#check WP.positiveLift
#print axioms WP.positiveLift
#check WP.positiveRHS
#print axioms WP.positiveRHS
#check WP.positive_convolution
#print axioms WP.positive_convolution
#check WP.positive_recursion
#print axioms WP.positive_recursion
#check WP.primitive_bounds
#print axioms WP.primitive_bounds
#check WP.profile
#print axioms WP.profile
#check WP.profileB
#print axioms WP.profileB
#check WP.profileC
#print axioms WP.profileC
#check WP.profile_monotone
#print axioms WP.profile_monotone
#check WP.pureC
#print axioms WP.pureC
#check WP.pureC_zero_bounds
#print axioms WP.pureC_zero_bounds
#check WP.quadratic_profile
#print axioms WP.quadratic_profile
#check WP.quadratic_profile_all_markings
#print axioms WP.quadratic_profile_all_markings
#check WP.quantitative_adjacent
#print axioms WP.quantitative_adjacent
#check WP.quantitative_cusp_local
#print axioms WP.quantitative_cusp_local
#check WP.ratio
#print axioms WP.ratio
#check WP.saddleZeta
#print axioms WP.saddleZeta
#check WP.second_profile
#print axioms WP.second_profile
#check WP.second_profile_adjacent
#print axioms WP.second_profile_adjacent
#check WP.second_profile_all_degrees
#print axioms WP.second_profile_all_degrees
#check WP.separatingS
#print axioms WP.separatingS
#check WP.separatingSTail
#print axioms WP.separatingSTail
#check WP.separatingT
#print axioms WP.separatingT
#check WP.separatingTTail
#print axioms WP.separatingTTail
#check WP.separating_S_all_markings
#print axioms WP.separating_S_all_markings
#check WP.separating_T_two_markings
#print axioms WP.separating_T_two_markings
#check WP.separating_estimates
#print axioms WP.separating_estimates
#check WP.sharp_extraction
#print axioms WP.sharp_extraction
#check WP.shifted
#print axioms WP.shifted
#check WP.shifted_dilaton
#print axioms WP.shifted_dilaton
#check WP.shifted_kdv
#print axioms WP.shifted_kdv
#check WP.stationaryIntegral
#print axioms WP.stationaryIntegral
#check WP.stationary_root
#print axioms WP.stationary_root
#check WP.string_flow
#print axioms WP.string_flow
#check WP.substitutionCoeff
#print axioms WP.substitutionCoeff
#check WP.terminal_bounds
#print axioms WP.terminal_bounds
#check WP.terminal_ratio_lower
#print axioms WP.terminal_ratio_lower
#check WP.theta
#print axioms WP.theta
#check WP.tightGeneratingFunction_allStable_bounds
#print axioms WP.tightGeneratingFunction_allStable_bounds
#check WP.tightGeneratingFunction_allStable_positive_factor
#print axioms WP.tightGeneratingFunction_allStable_positive_factor
#check WP.tightGeneratingFunction_allStable_uniform_relative_error
#print axioms WP.tightGeneratingFunction_allStable_uniform_relative_error
#check WP.tightGeneratingFunction_identity
#print axioms WP.tightGeneratingFunction_identity
#check WP.tightIntensity
#print axioms WP.tightIntensity
#check WP.tightIntensityDensity
#print axioms WP.tightIntensityDensity
#check WP.tightScale
#print axioms WP.tightScale
#check WP.top_anchor
#print axioms WP.top_anchor
#check WP.topology_tails
#print axioms WP.topology_tails
#check WP.totalDegree
#print axioms WP.totalDegree
#check WP.transportBeta
#print axioms WP.transportBeta
#check WP.transport_equation
#print axioms WP.transport_equation
#check WP.trigDensity
#print axioms WP.trigDensity
#check WP.trigSaddle
#print axioms WP.trigSaddle
#check WP.trig_saddle_spec
#print axioms WP.trig_saddle_spec
#check WP.two_point
#print axioms WP.two_point
#check WP.uniform_kernel_moments
#print axioms WP.uniform_kernel_moments
#check WP.uniform_recursive_expansions
#print axioms WP.uniform_recursive_expansions
#check WP.uniform_saddle
#print axioms WP.uniform_saddle
#check WP.universalV
#print axioms WP.universalV
#check WP.unmarked_reduction
#print axioms WP.unmarked_reduction
#check WP.unscaledCoeff
#print axioms WP.unscaledCoeff
#check WP.unscaledMean
#print axioms WP.unscaledMean
#check WP.varpi
#print axioms WP.varpi
#check WP.volumeModel
#print axioms WP.volumeModel
#check WP.volume_ratios
#print axioms WP.volume_ratios
#check WP.weight
#print axioms WP.weight
#check WP.weightedLinear
#print axioms WP.weightedLinear
#check WP.weightedSeparating
#print axioms WP.weightedSeparating
#check WP.weighted_linear_bound
#print axioms WP.weighted_linear_bound
#check WP.weighted_separating_bound
#print axioms WP.weighted_separating_bound
#check WP.xCritical
#print axioms WP.xCritical
#check WP.y₀
#print axioms WP.y₀
#check WP.zeroLinearMass
#print axioms WP.zeroLinearMass
#check WP.zero_mass_defect
#print axioms WP.zero_mass_defect
#check WP.zeros
#print axioms WP.zeros
#check WP.zograf_constant
#print axioms WP.zograf_constant
