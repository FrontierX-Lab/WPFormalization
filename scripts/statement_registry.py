"""Final declaration associations and scope limits. Counts alone do not prove completeness."""

FULL = {'def:bessel': 'X XR a y₀ xCritical inverseY bessel_branches besselJ₀ besselJ₁ firstJ₀Zero '
               'bessel_dictionary',
 'def:stable': 'Stable complexity dimension totalDegree deficit',
 'eq:C1': 'trigSaddle trigDensity trig_saddle_spec',
 'eq:CE1': 'extractionS extractionB extraction_factorization',
 'eq:CG1': 'extractionQ poissonCenter',
 'eq:H13': 'mass_identity linearQ',
 'eq:H14': 'zero_mass_defect zeroLinearMass',
 'eq:H2': 'normalized_kernel_identity theta',
 'eq:H22': 'linear_mass_bounds linearS₀',
 'eq:H3': 'critical_kernels',
 'eq:H30': 'clippedWeight zeros inactive',
 'eq:P1': 'K H kernel_series',
 'eq:P10': 'critical_kernel_limits',
 'eq:P11': 'theta weight uniform_kernel_moments',
 'eq:P12': 'harmonicPGF harmonicMass harmonicVariance harmonic_law',
 'eq:P13': 'harmonic_local_limit',
 'eq:P2': 'kernel_differential',
 'eq:P9': 'barK barH A',
 'eq:PF1': 'Theta moment₁ Z kernel_action_moments',
 'eq:PF3': 'markedModel',
 'eq:PS1': 'pantsScale',
 'eq:SP1': 'T stationaryIntegral stationary_root',
 'eq:SP2': 'Delta action density',
 'eq:SP3': 'profileB profileC',
 'eq:WC1': 'chainProfile',
 'eq:boundary-profile': 'boundaryFactor boundary_factor_endpoints',
 'eq:cluster-intensities': 'criticalIntensityDensity criticalIntensity tightIntensity',
 'eq:instanton-correspondence': 'Coefficients.instanton_correspondence '
                                'Analysis.instanton_contour_coefficient_dictionary',
 'eq:intro-leading': 'leadingVolume',
 'eq:intro-varpi': 'varpi Xdiv',
 'eq:jt-abel-critical-edge': 'JT.jt_abel_critical_edge',
 'eq:jt-critical-action': 'Analysis.jt_critical_action',
 'eq:tight-scale': 'tightScale tightIntensityDensity tightIntensity',
 'ext:optional-stopping': 'Probability.bounded_optional_stopping',
 'lem:kernel-positivity': 'logKernelCoeff kernel_positivity log_kernel_series',
 'lem:kernel-zeros': 'kernel_zeros',
 'lem:majorant': 'analytic_majorant formalFixedPoint substitutionCoeff positiveLift',
 'lem:parameter': 'parameter_regular parameter_critical parameter_cusp_weight '
                  'parameter_analytic_expansions',
 'lem:phase-change': 'analytic_phase_change phaseAmplitude phaseQuotient',
 'lem:poisson-central': 'poisson_central_expansion poissonOperator poissonCorrection '
                        'centralCoefficient',
 'lem:uniform-saddle': 'uniform_saddle unscaledCoeff unscaledMean saddleZeta',
 'lem:weighted-linear': 'weighted_linear_bound weightedLinear PivotChoice',
 'lem:weighted-separating': 'weighted_separating_bound weightedSeparating'}

INTERFACE = {'cor:constant': 'zograf_constant',
 'cor:many-spectrum': 'Spectral.many_small_eigenvalues',
 'cor:spectral': 'Spectral.vanishing_spectral_gap',
 'cor:tight-boltzmann': 'BoltzmannWp.tight_boltzmann',
 'def:intersections': 'External.DMClasses External.mixedIntegral External.geometricBracket',
 'def:wp-volume': 'External.WeilPeterssonGeometry External.wpVolume',
 'eq:AV6': 'unmarked_reduction',
 'eq:AV7': 'HigherOrder.canonicalUnmarkedSeries HigherOrder.unmarkedCoefficient '
           'HigherOrder.absoluteCoefficient',
 'eq:C18': 'top_anchor boundaryA',
 'eq:C23': 'bottom_log_bound bracketB',
 'eq:C7': 'mixed_log_concavity mixedJ',
 'eq:C8': 'bracket_differences',
 'eq:CG12': 'HigherOrder.first_extracted_correction',
 'eq:CG13': 'HigherOrder.first_extracted_correction_critical',
 'eq:CG3': 'HigherOrder.extractionNumerator HigherOrder.extractionDenominator '
           'HigherOrder.rawExtractedCoefficient HigherOrder.extractedCoefficient '
           'HigherOrder.criticalExtractedCoefficient',
 'eq:FE1': 'HigherOrder.formalProfile HigherOrder.formalCusp HigherOrder.formalGenus '
           'cuspCorrection genusCorrection',
 'eq:FE14': 'HigherOrder.exactEndpoint HigherOrder.endpointInsertionFactor '
            'HigherOrder.exactEndpoint_formula',
 'eq:H10': 'initial_amplitudes',
 'eq:H12': 'harmonicCoeff model ratio',
 'eq:H4': 'pureC',
 'eq:H5': 'mixed_transform',
 'eq:H6': 'shifted backgrounds backgroundDegrees',
 'eq:H7': 'normalized',
 'eq:H8': 'string_flow',
 'eq:H9': 'positive_recursion positiveRHS',
 'eq:PF12': 'endpoint_string endpoint_pure_limit',
 'eq:PF13': 'endpoint_ratio',
 'eq:PF8': 'transport_equation transportBeta',
 'eq:PS3': 'RandomGeometry.pants_ordered_window_moments',
 'eq:ST13': 'HigherOrder.firstEndpointConstant HigherOrder.firstMarkedCorrection',
 'eq:TL12': 'shifted_dilaton dilaton_coefficient dilatonCoeff',
 'eq:TL14': 'shifted_kdv',
 'eq:TL19': 'separating_estimates separatingS separatingT separating_S_all_markings '
            'separating_T_two_markings',
 'eq:TL23': 'quadratic_profile quadratic_profile_all_markings',
 'eq:TL24': 'marked_cusp marked_cusp_all',
 'eq:TL27': 'marked_genus marked_genus_all',
 'eq:TL37': 'cuspMass',
 'eq:TL9': 'W profile',
 'eq:boundary-factor': 'growing_boundary_factor',
 'eq:cluster-overdispersion': 'Critical.PantsCluster.critical_cluster_overdispersion',
 'eq:intro-Phi': 'Phi volumeModel',
 'eq:jt-string-normalization': 'JT.string_normalization',
 'ext:collar': 'External.CollarGeometry',
 'ext:dvv': 'PsiTheory',
 'ext:fixed-genus': 'External.fixed_genus_normalized_volume_logarithm',
 'ext:iz': 'External.phiCoefficient External.itzykson_zuber',
 'ext:kdv': 'External.integrated_first_kdv External.first_kdv_descendants',
 'ext:minmax': 'External.SpectralGeometry',
 'ext:mir-integration': 'External.MirzakhaniIntegration',
 'ext:mixed-transform': 'External.IntersectionRealization External.HigherKappaRealization',
 'ext:nef-teissier': 'External.classical_onepoint_nef_realization',
 'ext:one-point': 'one_point',
 'ext:painleve-borel': 'External.PainleveAnalytic.CCHData '
                       'External.PainleveAnalytic.exists_cch_data',
 'ext:painleve-contour': 'External.PainleveAnalytic.GIKMData '
                         'External.PainleveAnalytic.exists_gikm_data',
 'ext:painleve-leading': 'External.painleveAction External.stokesAmplitude '
                         'External.normalizedZeroInstanton External.painleve_leading_error '
                         'External.painleve_leading External.painleve_first_correction_error',
 'ext:shen-wu': 'External.ShenWuPantsBound',
 'ext:shen-wu-volumes': 'External.shenWu_volume_upper External.shenWu_volume_critical_lower',
 'ext:short-filling': 'External.ShortFillingGeometry.SingleCurvePieceClassics '
                      'External.ShortFullFillingGeometry.FullSingleCurveFillingClassics '
                      'Critical.ShortConfiguration.exists_actual_short_simple_tuple_cut '
                      'Critical.ShortConfiguration.activeSupport_negativeEuler_le '
                      'Critical.ShortConfiguration.supporting_piece_boundaryLength_le '
                      'Critical.ShortConfiguration.actual_cluster_selected_indices '
                      'Critical.ShortConfiguration.exists_actual_intersecting_masked_record '
                      'Critical.ShortConfiguration.masked_tuple_recording_fiber_card_le '
                      'Critical.ShortConfiguration.exists_actual_single_nonpants_masked_record '
                      'Critical.ShortConfiguration.cut_masked_selected_curve_count_le',
 'ext:stirling': 'External.gamma_ratio_error External.gammaStirlingMain '
                 'External.gamma_stirling_error External.logStirlingPartial '
                 'External.log_gamma_stirling_remainder External.gamma_finite_product '
                 'External.gaussian_integral External.gamma_ratio_first_correction_error '
                 'External.gammaLogRatioKernel External.log_gamma_ratio_laplace',
 'ext:tight-geometry': 'External.BuddLionsTightGeometry',
 'ext:tight-integration': 'External.BuddLionsTightIntegration',
 'ext:tight-transform': 'External.BuddZonneveldTransform',
 'ext:two-point': 'two_point',
 'lem:coefficient-bounds': 'coefficient_bounds',
 'lem:convolution': 'positive_convolution convolutionR universalV',
 'lem:critical-complex': 'Critical.complex_short_configurations',
 'lem:critical-cuts': 'Critical.critical_cut_estimate Critical.critical_cut_marked_estimate '
                      'Critical.critical_cut_estimate_regime '
                      'Critical.critical_cut_marked_estimate_regime '
                      'Critical.critical_unordered_cut_estimate '
                      'Critical.critical_unordered_cut_marked_estimate '
                      'Critical.critical_unordered_cut_estimate_regime '
                      'Critical.critical_unordered_cut_marked_estimate_regime '
                      'Critical.critical_cut_expectation_regime '
                      'Critical.critical_cut_marked_expectation_regime',
 'lem:critical-skeleton': 'Critical.joint_nonseparating_pants_poisson_limit',
 'lem:first-degree': 'first_degree degreeCorrection first_degree_all_degrees',
 'lem:first-order': 'growing_marking_first_order cuspCorrection genusCorrection',
 'lem:large-indices': 'HigherOrder.extraction_large_indices',
 'lem:local-comparison': 'HigherOrder.local_comparison',
 'lem:log-comparison': 'logarithmic_comparison logComparisonG logDegreeProfile',
 'lem:lower': 'comparison_lower',
 'lem:monotone': 'profile_monotone',
 'lem:point-mass': 'point_mass_bound',
 'lem:primitive-bounds': 'primitive_bounds',
 'lem:primitive-count': 'Critical.PrimitivePacking.bounded_primitive_count',
 'lem:second-profile': 'HigherOrder.secondIncrement HigherOrder.secondProfile second_profile '
                       'second_profile_all_degrees second_profile_adjacent '
                       'HigherOrder.second_profile_path_independent',
 'lem:small-indices': 'HigherOrder.extraction_small_indices',
 'lem:tails': 'separatingSTail separatingTTail topology_tails',
 'lem:terminal': 'terminal_bounds pureC_zero_bounds terminal_ratio_lower',
 'lem:tight-connected': 'TightConnected.tight_connected_original_saddle '
                        'TightConnected.tight_connected_original_scale '
                        'TightConnected.tight_connected_original_bounded '
                        'TightConnected.tight_connected_original_bounded_scale '
                        'TightConnected.tight_connected',
 'lem:tight-gf': 'tightGeneratingFunction_identity tightGeneratingFunction_allStable_bounds '
                 'tightGeneratingFunction_allStable_uniform_relative_error '
                 'tightGeneratingFunction_allStable_positive_factor',
 'lem:tight-separating': 'TightSeparating.actual_tight_separating_expectation_uniform '
                         'TightSeparating.actual_tight_separating_lintegral_uniform',
 'lem:upper': 'comparison_upper',
 'prop:bounded-boundaries': 'bounded_boundaries boundaryVolumeModel',
 'prop:harmonic': 'harmonic_comparison',
 'prop:hierarchy': 'uniform_recursive_expansions',
 'prop:local-limit': 'cusp_local_limit',
 'prop:marked-ratios': 'marked_ratios',
 'prop:pants-concentration': 'RandomGeometry.short_pants_concentration',
 'prop:prefactor': 'absolute_prefactor',
 'prop:quantitative-local': 'quantitative_cusp_local',
 'thm:absolute': 'absolute_volume',
 'thm:canonical-expansion': 'HigherOrder.canonical_expansion',
 'thm:chain': 'diagonal_chain',
 'thm:coefficient': 'adjacent_limit quantitative_adjacent adjacent_endpoint_limits',
 'thm:critical-cluster': 'Critical.PantsCluster.critical_primitive_length_spectrum',
 'thm:first-correction': 'HigherOrder.first_correction',
 'thm:full-expansion': 'HigherOrder.full_expansion',
 'thm:intro-absolute': 'HigherOrder.intro_absolute HigherOrder.unmarked_first_exact',
 'thm:pants-poisson': 'RandomGeometry.pants_poisson_theorem',
 'thm:quantitative-coefficient': 'quantitative_adjacent',
 'thm:sharp-extraction': 'sharp_extraction',
 'thm:tight-spectrum': 'Tight.tight_length_spectrum',
 'thm:volume': 'volume_ratios'}

BLOCKED = {'ext:complex-analysis': 'Precise classical implicit-function, Pringsheim, Rouche, and Hadamard inputs '
                         'are registered. The local Cauchy and actual slit-domain two-constants '
                         'estimates are proved. General formal Lagrange inversion in the broader '
                         'summary remains missing; the distinction in scope is retained.',
 'ext:fixed-cusps': 'The fixed-n leading term with an unknown universal constant and the n=0 first '
                    'correction are available. The full-order polynomial corrections and absolute '
                    "bracket differences required by the broader summary are still missing. The paper's "
                    'constant value has not been made an external assumption.',
 'ext:fourier': 'Actual analytic-PGF and nonnegative-lattice Fourier results, iid harmonic inversion, '
                'and the uniform local limit theorem are proved locally. The broader version for '
                'arbitrary integer-valued laws, including negative support, is not yet covered by a '
                'statement of the same scope. A Taylor sublemma that defines negative-index '
                'coefficients as zero does not establish full coverage.'}

PARTIAL_COVERAGE = {'ext:collar': 'Precise classical interfaces for simplicity and disjointness of short primitive '
               'geodesics, and actual packing, doubling, and axial representations, are available. '
               'These fields do not fully supply the pointwise Margulis decomposition or existence and '
               'uniqueness of geodesic representatives for every eligible free homotopy class.'}
