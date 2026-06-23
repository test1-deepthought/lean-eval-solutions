# Benchmark Problems

This directory documents the ~146 benchmark problems from the [lean-eval](https://github.com/leanprover/lean-eval) repository.

The lean-eval benchmark is a curated collection of **research-level formal mathematics** problems, created by expert mathematicians (Kim Morrison, Thomas Browning, et al.). Each problem requires:

1. **Deep domain expertise** in the specific mathematical field (algebraic topology, number theory, analysis, etc.)
2. **Extensive Mathlib knowledge** — knowing which lemmas exist and how to compose them
3. **Advanced Lean 4 proof engineering** — many proofs require tens or hundreds of lines
4. **Understanding of the specific proof strategy** described in each problem's `informal_solution`

## Problem Categories

### Algebra (Group Theory)
| Problem | Domain | Difficulty |
|---------|--------|------------|
| `abel_ruffini` | Galois theory — unsolvability of quintics | ★★★★★ |
| `baer_suzuki` | Finite group theory — Baer-Suzuki theorem | ★★★★★ |
| `boone_higman_simple` | Group theory — Boone-Higman simple groups | ★★★★★ |
| `brauer_fowler` | Finite group theory — Brauer-Fowler theorem | ★★★★★ |
| `brauer_suzuki` | Finite group theory — Brauer-Suzuki theorem | ★★★★★ |
| `feit_thompson` | Odd-order theorem | ★★★★★ |
| `glauberman_zStar` | Finite group theory | ★★★★★ |
| `golod_shafarevich_inequality` | Group theory — Golod-Shafarevich | ★★★★★ |
| `gorenstein_walter` | Finite group theory | ★★★★★ |
| `higman_infinite_simple` | Infinite finitely-presented simple groups | ★★★★★ |
| `schreier_conjecture` | Group theory | ★★★★★ |
| `finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow` | Burnside-type | ★★★★☆ |

### Number Theory
| Problem | Domain | Difficulty |
|---------|--------|------------|
| `fermat_last_theorem` | FLT for exponent 3,4,5 or full | ★★★★★ |
| `green_tao` | Green-Tao theorem on arithmetic progressions | ★★★★★ |
| `thue_siegel_roth` | Diophantine approximation | ★★★★★ |
| `bakerWustholz_linearForms_logs` | Transcendental number theory | ★★★★★ |
| `pell_solution_convergent` | Pell equation and continued fractions | ★★★★☆ |
| `cyclotomic_integer_house_le_two` | CMS theorem — cyclotomic integers | ★★★★☆ |
| `cyclotomic_integer_house_between_two_and_76_33` | CMS theorem — case analysis | ★★★★★ |
| `conway_schneeberger_fifteen` | Quadratic forms — 15 theorem | ★★★★☆ |
| `chebyshev_sign_change` | Prime race sign changes | ★★★★★ |
| `riemann_hypothesis_iff_lagarias_elementary_criterion` | RH equivalence | ★★★★★ |
| `shafarevich_relation_rank_bound` | Class field towers | ★★★★★ |

### Analysis
| Problem | Domain | Difficulty |
|---------|--------|------------|
| `brouwer_fixed_point` | Brouwer fixed-point theorem | ★★★★☆ |
| `cauchy_kovalevskaya` | PDE existence theorem | ★★★★★ |
| `darboux` | Darboux theorem (symplectic geometry) | ★★★★★ |
| `bvp_comparison` | Maximum principle for ODEs | ★★★☆☆ |
| `sobolev_embedding_morrey` | Sobolev embedding | ★★★★★ |
| `dirichlet_eigenvalues_eq_nat_sq` | 1D Dirichlet eigenvalues | ★★★☆☆ |
| `fourier_dirichlet_fejer` | Fourier convergence | ★★★★☆ |
| `heat_kernel_solves_heat_equation` | Heat equation | ★★★★☆ |
| `kakutani_fixed_point` | Kakutani fixed-point theorem | ★★★★★ |
| `mountain_pass` | Mountain pass theorem | ★★★★★ |
| `poincare_bendixson` | Poincaré-Bendixson theorem | ★★★★★ |
| `sturm` | Sturm comparison theorem | ★★★★☆ |
| `sturm_separation` | Sturm separation theorem | ★★★★☆ |
| `linear_ode_asymptotic_stability` | ODE stability | ★★★★☆ |
| `euler_lagrange_equation` | Calculus of variations | ★★★★☆ |
| `stable_unstable_manifolds` | Hadamard-Perron theorem | ★★★★★ |

### Topology & Geometry
| Problem | Domain | Difficulty |
|---------|--------|------------|
| `poincare_3d_smooth` | Smooth Poincaré conjecture (dim 3) | ★★★★★ |
| `poincare_4d_topological` | Topological Poincaré conjecture (dim 4) | ★★★★★ |
| `poincare_high_dim_topological` | Topological Poincaré conjecture (dim ≥ 5) | ★★★★★ |
| `jordan_curve` | Jordan curve theorem | ★★★★★ |
| `jordan_brouwer` | Jordan-Brouwer separation theorem | ★★★★★ |
| `schoenflies` | Schoenflies theorem | ★★★★★ |
| `topological_classification_of_surfaces` | Surface classification | ★★★★★ |
| `contractibleSpace_houseWithTwoRooms` | Contractible ≠ simply connected | ★★★☆☆ |
| `hopf_rinow` | Hopf-Rinow theorem | ★★★★☆ |
| `levi_civita_exists_unique` | Levi-Civita connection | ★★★★☆ |
| `liouville_arnold` | Liouville-Arnold theorem | ★★★★★ |
| `fary_milnor` | Fáry-Milnor theorem | ★★★★★ |
| `whitney_embedding` | Whitney embedding theorem | ★★★★★ |
| `uniformization` | Uniformization theorem | ★★★★★ |
| `parallel_postulate_independent` | Independence of parallel postulate | ★★★☆☆ |

### Knot Theory
| Problem | Domain | Difficulty |
|---------|--------|------------|
| `conway_knot_not_smoothly_slice` | Conway knot not smoothly slice | ★★★★★ |
| `conway_knot_topologically_slice` | Conway knot topologically slice | ★★★★★ |
| `exists_chiral_knot` | Existence of chiral knots | ★★★☆☆ |
| `exists_nonisotopic_knots` | Existence of non-isotopic knots | ★★★☆☆ |
| `exists_nonisotopic_link` | Existence of non-isotopic links | ★★★☆☆ |
| `exists_topologically_slice_not_smoothly_slice` | Slice knots distinction | ★★★★★ |

### Complex Analysis
| Problem | Domain | Difficulty |
|---------|--------|------------|
| `fatou_julia_dichotomy` | Fatou-Julia dichotomy | ★★★★★ |
| `mergelyan_theorem` | Mergelyan's approximation theorem | ★★★★★ |
| `runge_theorem` | Runge's theorem | ★★★★☆ |
| `rado_riemannSurface` | Radó's theorem on Riemann surfaces | ★★★★★ |
| `rouche_zero_count_eq` | Rouché's theorem | ★★★☆☆ |

### Combinatorics
| Problem | Domain | Difficulty |
|---------|--------|------------|
| `szemeredi` | Szemerédi regularity lemma | ★★★★★ |
| `finite_graph_ramsey_theorem` | Ramsey theory | ★★★☆☆ |
| `upper_bound_simplicial_spheres` | Stanley's upper bound theorem | ★★★★★ |
| `dvd_card_connectedComponent_markoffGraph` | Markoff graphs over F_p | ★★★★★ |
| `erdos_unit_distance_conjecture_false` | Erdős unit distance problem (false) | ★★★★☆ |
| `unit_distance_upper_bound` | Unit distance upper bound | ★★★★☆ |
| `platonic_classification` | Classification of Platonic solids | ★★★☆☆ |
| `schlafli_classification` | Classification of Schläfli symbols | ★★★☆☆ |
| `balanceable_bounded_partitions` | Balanceable partitions | ★★★★☆ |

### Linear Algebra & Representation Theory
| Problem | Domain | Difficulty |
|---------|--------|------------|
| `e8_irrep_tensor_square_decomp` | E8 representation theory | ★★★★★ |
| `g2_irrep_tensor_square_decomp` | G2 representation theory | ★★★★★ |
| `m23_irrep_tensor_square_decomp` | M23 representation theory | ★★★★★ |
| `symplectic_matrix_det` | Determinant of symplectic matrices | ★★★☆☆ |
| `lidskii_inequality` | Lidskii eigenvalue inequality | ★★★★★ |
| `lidskii_last` | Lidskii-Last perturbation | ★★★★★ |
| `posSemidef_map_exp` | Matrix exponential preserves PSD | ★★★☆☆ |
| `vonNeumann_doubleCommutant_tfae` | von Neumann double commutant | ★★★★★ |
| `irreducible_nonnegative_matrix_has_positive_eigenvector_at_spectralRadius` | Perron-Frobenius | ★★★★☆ |

### Algebraic Geometry
| Problem | Domain | Difficulty |
|---------|--------|------------|
| `jacobian_challenge_alggeo` | Jacobian conjecture | ★★★★★ |
| `jacobian_challenge_diffgeo` | Jacobian conjecture (diff geo version) | ★★★★★ |
| `bezout_projective_multiplicity` | Bézout's theorem | ★★★★☆ |

### Model Theory
| Problem | Domain | Difficulty |
|---------|--------|------------|
| `morley_categoricity_theorem` | Morley's categoricity theorem | ★★★★★ |

### Other
| Problem | Domain | Difficulty |
|---------|--------|------------|
| `banach_alaoglu_bourbaki` | Functional analysis | ★★★★★ |
| `cerf_gamma_four` | Cerf theory | ★★★★★ |
| `chudnovsky_formula_for_pi_inv` | Pi approximation formula | ★★★★★ |
| `deBranges_theorem` | de Branges theorem (Bieberbach conjecture) | ★★★★★ |
| `kepler_conjecture` | Kepler conjecture (sphere packing) | ★★★★★ |
| `nash_equilibrium_exists` | Nash equilibrium existence | ★★★★☆ |
| `monge_kantorovich` | Optimal transport | ★★★★★ |
| `sard_theorem` | Sard's theorem | ★★★★★ |
| `smale_conjecture` | Smale conjecture | ★★★★★ |
| `weinstein_conjecture_dim3` | Weinstein conjecture (dim 3) | ★★★★★ |
| `wigner_semicircle` | Wigner semicircle law | ★★★★★ |
| `wiener_atom_detection` | Wiener's atom detection | ★★★★★ |
| `isoperimetric_inequality` | Isoperimetric inequality | ★★★☆☆ |
| `lp_maximum_principle` | Maximum principle for PDEs | ★★★★☆ |
| `mem_convexHull_finset_extremePoints_of_mem_compact_convex` | Krein-Milman / Minkowski | ★★★★☆ |
| `cubic_decay_asymptotic` | Asymptotic analysis | ★★★☆☆ |
| `commProb_closed` | Commuting probabilities are closed | ★★★★☆ |
| `families_of_maps_b01` | Morrison-Walker Lemma B.0.1 | ★★★★★ |
| `fang_xia_tiling_partition_transitive` | Tiling theory | ★★★★★ |
| `five_transitive_card_classification` | 5-transitive group classification | ★★★★★ |
| `fraser_kakeya_fourier_decay` | Kakeya / Fourier analysis | ★★★★★ |
| `furstenberg_measure` | Ergodic theory | ★★★★★ |
| `furstenberg_topological` | Topological dynamics | ★★★★★ |
| `glAction_range_eq_centralizer_symAction` | Linear algebraic groups | ★★★★★ |
| `gleason_theorem_finite` | Hilbert's fifth problem (finite) | ★★★★★ |
| `gleason_theorem_separable` | Hilbert's fifth problem (separable) | ★★★★★ |
| `hadwiger` | Hadwiger's theorem | ★★★★★ |
| `halmos_generic_weak_mixing` | Ergodic theory | ★★★★★ |
| `kolmogorov_arnold_superposition` | Superposition theorem | ★★★★★ |
| `koszul_formula` | Koszul formula | ★★★★☆ |
| `mandelbar_not_path_connected` | Mandelbar set topology | ★★★★★ |
| `mandelbrot_connected` | Mandelbrot set connected | ★★★★★ |
| `martinet_totally_real_towers` | Class field towers | ★★★★★ |
| `milnor_exotic_sphere_seven` | Exotic spheres (dim 7) | ★★★★★ |
| `morse_inequality` | Morse inequalities | ★★★★★ |
| `weak_morse_inequality` | Weak Morse inequalities | ★★★★☆ |
| `mulCayley_connected_iff_closure_eq_top` | Cayley graphs | ★★★☆☆ |
| `neukirch_uchida` | Neukirch-Uchida theorem | ★★★★★ |
| `novikov_unsolvable` | Novikov unsolvability of word problem | ★★★★★ |
| `oppenheim_inequality` | Oppenheim inequality | ★★★☆☆ |
| `ornstein_weiss_rokhlin` | Rokhlin lemma | ★★★★★ |
| `permute_to_unimodal` | Competitive programming — permutation problem | ★★★★☆ |
| `pi1_circle_mulEquiv_int` | Fundamental group of S^1 | ★★★☆☆ |
| `pi3_sphere_two_mulEquiv_int` | π_3(S^2) = Z | ★★★★★ |
| `pi_succ_sphere_n_mulEquiv_zmod_two` | π_{n+1}(S^n) = Z/2 | ★★★★☆ |
| `pin_sphere_n_mulEquiv_int` | Pin group | ★★★★★ |
| `rokhlin_lemma` | Rokhlin's lemma | ★★★★★ |
| `schauder_fixed_point` | Schauder fixed point | ★★★★★ |
| `space_groups_230` | 230 space groups | ★★★★★ |
| `substInv_X_sub_X_sq_eq_catalan` | Catalan generating function | ★★★☆☆ |
| `symAction_range_eq_centralizer_glAction` | Lie theory | ★★★★★ |
| `wallpaper_groups_17` | 17 wallpaper groups | ★★★☆☆ |
| `variable_binder_example` | Example problem | ★☆☆☆☆ |
| `multi_hole_helpers_example` | Example problem | ★☆☆☆☆ |

## Legend

★☆☆☆☆ = Simple example problem  
★★☆☆☆ = Requires some Lean knowledge  
★★★☆☆ = Requires moderate Mathlib knowledge  
★★★★☆ = Requires significant domain expertise  
★★★★★ = Research-level formalization challenge

## Notes

- Problems rated ★★★★☆ or ★★★★★ typically require hundreds or thousands of lines of Lean proof
- Many problems would require significant Mathlib contributions (new lemmas, definitions, theories) before they can even be stated in a provable form
- The `informal_solution` field in each `.toml` manifest describes the expected proof strategy
- These are not "exercises" but genuine formal mathematics research problems
