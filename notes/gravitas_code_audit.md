# The public Gravitas code at commit 9b02562

Source: github.com/JonathanGorard/Gravitas (GC), commit 9b02562 of 2023-08-28 ("Completed ADM evolution and conservation equation implementation."). The repository has 82 commits, the first (32dab75) of 2022-12-03, and 23 `.wl` files with 28,576 lines. File:line references below are to this commit.

Dates: G3 (arXiv:2102.09363) is of February 2021, 22 months before the first commit. The last commit is five months before Gravitas II (GII, arXiv:2401.14209, 2024-01-25).

Paper references: GII = `papers/tex_2401/GravitasPaper2.tex`, GH = `papers/tex_2402/AccretionPaper2.tex` (arXiv:2402.02331). Each TeX paragraph is one line, so a TeX line number names a paragraph. G3 line numbers refer to `papers/gorard_2102.09363.txt`.

Every finding in this note is READ (from the code at commit 9b02562) unless another status is given.

## 1. Discrete hypersurfaces are samples of a continuum metric

`DiscreteHypersurfaceDecomposition.wl:56-98` (property "CoordinatizedPolarGraphColored"):

- Lines 65-87 compute the Christoffel symbols, the Riemann tensor and the Kretschmann scalar of the symbolic `MetricTensor`, with the coordinates other than time and the two plotted coordinates set to 0.
- Lines 88-92 build `DiscretizeRegion[ImplicitRegion[-(kretschmannScalar /. {r -> Sqrt[x^2 + y^2], θ -> ArcTan[y/x]} /. t -> finalTime) == l, {x, y, l}], cube]`.
- Line 93 is `points = RandomPoint[region, vertexCount]`.
- Lines 94-95 join two points by an `UndirectedEdge` when `Norm[First[#1] - Last[#1]] < discretizationScale`.
- Lines 96-98 colour vertices and edges with `ColorData["LightTemperatureMap", -(l/curvatureRange)]` and place each vertex at its point (x, y, l).

A "discrete hypersurface" in GC is a uniform random sample of `vertexCount` points on the two-dimensional surface l = −K(x, y, t) inside a cube, where K is the Kretschmann scalar, with an undirected edge between points at Euclidean distance below the discretization scale. The variants without "Coordinatized" (lines 103-147 and 195-236) build the same graph and leave the layout to `Graph`. Points near the singularity, where −K leaves the cube, are absent, which leaves a hole at the centre. GII Figure 47 (`papers/tex_2401/GravitasFigure93.png`) shows the input `DiscreteHypersurfaceDecomposition[MetricTensor[{"Schwarzschild", 1}, {t, r, θ, φ}], {t, 0, 1}, {r, 0, 4}, {θ, -Pi, Pi}, 400, 1.2]` and its output.

## 2. The "evolution" properties draw a new sample at each time

`DiscreteHypersurfaceDecomposition.wl:293` defines `{"CoordinatizedPolarGraphEvolutionColored", stepCount_Integer}`. Line 331 builds one region per time in `Range[initialTime, finalTime, (finalTime - initialTime)/stepCount]`, and line 332 draws `RandomPoint[#1, vertexCount] & /@ regions`. The property without a step count (lines 241-290) uses 10 steps (line 279).

Each time slice receives a new `RandomPoint` sample of the continuum metric at that time, so no vertex or edge passes from one slice to the next, and no rewriting rule is applied. GII Figure 49 (`papers/tex_2401/GravitasFigure97.png`) shows the call `decomposition[{"CoordinatizedPolarGraphEvolutionColored", 5}]` and six graphs. The Kretschmann scalar of Schwarzschild in Schwarzschild coordinates does not depend on t, so the six graphs of GII Figures 49 and 50 are six samples of one surface, and their layouts differ (`papers/tex_2401/GravitasFigure99.png`). GC produces a time sequence of hypergraph images from any time-dependent `MetricTensor` without a rewriting rule.

GII line 1277 states that Figures 52 and 53 "use the DiscreteHypersurfaceDecomposition function to show the full evolution of spatial hypergraphs from the initial coordinate time t = 0M to the final coordinate time t = 24M via a sequence of six discrete time steps, for decompositions of the resulting Brill-Lindquist geometry obtained from the simulated collision".

## 3. Colouring

GII line 1180 describes the figures as having "vertices and edges colored based on the extrinsic curvature of the spacelike hypersurface". `DiscreteHypersurfaceDecomposition.wl:85-97` colour by the Kretschmann scalar. The t = const slices of the static Schwarzschild metric have K_ij = 0, so a colouring by extrinsic curvature would be uniform. The figures show a radial gradient.

## 4. Geodesics

`DiscreteHypersurfaceGeodesic.wl:146` solves the geodesic equations of the `MetricTensor` with `NDSolve`. Line 164 adds `RandomPoint[region, vertexCount - Length[geodesicPoints]]` and line 167 applies the same Euclidean cut-off. The evolution variant samples at each time (line 311). The `NDSolve` calls of this file (lines 146, 219, 291 and 369) are the only numerical solver calls in GC.

## 5. The ADM "solvers" are symbolic

- `SolveVacuumADMEquations.wl:3-8`: `SolveVacuumADMEquations[ADMDecomposition[...]]` returns `VacuumADMSolution[...]`, which holds the input decomposition.
- Lines 18-103 ("SolutionQ") build the evolution equations from the given metric, lapse and shift, and return `True` or `False` after `FullSimplify` (lines 97-100).
- The properties at lines 192-1557 ("EvolutionEquations", "HamiltonianConstraint", "MomentumConstraints" and their Reduced and Symbolic forms) return expressions.
- `SolveADMEquations.wl` has the same structure, with the energy and momentum conservation equations (lines 662-1102).

Neither file calls `NDSolve`, discretises a derivative, or contains a time step. No file of GC contains any of the strings `RungeKutta`, `Runge`, `Kreiss`, `WENO`, `Refine`, `Coarsen`, `Subdivide`, `WolframModel`, `SetReplace`, `hypergraph` or `Hypergraph`. The commit "Finalized implementation of vacuum ADM equation solver" (6ac8774, 2023-03-27) is the last change to `SolveVacuumADMEquations.wl`.

## 6. Capabilities stated in GII, against GC

GII abstract (line 24), line 1168 and lines 1226-1329. "Present" gives the file:line in GC. "Absent" means no code in GC at commit 9b02562.

| Capability | GC |
|---|---|
| Brill-Lindquist initial data | Present as a symbolic spatial metric, `ADMDecomposition.wl:265-290`: ψ = 1 + (M/\|r − z₀\| + M/\|r + z₀\|)/2, symbolic lapse and shift, no time dependence |
| Gauge conditions | Present as symbolic equations, `ADMDecomposition.wl:941-1700`: geodesic slicing (line 941, which returns `lapseFunction == 1`), maximal and harmonic slicing, 1 + log slicing (line 1194), normal and harmonic coordinate conditions (lines 1300, 1311), minimal distortion (line 1433) and pseudo-minimal distortion (line 1614) shift conditions |
| ADM evolution equations, Hamiltonian and momentum constraints | Present as symbolic expressions and truth values, `SolveVacuumADMEquations.wl:279-1557`, `SolveADMEquations.wl:345-1420` |
| Numerical time integration (fourth-order Runge-Kutta, finite-difference stencils, Kreiss-Oliger dissipation, GII line 1168) | Absent |
| Numerical constraint solve (the iterative elliptic solve of GII line 1337 and GH line 364) | Absent |
| Adaptive refinement by hypergraph rewriting, tagging function, WENO reconstruction | Absent |
| Discrete hypersurfaces | Present as samples of an analytic metric (§1-§2) |
| Binary merger of GII Figures 51-53 | The decomposition of Figure 51 is present (`ADMDecomposition.wl:265`). GC has no solver that yields a time-dependent metric for these data, and its Brill-Lindquist decomposition does not depend on time, so the evolved hypergraphs of Figures 52-53 cannot be produced from GC |
| Ψ4, null tetrads, spin-weighted harmonics and strain (GII lines 1306-1321) | Absent. `WeylTensor.wl` (832 lines) computes the Weyl tensor and its two principal invariants and no Newman-Penrose scalar |

Whether the code behind GII and GH exists elsewhere cannot be determined from the public repository (OPEN). GII line 39 states that many functions "have not yet been documented in this way, or ... have received further development beyond their documented versions".

## 7. G3 §6 images and the GC mechanism

G3 lines 6198-6208 and the captions of Figures 73-77 and 79-83 present hypergraphs of the rule's evolution at t = 0, 6M, 12M and 24M. §2 gives a hypergraph per time from a continuum metric, coloured by a curvature scalar with `LightTemperatureMap`, with a hole where the curvature leaves the plotting cube. The right-hand (rule) panels of G3 have the same colour map and a hole at each puncture (`papers/tex_2102/NumericalRelativity167.png` to `NumericalRelativity170.png`). GC colours by the Kretschmann scalar, G3 states colouring by ψ (lines 6185-6192), and GC has no time-dependent Brill-Lindquist metric. GC postdates G3 by 22 months.

- GC contains neither the exponent −2 of G3 eq. 391 nor any colouring by ψ.
- GC has no function named `CurvedSpacetimeRegionSprinkling` (G3 line 300).
- Whether G3 Figures 73-77 were produced by re-sampling of this kind or by evolution under the rule cannot be determined from the public code (OPEN).

## 8. PhysicsFoundation

github.com/JonathanGorard/PhysicsFoundation, commit bfb356d of 2026-01-20 ("Extended training pipeline to incorporate pretraining of electron parallel heat flux (M3par) inference for the NSTX-U axisymmetric GK setup, and added new corresponding model weights."). The tree has 9,561 files, of which 9,399 are `.gkyl` data files. The C sources in `training_src/`, `evaluation_src/` and `validation_src/` are Vlasov and gyrokinetic setups (for example `rt_gk_bgk_asdex_2x2v_p1.c` and `rt_vlasov_sr_twostream_1x1v.c`) built on Gkeyll. A case-insensitive search of every text file for wolfram, hypergraph, lindquist, ccz4, bssn, gravitas, einstein, schwarzschild and kerr finds no file. The repository contains plasma kinetic simulation and machine-learning code, and no general relativity, rewriting or refinement code.
