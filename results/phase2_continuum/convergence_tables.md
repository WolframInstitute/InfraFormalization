# Convergence tables of G3 and G4 against their norm definitions

## Norm definitions

G3 eqs. 180-181 (`papers/gorard_2102.09363.txt` lines 2671-2687) define the norms of the Hamiltonian constraint H over a partition of the domain into subgraphs i:

    ‖H‖₁ = Σ_i m_i |H_i|,   ‖H‖₂ = (Σ_i m_i H_i²)^(1/2),   ‖H‖∞ = max_i [m_i |H_i|],   m_i = V_i / V_tot.

G4 eqs. 186-187 (`papers/gorard_2303.07282.txt` lines 2955-2968) repeat these definitions. G4 eq. 186 prints the maximum as max_i [m_i |H|], with H unsubscripted.

## Ordering forced by the definitions

The weights satisfy m_i ≥ 0 and Σ_i m_i ≤ 1. The two inequalities below are elementary and are not formalised in Lean.

- ‖H‖∞ ≤ ‖H‖₁, because ‖H‖∞ is one non-negative term of the sum ‖H‖₁.
- ‖H‖₁ ≤ ‖H‖₂, because the Cauchy-Schwarz inequality gives ‖H‖₁² ≤ (Σ_i m_i)(Σ_i m_i H_i²) ≤ ‖H‖₂².

Every row of a table computed with these definitions satisfies L∞ ≤ L1 ≤ L2.

## Rows that violate the ordering (MEASURED)

Script: `scripts/python/check_convergence_tables.py`, run as `python3 -I scripts/python/check_convergence_tables.py` from the repository root on 2026-10-24. Output: `results/phase2_continuum/convergence_tables.out`. The script reads every row of the tables from the text files, with the vertex count, the three norms (L1, L2, L∞) and the printed orders.

| Paper | Table | Text lines | Problem | Rows violating L∞ ≤ L1 ≤ L2 |
|---|---|---|---|---:|
| G3 | 1 | 2709-2713 | CCZ4, static Schwarzschild | 2 of 5 |
| G3 | 2 | 3200-3204 | CCZ4, Kerr | 5 of 5 |
| G3 | 3 | 3517-3521 | CCZ4, maximally extended Schwarzschild | 5 of 5 |
| G3 | 4 | 4476-4480 | CCZ4, Schwarzschild head-on collision | 5 of 5 |
| G3 | 5 | 4694-4698 | CCZ4, Kerr head-on collision | 5 of 5 |
| G3 | 6 | 6227-6231 | the rule of line 6202, Schwarzschild head-on collision | 5 of 5 |
| G3 | 7 | 6377-6381 | the rule of line 6202, Kerr head-on collision | 1 of 5 |
| G4 | 1 | 3003-3007 | CCZ4, scalar-field collapse to Schwarzschild | 0 of 5 |
| G4 | 2 | 4408-4412 | CCZ4, scalar-field collapse to extremal Kerr | 2 of 5 |
| G4 | 3 | 5131-5135 | the rule, scalar-field collapse to Schwarzschild | 0 of 5 |
| G4 | 4 | 5148-5152 | the rule, scalar-field collapse to extremal Kerr | 5 of 5 |

In total 28 of 35 rows of G3 and 7 of 20 rows of G4 violate the ordering.

Examples:

- G3 Table 6 at 100 vertices (line 6227): L1 = 0.680, L2 = 0.315, L∞ = 0.897. Both L∞ > L1 and L1 > L2.
- G4 Table 4 at 100 vertices (line 5148): L1 = 0.256, L2 = 0.0234, L∞ = 0.435.

## Printed convergence orders (MEASURED)

Each order is recomputed as log₂ of the ratio of a norm to the norm at the next vertex count. The printed orders are therefore per doubling of the vertex count. 127 of the 132 printed orders agree with the recomputed values to ±0.01. Five differ:

| Paper | Table | Line | Vertices | Norm | Recomputed | Printed |
|---|---|---:|---:|---|---:|---:|
| G3 | 1 | 2712 | 800 | L2 | 3.13 | 3.10 |
| G3 | 5 | 4696 | 400 | L2 | 3.66 | 3.61 |
| G3 | 5 | 4697 | 800 | L2 | 3.58 | 3.62 |
| G4 | 4 | 5151 | 800 | L2 | 2.71 | 2.49 |
| G4 | 4 | 5152 | 1600 | L2 | 1.60 | 1.81 |

## Findings about the tables (READ)

- The column labelled L∞ is a volume-weighted maximum, max_i [m_i |H_i|] (G3 line 2675). The L∞ norm is max_i |H_i|. The weighted maximum decreases as the volume fractions m_i decrease, and the m_i depend on the partition.
- G3 indexes resolution by the vertex count (100 to 1600) and states no relation between the vertex count and the grid spacing. An order per doubling of the vertex count equals an order in the spacing only for a stated relation between the two. If the spacing scales as N^(−1/3), an order in the spacing is three times the printed order (OPEN: G3 does not state the relation).
- The orders of the rule's runs range from 1.11 to 2.83 in G3 Table 6 (lines 6226-6235) and from 1.44 to 2.86 in G3 Table 7 (lines 6376-6385). G3 lines 6233-6246 describe them as "approximately second-order". In G4 Tables 3-4 (lines 5131-5152) the printed orders range from 1.54 to 2.49, and the recomputed orders from 1.54 to 2.71. G4 describes them as "approximately second-order" (captions at lines 5136-5158).
- At 1600 vertices, the L1 norm of the rule's Schwarzschild head-on run is 5.29 × 10⁻³ (G3 Table 6, line 6231), and the L1 norm of the CCZ4 run of the same problem is 8.36 × 10⁻⁷ (G3 Table 4, line 4480). The ratio is 6.3 × 10³.

## Open

- Whether Tables 1-7 of G3 and Tables 1-4 of G4 were computed with norms other than those of G3 eqs. 180-181 and G4 eqs. 186-187. The code that produced the tables is not public.
