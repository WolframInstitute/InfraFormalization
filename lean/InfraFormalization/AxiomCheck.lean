/-
Axiom-cleanliness check.

`#print axioms T` prints the axioms a theorem depends on. For any
proof we want to certify as purely constructive, the output should
contain only Lean's three standard axioms:
  propext, Quot.sound, Classical.choice
(we use Classical.choice implicitly via `Decidable.decide` in some
places; for the linear-arithmetic proofs here we stay in the `omega`
decision procedure which does not touch it.)

Never acceptable:
  sorryAx, lcProof
(these indicate `sorry` or `native_decide` respectively.)
-/

import InfraFormalization.Demo
import InfraFormalization.Growth
import InfraFormalization.ParallelSchedule
import InfraFormalization.Infra.ScaledCycle
import InfraFormalization.Infra.LatticeDensity
import InfraFormalization.Infra.Circle
import InfraFormalization.Infra.GHBound

#print axioms InfraFormalization.edge_conservation
#print axioms InfraFormalization.trajectory_preserves_size
#print axioms InfraFormalization.Application.size_result_of_conservative
#print axioms InfraFormalization.size_preserved_by_applications
#print axioms InfraFormalization.growthExponentAtMost_of_linear
#print axioms InfraFormalization.in_degree_eq_lhsSize
#print axioms InfraFormalization.out_degree_eq_rhsSize
#print axioms InfraFormalization.balanced_of_conservative
#print axioms InfraFormalization.Infra.cycleDist_self
#print axioms InfraFormalization.Infra.cycleDist_symm
#print axioms InfraFormalization.Infra.cycleDist_le_half
#print axioms InfraFormalization.Infra.cycleDist_zero_of_small
#print axioms InfraFormalization.Infra.cycleDist_triangle
#print axioms InfraFormalization.Infra.cycleDist_eq_zero_iff
#print axioms InfraFormalization.Infra.exists_lattice_index
#print axioms InfraFormalization.Infra.lattice_one_over_n_dense
#print axioms InfraFormalization.Infra.lattice_half_n_cover
#print axioms InfraFormalization.Infra.circleDist_self
#print axioms InfraFormalization.Infra.circleDist_symm
#print axioms InfraFormalization.Infra.circleDist_nonneg
#print axioms InfraFormalization.Infra.circleDist_le_half
#print axioms InfraFormalization.Infra.latticeEmbed_mem_unit_interval
#print axioms InfraFormalization.Infra.latticeEmbed_covers
#print axioms InfraFormalization.Infra.latticeEmbed_isometry
#print axioms InfraFormalization.Infra.cycle_circle_gh_bound
#print axioms InfraFormalization.Infra.cycle_circle_eventual_epsilon_dense
