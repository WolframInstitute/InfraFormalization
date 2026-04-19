/-
Branchial structure — placeholder.

Gorard's notion of branchial graph is defined in the quantum companion
paper to arXiv:2004.14810 (not one of the three we audit here). We
leave a type-level placeholder so downstream modules can reference the
notion without a committed construction.
-/

import InfraFormalization.Multiway

namespace InfraFormalization

/-- Placeholder type-level interface for branchial structure. -/
structure BranchialStructure (V : Type*) where
  Slice : Type*
  sliceOf : Hypergraph V → Slice

end InfraFormalization
