/-
Two maps of type `PoissonBracket V` and two hypergraph functions.

This module defines the zero bracket and the difference bracket
`{f, g}(H) = f H − g H`, and proves both satisfy `IsAntisymmetric`. It also
defines the vertex-count function, which depends only on `V`, and the
edge-count function, and proves elementary facts about them. Neither
bracket is shown to satisfy the Jacobi identity.
-/

import InfraFormalization.BlowupLieAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace InfraFormalization

/-- The bracket `{f, g} := 0`. -/
def zeroPoissonBracket (V : Type*) : PoissonBracket V :=
  fun _ _ _ => 0

/-- The zero bracket satisfies `IsAntisymmetric`. -/
theorem zeroPoissonBracket_antisymm (V : Type*) :
    (zeroPoissonBracket V).IsAntisymmetric := by
  intros f g H
  unfold zeroPoissonBracket
  ring

/-- The number of hyperedges of a hypergraph, as a real number. -/
noncomputable def edgeCountFn {V : Type*} : Hypergraph V → ℝ :=
  fun H => (Multiset.card H.edges : ℝ)

/-- The empty hypergraph has edge count 0. -/
theorem edgeCountFn_empty (V : Type*) :
    edgeCountFn (Hypergraph.empty : Hypergraph V) = 0 := by
  unfold edgeCountFn Hypergraph.empty
  simp

/-- The edge count is non-negative. -/
theorem edgeCountFn_nonneg {V : Type*} (H : Hypergraph V) :
    0 ≤ edgeCountFn H := by
  unfold edgeCountFn
  positivity

/-- The bracket `{f, g}(H) := f H − g H`. -/
def differencePoissonBracket (V : Type*) : PoissonBracket V :=
  fun f g H => f H - g H

/-- The difference bracket satisfies `{f, g}(H) = -{g, f}(H)`. -/
theorem differencePoissonBracket_antisymm (V : Type*) :
    (differencePoissonBracket V).IsAntisymmetric := by
  intros f g H
  unfold differencePoissonBracket
  ring

end InfraFormalization
