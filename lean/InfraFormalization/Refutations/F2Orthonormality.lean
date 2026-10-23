/-
**F2: the JGORARD G1 §3.2 "all non-parallel hyperedges are orthonormal"
fiat assumption is vacuous / non-canonical.**

**Context.** arXiv:2004.14810 line 840 states, verbatim:

  "We also assume that all pairs of hyperedges which are not parallel
   (i.e. incident to the same set of vertices) can be considered to be
   orthonormal."

Orthonormality is a property of a bilinear form: two vectors `u, v` are
orthonormal w.r.t. `g` iff `g(u,u) = g(v,v) = 1 ∧ g(u,v) = 0`. JGORARD
uses this fiat claim to propagate Riemannian-geometry formulas (Gauss
curvature, Ricci, sectional curvature) onto the hypergraph side.

**The structural issue.** `g^{ab}` itself is never constructed (see F1).
Even granting *some* bilinear form `g` on the hyperedge set, the
demand "all non-parallel hyperedges are orthonormal" is extremely
restrictive and in general has no solution — imposing it on a generic
hyperedge set produces an over-determined linear system. Conversely,
if one is *free* to choose `g`, then the statement carries no
geometric content: any proposition about the hyperedges can be made
true by a sufficiently accommodating `g`.

**What this file proves.** Two facts about real-valued functions on
`Bool × Bool`:

1. `orthonormality_depends_on_form`: one function makes the pair
   `(true, false)` orthonormal and another does not.

2. `orthonormalising_form_not_unique`: two distinct functions both make
   the pair `(true, false)` orthonormal.

Neither theorem mentions arXiv:2004.14810. The finding about the paper,
that line 840 asserts orthonormality without defining a bilinear form,
is a reading of the paper text and is not a Lean theorem.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace InfraFormalization
namespace Refutations

/-- An abstract "bilinear form on hyperedges": a binary function
`g : E → E → ℝ`. We do not require bilinearity in any strict sense —
the weakest interpretation of JGORARD's `g^{ab}`. -/
abbrev Form (E : Type*) : Type _ := E → E → ℝ

/-- Orthonormality of a pair `(e₁, e₂) : E × E` with respect to a
form `g`: both have unit self-inner-product, and mutual inner-product
is zero. -/
def Orthonormal {E : Type*} (g : Form E) (e₁ e₂ : E) : Prop :=
  g e₁ e₁ = 1 ∧ g e₂ e₂ = 1 ∧ g e₁ e₂ = 0

/-- **F2 Lean statement, part 1.** Orthonormality is a property of
the form, not of the hyperedges alone. Take `E := Bool`,
`e₁ := true`, `e₂ := false`. `g₁ : Form Bool` can be chosen with
`g₁ true true = g₁ false false = 1` and `g₁ true false = g₁ false true = 0`
(standard Euclidean on `ℝ²`) — giving orthonormality. `g₂ : Form Bool`
identically zero fails orthonormality. So "the hyperedges are
orthonormal" is not a property of the hyperedges without specifying `g`. -/
theorem orthonormality_depends_on_form :
    ∃ (g₁ g₂ : Form Bool),
      Orthonormal g₁ true false ∧ ¬ Orthonormal g₂ true false := by
  refine ⟨(fun a b => if a = b then 1 else 0), (fun _ _ => 0), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp
    · simp
    · simp
  · rintro ⟨h, _, _⟩
    simp at h

/-- **F2 Lean statement, part 2.** The orthonormality-imposing form
is not unique: for any hyperedge set with at least two non-parallel
hyperedges, there exist multiple distinct forms making the pair
orthonormal. Thus "the orthonormal form of the hypergraph" is a
non-canonical choice. -/
theorem orthonormalising_form_not_unique :
    ∃ (g₁ g₂ : Form Bool),
      g₁ ≠ g₂ ∧
      Orthonormal g₁ true false ∧
      Orthonormal g₂ true false := by
  refine
    ⟨(fun a b => if a = b then 1 else 0),
     (fun a b =>
        if a = b then 1
        else if a = false ∧ b = true then 7
        else 0), ?_, ?_, ?_⟩
  · intro h
    have hv := congrFun (congrFun h false) true
    simp at hv
  · refine ⟨?_, ?_, ?_⟩ <;> simp
  · refine ⟨?_, ?_, ?_⟩ <;> simp

end Refutations
end InfraFormalization
