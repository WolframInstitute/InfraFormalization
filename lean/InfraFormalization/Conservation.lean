/-
Edge-count conservation.

If a rule has as many hyperedges on its right-hand side as on its left
(`Rule.IsConservative`), every application preserves the number of
hyperedges of the state (`Application.size_result_of_conservative`), and
so does every chain of applications (`size_preserved_by_applications`).
-/

import InfraFormalization.Application
import Mathlib.Data.Multiset.Basic

namespace InfraFormalization

open Hypergraph Application

variable {P V : Type*} [DecidableEq V] {r : Rule P} {H : Hypergraph V}

/-- For a conservative rule, every application leaves the number of
hyperedges unchanged. -/
theorem Application.size_result_of_conservative
    (a : Application r H) (hcons : r.IsConservative) :
    a.result.size = H.size := by
  have hsub : a.consumed ≤ H.edges := a.lhs_embedded
  have hle : a.consumed.card ≤ H.edges.card := Multiset.card_le_card hsub
  have hc : a.consumed.card = r.lhsSize := by simp [Application.consumed_card]
  have hp : a.produced.card = r.rhsSize := by simp [Application.produced_card]
  show ((H.edges - a.consumed) + a.produced).card = H.edges.card
  rw [Multiset.card_add, Multiset.card_sub hsub, hc, hp]
  -- Goal: H.edges.card - r.lhsSize + r.rhsSize = H.edges.card
  -- Conservation says r.lhsSize = r.rhsSize, and r.lhsSize ≤ H.edges.card
  unfold Rule.IsConservative at hcons
  have hlerw : r.lhsSize ≤ H.edges.card := hc ▸ hle
  omega

/-- Let `as` be a list of applications of a conservative rule whose first
input is `H₀` and in which each input is the result of the previous
application. Then every input in the list has the same number of hyperedges
as `H₀`. -/
theorem size_preserved_by_applications
    (hcons : r.IsConservative)
    (H₀ : Hypergraph V)
    (as : List (Σ H : Hypergraph V, Application r H))
    (hfirst : ∀ (h : as ≠ []), (as.head h).1 = H₀)
    (hchain : ∀ i (hi : i + 1 < as.length),
      (as.get ⟨i + 1, hi⟩).1 = (as.get ⟨i, Nat.lt_of_succ_lt hi⟩).2.result) :
    ∀ i (hi : i < as.length), (as.get ⟨i, hi⟩).1.size = H₀.size := by
  intro i
  induction i with
  | zero =>
    intro hi
    -- Goal: (as.get ⟨0, hi⟩).1.size = H₀.size.
    -- Since hi says 0 < as.length, as ≠ [], so as.head = (as.get ⟨0, hi⟩).1.
    have hne : as ≠ [] := by
      intro h
      rw [h] at hi
      exact Nat.not_lt_zero 0 hi
    have h_head : (as.head hne).1 = H₀ := hfirst hne
    -- Connect list.head to list.get at index 0:
    have heq : (as.get ⟨0, hi⟩).1 = (as.head hne).1 := by
      cases as with
      | nil => exact absurd rfl hne
      | cons first rest => simp [List.get, List.head]
    rw [heq, h_head]
  | succ i ih =>
    intro hi
    have hi' : i < as.length := Nat.lt_of_succ_lt hi
    have step_eq := hchain i hi
    rw [show (as.get ⟨i + 1, hi⟩).1 = (as.get ⟨i, hi'⟩).2.result from step_eq]
    rw [(as.get ⟨i, hi'⟩).2.size_result_of_conservative hcons]
    exact ih hi'

end InfraFormalization
