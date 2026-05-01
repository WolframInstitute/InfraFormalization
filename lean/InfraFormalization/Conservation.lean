/-
The Edge Conservation Theorem.

**Statement.** If a rewrite rule `r` is conservative (its LHS and RHS
have the same number of hyperedges), then every application of `r`
preserves the size of the state.

This is Theorem A of the project's verified-results track. It is the
structural fact that drives the empirical refutation of the
"EFE-satisfying" rule in arXiv:2102.09363: the rule has `|LHS| = |RHS|
= 4`, so the spatial hypergraph size is a conserved quantity — it
cannot grow as $r^d$ for any $d > 0$, which is a necessary condition for
JGORARD's §3.3 continuum-Einstein argument to even begin.
-/

import InfraFormalization.Application
import Mathlib.Data.Multiset.Basic

namespace InfraFormalization

open Hypergraph Application

variable {P V : Type*} [DecidableEq V] {r : Rule P} {H : Hypergraph V}

/-- **Edge Conservation Theorem.** For a conservative rule, every
application preserves the state size. -/
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

/-- Corollary: iterating any finite list of conservative applications
never changes the state size, given that the starting application's
input is `H₀` and subsequent applications chain through the `.result`
of the previous one. Reformulated to avoid dependent-type gymnastics:
we state the corollary on a list of applications (so there's no
separate "state" list). -/
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
