(* v2: correct the API (use indexing on the Multihistory object, not
   top-level EventCount etc), and try several initial conditions.
   Focus question: does Gorard's named "EFE-satisfying" rule actually
   evolve nontrivially from simple seeds? *)

Needs["SetReplace`"];

rule = {{x_, y_}, {y_, z_}, {z_, w_}, {w_, v_}} :>
        Module[{u}, {{y, u}, {u, v}, {w, x}, {x, u}}];

runOne[label_String, init_, maxEvents_] := Module[
  {mh, events, expr, inputs, outputs},
  Print["\n--- ", label, " ---"];
  Print["Initial: ", init];
  mh = GenerateSingleHistory[
    MultisetSubstitutionSystem[rule], MaxEvents -> maxEvents
  ][init];
  inputs = mh["EventInputs"];
  outputs = mh["EventOutputs"];
  expr = mh["Expressions"];
  (* Event 0 is the virtual "initial state" event. Real events are >= 1. *)
  events = Length[inputs] - 1;
  Print["  Real rule firings: ", events];
  Print["  Final expression count: ", Length[expr]];
  If[events <= 3,
    Print["  Final state: ", expr]
  ];
  events
];

(* Seed 1: the directed 4-cycle. Should match LHS once, then die. *)
runOne["4-cycle seed {{1,2},{2,3},{3,4},{4,1}}",
  {{1, 2}, {2, 3}, {3, 4}, {4, 1}}, 100];

(* Seed 2: a longer directed path. *)
runOne["5-path seed {{1,2},{2,3},{3,4},{4,5}}",
  {{1, 2}, {2, 3}, {3, 4}, {4, 5}}, 100];

(* Seed 3: 8-cycle — two overlapping windows initially. *)
runOne["8-cycle seed",
  Table[{i, Mod[i, 8] + 1}, {i, 8}], 500];

(* Seed 4: a complete graph on 4 vertices (all 12 directed edges) — lots
   of chains to match. *)
runOne["complete digraph K4 (12 edges)",
  Flatten[Table[{i, j}, {i, 4}, {j, 4}], 1] /. {i_, i_} :> Nothing, 500];

(* Seed 5: two disjoint 4-cycles. *)
runOne["two disjoint 4-cycles",
  Join[
    Table[{i, Mod[i, 4] + 1}, {i, 4}],
    Table[{i + 4, Mod[i, 4] + 5}, {i, 4}]
  ], 200];

(* Seed 6: the canonical Wolfram-model "particle-ring" initial seed
   sometimes used in Wolfram's talks: a 6-cycle. *)
runOne["6-cycle seed",
  Table[{i, Mod[i, 6] + 1}, {i, 6}], 300];

(* Seed 7: 2 copies of a 6-cycle, sharing a vertex. *)
runOne["figure-8 (two 6-cycles sharing one vertex)",
  Join[
    Table[{i, Mod[i, 6] + 1}, {i, 6}],
    Table[{i + 6, Mod[i, 6] + 7}, {i, 6}],
    {{1, 7}}
  ], 400];

Print["\n=== summary ==="];
Print["Rule: ", rule];
Print["Observation: how long does the evolution run from each seed?"];
