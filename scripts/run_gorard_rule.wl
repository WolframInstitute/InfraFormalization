(* Empirical test of the rule Gorard (2102.09363, line 6202) names as
   "provably satisfying the Einstein field equations in the continuum
   limit." We check: (1) does it even evolve? (2) how does the spatial
   hypergraph grow? (3) what does the causal graph look like? (4) does
   the dimension converge? (5) is the causal-graph cone-growth anywhere
   near what Gorard's §3.2 formulas would require for GR? *)

Needs["SetReplace`"];

(* The rule. Signature: 4 binary edges -> 4 binary edges. Introduces 1
   fresh vertex u on RHS. *)
rule = {{x_, y_}, {y_, z_}, {z_, w_}, {w_, v_}} :>
        Module[{u}, {{y, u}, {u, v}, {w, x}, {x, u}}];

(* Initial condition: a small seed graph with enough structure to match.
   Try the 4-cycle as the canonical initial state. *)
init = {{1, 2}, {2, 3}, {3, 4}, {4, 1}};

Print["=== Rule ==="];
Print[rule];
Print["Initial: ", init];

(* Generate single history up to some number of events. *)
maxEvents = 2000;
Print["\n=== Generating history with MaxEvents -> ", maxEvents, " ==="];
mh = GenerateSingleHistory[
   MultisetSubstitutionSystem[
     {{x_, y_}, {y_, z_}, {z_, w_}, {w_, v_}} :>
     Module[{u}, {{y, u}, {u, v}, {w, x}, {x, u}}]
   ],
   MaxEvents -> maxEvents
][init];

Print["Total events generated: ", EventCount[mh]];
Print["Final state atom count: ", AtomCount[mh]];
Print["Final state expression count: ", StateExpressionCount[mh]];

(* Causal graph *)
cg = mh["CausalGraph"];
Print["\n=== Causal graph ==="];
Print["Causal graph vertex count: ", VertexCount[cg]];
Print["Causal graph edge count: ", EdgeCount[cg]];

(* Count outgoing/incoming edges distribution. *)
outDegs = VertexOutDegree[cg];
inDegs = VertexInDegree[cg];
Print["Out-degree stats (min/mean/max): ", {Min[outDegs], N[Mean[outDegs]], Max[outDegs]}];
Print["In-degree stats  (min/mean/max): ", {Min[inDegs], N[Mean[inDegs]], Max[inDegs]}];

(* Dimension estimate: N(r) = number of causal-graph vertices within
   graph distance r of a chosen vertex. For a Riemannian analog, this
   should grow as r^n asymptotically. Gorard's §3.2 needs a well-defined
   n. We pick the "middle" event as the center. *)
n = VertexCount[cg];
center = Ceiling[n / 2];
Print["\n=== Dimensionality check ==="];
dists = GraphDistance[cg, center, All];
finiteDists = Select[dists, # < Infinity &];
maxR = If[Length[finiteDists] > 0, Max[finiteDists], 0];
Print["Max finite graph distance from center: ", maxR];
If[maxR >= 3,
  nOfR = Table[{r, Length[Select[finiteDists, # <= r &]]}, {r, 1, maxR}];
  Print["First several (r, N(r)): ", Take[nOfR, UpTo[15]]];
  (* Fit N(r) = a*r^d on the interior range. *)
  interior = Select[nOfR, 2 <= First[#] <= Max[3, Floor[maxR * 0.7]] &];
  If[Length[interior] >= 3,
    rs = First /@ interior;
    ns = Last /@ interior;
    logFit = LinearModelFit[Log[{rs, ns}\[Transpose]], x, x];
    Print["log N(r) ~ a + d log r, fit: ", Normal[logFit]];
    Print["Estimated dimension d = ", logFit["BestFitParameters"][[2]]];
  ];
];

(* NB: SetReplace is primarily single-way, so causal invariance cannot be
   checked by enumerating branches from inside this run. The absence of a
   multi-branch falsification here does NOT confirm causal invariance —
   it merely says the canonical single-history did not diverge in an
   observable way. *)

Print["\n=== Done ==="];
