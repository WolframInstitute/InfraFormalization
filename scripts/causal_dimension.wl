(* For the seeds where the rule keeps running, measure causal-graph
   cone growth C(t) = |{event e' : graph-distance from some fixed
   source <= t}|. If C(t) ~ a t^n for some n, that's the causal-graph
   dimension. For Gorard's §3.3 to apply, we'd want n close to 4 for
   anything resembling 3+1-dim spacetime. *)

Needs["SetReplace`"];

rule = <|"PatternRules" -> {{x_, y_}, {y_, z_}, {z_, w_}, {w_, v_}} :>
        Module[{u}, {{y, u}, {u, v}, {w, x}, {x, u}}]|>;

measureCausalDim[label_String, init_, maxEvents_] := Module[
  {cg, center, dists, finiteDists, maxR, nOfR, interior, rs, ns, fit},
  Print["\n--- ", label, " ---"];
  cg = WolframModel[rule, init, <|"MaxEvents" -> maxEvents|>, "CausalGraph"];
  Print["  cg vertex count: ", VertexCount[cg], "  edge count: ", EdgeCount[cg]];
  If[VertexCount[cg] < 20, Print["  too few events, skipping dimension fit"]; Return[]];
  (* Use the first event as source. GraphDistanceMatrix row gives all
     distances from that vertex. *)
  center = First[VertexList[cg]];
  dists = GraphDistance[cg, center, #] & /@ VertexList[cg];
  finiteDists = Select[dists, NumericQ[#] && # < Infinity &];
  maxR = If[Length[finiteDists] > 0, Max[finiteDists], 0];
  Print["  max out-distance from vertex ", center, ": ", maxR];
  If[maxR < 4, Return[]];
  nOfR = Table[{r, Length[Select[finiteDists, # <= r &]]}, {r, 1, maxR}];
  Print["  (r, C(r)) first 20: ", Take[nOfR, UpTo[20]]];
  (* Log-log fit in the middle portion. *)
  interior = Select[nOfR, (maxR / 4) <= First[#] <= (3 maxR / 4) &];
  If[Length[interior] >= 3,
    rs = First /@ interior;
    ns = Last /@ interior;
    fit = LinearModelFit[Transpose[{Log[rs], Log[ns]}], x, x];
    Print["  log-log fit: log C(r) ~ ", N[fit["BestFitParameters"][[1]]],
          " + ", N[fit["BestFitParameters"][[2]]], " * log r"];
    Print["  => causal-graph cone dimension ≈ ", N[fit["BestFitParameters"][[2]]]];
  ];
];

measureCausalDim["6-cycle, 500 events",  Table[{i, Mod[i, 6] + 1}, {i, 6}], 500];
measureCausalDim["6-cycle, 2000 events", Table[{i, Mod[i, 6] + 1}, {i, 6}], 2000];
measureCausalDim["8-cycle, 500 events",  Table[{i, Mod[i, 8] + 1}, {i, 8}], 500];
measureCausalDim["20-cycle, 1000 events", Table[{i, Mod[i, 20] + 1}, {i, 20}], 1000];
measureCausalDim["10-path, 500 events",  Table[{i, i + 1}, {i, 10}], 500];
