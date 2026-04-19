(* Does the rule produce a higher-dimensional causal graph when seeded
   with a 3D grid (so the spatial hypergraph is itself 3-dimensional)?

   Construct a k x k x k grid with nearest-neighbor directed edges in
   the +x, +y, +z directions. Vertex labels are tuples (i, j, k). *)

Needs["SetReplace`"];

rule = <|"PatternRules" -> {{x_, y_}, {y_, z_}, {z_, w_}, {w_, v_}} :>
        Module[{u}, {{y, u}, {u, v}, {w, x}, {x, u}}]|>;

grid3d[k_] := Flatten[Table[
  {
    If[i < k, {{i, j, l}, {i + 1, j, l}}, Nothing],
    If[j < k, {{i, j, l}, {i, j + 1, l}}, Nothing],
    If[l < k, {{i, j, l}, {i, j, l + 1}}, Nothing]
  },
  {i, k}, {j, k}, {l, k}
], 3];

measure[label_String, init_, maxEvents_] := Module[
  {wm, fs, cg, center, dists, finiteDists, maxR, nOfR, interior, rs, ns, fit},
  Print["\n--- ", label, " ---"];
  Print["  seed |E| = ", Length[init]];
  wm = WolframModel[rule, init, <|"MaxEvents" -> maxEvents|>, "AllEventsCount"];
  Print["  events fired: ", wm];
  fs = WolframModel[rule, init, <|"MaxEvents" -> maxEvents|>, "FinalState"];
  Print["  final state |E|: ", Length[fs]];
  If[!NumericQ[wm] || wm < 20, Return[]];
  cg = WolframModel[rule, init, <|"MaxEvents" -> maxEvents|>, "CausalGraph"];
  Print["  cg |V| = ", VertexCount[cg], "  |E| = ", EdgeCount[cg]];
  center = First[VertexList[cg]];
  dists = GraphDistance[cg, center, #] & /@ VertexList[cg];
  finiteDists = Select[dists, NumericQ[#] && # < Infinity &];
  maxR = If[Length[finiteDists] > 0, Max[finiteDists], 0];
  Print["  max cone distance: ", maxR];
  If[maxR < 4, Return[]];
  nOfR = Table[{r, Length[Select[finiteDists, # <= r &]]}, {r, 1, maxR}];
  Print["  (r, C(r)) first 15: ", Take[nOfR, UpTo[15]]];
  interior = Select[nOfR, Floor[maxR / 4] <= First[#] <= Floor[3 maxR / 4] &];
  If[Length[interior] >= 3,
    rs = First /@ interior;
    ns = Last /@ interior;
    fit = LinearModelFit[Transpose[{Log[N[rs]], Log[N[ns]]}], x, x];
    Print["  fit: log C(r) ~ ", N[fit["BestFitParameters"][[1]]],
          " + ", N[fit["BestFitParameters"][[2]]], " log r"];
    Print["  => cone dimension ≈ ", N[fit["BestFitParameters"][[2]]]];
  ];
];

measure["3x3x3 grid, 300 events", grid3d[3], 300];
measure["4x4x4 grid, 1000 events", grid3d[4], 1000];
measure["5x5x5 grid, 2000 events", grid3d[5], 2000];
