(* Figure out the right SetReplace API for extracting event count,
   termination reason, and expressions from a Multihistory. *)

Needs["SetReplace`"];

rule = {{x_, y_}, {y_, z_}, {z_, w_}, {w_, v_}} :>
        Module[{u}, {{y, u}, {u, v}, {w, x}, {x, u}}];

init = {{1, 2}, {2, 3}, {3, 4}, {4, 5}};

mh = GenerateSingleHistory[
  MultisetSubstitutionSystem[rule], MaxEvents -> 10
][init];

Print["Head: ", Head[mh]];
Print["Applied to 'Properties' / 'properties':"];
Print["  mh['Properties'] -> ", mh["Properties"]];

Print["\nAvailable top-level event extractors:"];
Print["  EventCount[mh]      -> ", EventCount[mh]];
Print["  AtomCount[mh]       -> ", AtomCount[mh]];
Print["  StateExpressionCount[mh] -> ", StateExpressionCount[mh]];
Print["  MaxCompleteGeneration[mh] -> ", MaxCompleteGeneration[mh]];
Print["  MaxGeneration[mh]   -> ", MaxGeneration[mh]];
Print["  MaxEvents[mh]       -> ", MaxEvents[mh]];

Print["\nTry extraction via [[]] / Normal / Association:"];
Print["  Normal[mh]:"];
norm = Normal[mh];
Print["    Head[Normal[mh]] = ", Head[norm]];
If[AssociationQ[norm] || Head[norm] === Association,
  Print["    Keys = ", Keys[norm]];
  Print["    TerminationReason = ", norm["TerminationReason"]];
  Print["    EventInputs as list = ", Normal[norm["EventInputs"]]];
  Print["    Expressions as list = ", Normal[norm["Expressions"]]];
];
