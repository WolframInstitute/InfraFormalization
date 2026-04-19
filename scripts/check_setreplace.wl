(* Check SetReplace availability and list available paclets *)
Print["Wolfram version: ", $VersionNumber];
Print["PacletFind SetReplace: ", PacletFind["SetReplace"]];
Print["SetReplace paclet info:"];
Needs["SetReplace`"];
Print["SetReplace loaded OK."];
Print["Available symbols (partial): ", Take[Names["SetReplace`*"], UpTo[20]]];
