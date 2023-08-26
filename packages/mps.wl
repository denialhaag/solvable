(* ::Package:: *)

BeginPackage["mps`"];

Needs["utilities`", FileNameJoin[{"packages", "utilities.wl"}]];


T::usage = "";


Begin["`Private`"];


T[type_:"c", k_, d_, \[Chi]_, matrix_:Nothing] :=
    Which[
        type == "c",
            tc[k, d, \[Chi]]
        ,
        type == "l",
            tl[k, d, \[Chi], matrix]
        ,
        type == "r",
            tr[k, d, \[Chi], matrix]
    ]


tc[k_, d_, \[Chi]_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[
        \[Tau]], k, d * \[Chi]] * d ^ utilities`CountCycles[\[Tau], k] * d ^ utilities`CountCycles[
        \[Sigma], k] * \[Chi] ^ utilities`CountCycles[\[Sigma] \[PermutationProduct] InversePermutation[\[Theta]], k], {\[Sigma], 
        utilities`GetPermutations[k]}], {\[Tau], utilities`GetPermutations[k]}, {\[Theta],
         utilities`GetPermutations[k]}]]


tl[k_, d_, \[Chi]_, matrix_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[
        \[Tau]], k, d * \[Chi]] * Tr[Transpose[utilities`P[\[Tau], k, d]] . Nest[KroneckerProduct[
        #, matrix]&, matrix, k - 1]] * d ^ utilities`CountCycles[\[Sigma], k] * \[Chi] ^ 
        utilities`CountCycles[InversePermutation[\[Tau]], k] * \[Chi] ^ CountCycles[\[Sigma] \[PermutationProduct]
         InversePermutation[\[Theta]], k], {\[Sigma], utilities`GetPermutations[k]}, {\[Tau], utilities`GetPermutations[
        k]}], {\[Theta], utilities`GetPermutations[k]}]]


tr[k_, d_, \[Chi]_, matrix_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[
        \[Tau]], k, d * \[Chi]] * Tr[utilities`P[\[Sigma], k, d] . Nest[KroneckerProduct[#, matrix
        ]&, matrix, k - 1]] * d ^ utilities`CountCycles[\[Tau], k] * \[Chi] ^ utilities`CountCycles[
        \[Sigma], k], {\[Sigma], utilities`GetPermutations[k]}], {\[Tau], utilities`GetPermutations[
        k]}]]


End[];


EndPackage[];
