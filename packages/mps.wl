(* ::Package:: *)

BeginPackage["mps`"];

Needs["utilities`", FileNameJoin[{"packages", "utilities.wl"}]];


P::usage = "";

T::usage = "";


Begin["`Private`"];


P[\[Alpha]_, k_, q_] :=
    Sum[ket = Table[KroneckerDelta[FromDigits[Permute[PadLeft[IntegerDigits[
        i, q], k], InversePermutation[\[Alpha]]], q], j], {j, 0, q^k - 1}]; bra = Table[
        KroneckerDelta[i, j], {j, 0, q^k - 1}]; KroneckerProduct[ket, bra], {
        i, 0, q^k - 1}]


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
    FullSimplify[Table[Sum[Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Tau]], k, d
         * \[Chi]] * d ^ CountCycles[\[Tau], k] * d ^ CountCycles[\[Sigma], k] * \[Chi] ^ CountCycles[
        \[Sigma] \[PermutationProduct] InversePermutation[\[Theta]], k], {\[Sigma], GetPerms[k]}], {\[Tau], GetPerms[k]}, {
        \[Theta], GetPerms[k]}]]


tl[k_, d_, \[Chi]_, matrix_] :=
    FullSimplify[Table[Sum[Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Tau]], k, d
         * \[Chi]] * Tr[Transpose[P[\[Tau], k, d]] . Nest[KroneckerProduct[#, matrix]&,
         matrix, k - 1]] * d ^ CountCycles[\[Sigma], k] * \[Chi] ^ CountCycles[InversePermutation[
        \[Tau]], k] * \[Chi] ^ CountCycles[\[Sigma] \[PermutationProduct] InversePermutation[\[Theta]], k], {\[Sigma], GetPerms[
        k]}, {\[Tau], GetPerms[k]}], {\[Theta], GetPerms[k]}]]


tr[k_, d_, \[Chi]_, matrix_] :=
    FullSimplify[Table[Sum[Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Tau]], k, d
         * \[Chi]] * Tr[P[\[Sigma], k, d] . Nest[KroneckerProduct[#, matrix]&, matrix, k 
        - 1]] * d ^ CountCycles[\[Tau], k] * \[Chi] ^ CountCycles[\[Sigma], k], {\[Sigma], GetPerms[k
        ]}], {\[Tau], GetPerms[k]}]]


End[];


EndPackage[];
