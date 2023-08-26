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
        type == "bl",
            tbl[k, d, \[Chi]]
        ,
        type == "b",
            tb[k, d, \[Chi]]
        ,
        type == "br",
            tbr[k, d, \[Chi]]
        ,
        type == "r",
            tr[k, d, \[Chi], matrix]
        ,
        type == "tr",
            ttr[k, d, \[Chi]]
        ,
        type == "t",
            tt[k, d, \[Chi]]
        ,
        type == "tl",
            ttl[k, d, \[Chi]]
    ]


tc[k_, d_, \[Chi]_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Beta] \[PermutationProduct] InversePermutation[
        \[Alpha]], k, d * \[Chi]] * utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Gamma]], k, d 
        * \[Chi]] * d ^ utilities`CountCycles[\[Alpha], k] * d ^ utilities`CountCycles[\[Sigma],
         k] * d ^ utilities`CountCycles[\[Beta] \[PermutationProduct] InversePermutation[\[Gamma]], k] * \[Chi] ^ utilities`CountCycles[
        \[Sigma] \[PermutationProduct] InversePermutation[\[Delta]], k] * \[Chi] ^ (utilities`CountCycles[\[Beta] \[PermutationProduct] InversePermutation[
        \[Zeta]], k] / 2) * \[Chi] ^ (utilities`CountCycles[\[Epsilon] \[PermutationProduct] InversePermutation[\[Gamma]], k
        ] / 2), {\[Sigma], utilities`GetPermutations[k]}], {\[Alpha], utilities`GetPermutations[
        k]}, {\[Beta], utilities`GetPermutations[k]}, {\[Gamma], utilities`GetPermutations[
        k]}, {\[Delta], utilities`GetPermutations[k]}, {\[Epsilon], utilities`GetPermutations[
        k]}, {\[Zeta], utilities`GetPermutations[k]}]]


tl[k_, d_, \[Chi]_, matrix_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Beta] \[PermutationProduct] InversePermutation[
        \[Alpha]], k, d * \[Chi]] * utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Gamma]], k, d 
        * \[Chi]] * Tr[Transpose[utilities`P[\[Alpha], k, d]] . Nest[KroneckerProduct[#, 
        matrix]&, matrix, k - 1]] * d ^ utilities`CountCycles[\[Sigma], k] * d ^ utilities`CountCycles[
        \[Beta] \[PermutationProduct] InversePermutation[\[Gamma]], k] * \[Chi] ^ utilities`CountCycles[\[Alpha], k] * \[Chi] ^
         utilities`CountCycles[\[Sigma] \[PermutationProduct] InversePermutation[\[Delta]], k] * \[Chi] ^ (utilities`CountCycles[
        \[Beta] \[PermutationProduct] InversePermutation[\[Zeta]], k] / 2) * \[Chi] ^ (utilities`CountCycles[\[Epsilon] \[PermutationProduct] InversePermutation[
        \[Gamma]], k] / 2), {\[Alpha], utilities`GetPermutations[k]}, {\[Sigma], utilities`GetPermutations[
        k]}], {\[Beta], utilities`GetPermutations[k]}, {\[Gamma], utilities`GetPermutations[
        k]}, {\[Delta], utilities`GetPermutations[k]}, {\[Epsilon], utilities`GetPermutations[
        k]}, {\[Zeta], utilities`GetPermutations[k]}]]


tbl[k_, d_, \[Chi]_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Beta] \[PermutationProduct] InversePermutation[
        \[Alpha]], k, d * \[Chi]] * utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Gamma]], k, d 
        * \[Chi]] * d ^ utilities`CountCycles[\[Alpha], k] * d ^ utilities`CountCycles[\[Sigma],
         k] * d ^ utilities`CountCycles[\[Beta] \[PermutationProduct] InversePermutation[\[Gamma]], k] * \[Chi] ^ utilities`CountCycles[
        \[Alpha], k] * \[Chi] ^ utilities`CountCycles[\[Sigma] \[PermutationProduct] InversePermutation[\[Delta]], k] * \[Chi] ^
         (utilities`CountCycles[\[Beta], k] / 2) * \[Chi] ^ (utilities`CountCycles[\[Gamma], k]
         / 2) * \[Chi] ^ (utilities`CountCycles[\[Beta] \[PermutationProduct] InversePermutation[\[Zeta]], k] / 2)
         * \[Chi] ^ (utilities`CountCycles[\[Epsilon] \[PermutationProduct] InversePermutation[\[Gamma]], k] / 2), {\[Alpha],
         utilities`GetPermutations[k]}, {\[Beta], utilities`GetPermutations[k]}, {\[Gamma],
         utilities`GetPermutations[k]}, {\[Sigma], utilities`GetPermutations[k]}], {
        \[Delta], utilities`GetPermutations[k]}, {\[Epsilon], utilities`GetPermutations[k]}, 
        {\[Zeta], utilities`GetPermutations[k]}]]


tb[k_, d_, \[Chi]_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Beta] \[PermutationProduct] InversePermutation[
        \[Alpha]], k, d * \[Chi]] * utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Gamma]], k, d 
        * \[Chi]] * d ^ utilities`CountCycles[\[Alpha], k] * d ^ utilities`CountCycles[\[Sigma],
         k] * d ^ utilities`CountCycles[\[Beta] \[PermutationProduct] InversePermutation[\[Gamma]], k] * \[Chi] ^ utilities`CountCycles[
        \[Sigma] \[PermutationProduct] InversePermutation[\[Delta]], k] * \[Chi] ^ (utilities`CountCycles[\[Beta], k] / 2)
         * \[Chi] ^ (utilities`CountCycles[\[Gamma], k] / 2) * \[Chi] ^ (utilities`CountCycles[
        \[Beta] \[PermutationProduct] InversePermutation[\[Zeta]], k] / 2) * \[Chi] ^ (utilities`CountCycles[\[Epsilon] \[PermutationProduct] InversePermutation[
        \[Gamma]], k] / 2), {\[Beta], utilities`GetPermutations[k]}, {\[Gamma], utilities`GetPermutations[
        k]}, {\[Sigma], utilities`GetPermutations[k]}], {\[Alpha], utilities`GetPermutations[
        k]}, {\[Delta], utilities`GetPermutations[k]}, {\[Epsilon], utilities`GetPermutations[
        k]}, {\[Zeta], utilities`GetPermutations[k]}]]


tbr[k_, d_, \[Chi]_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Beta] \[PermutationProduct] InversePermutation[
        \[Alpha]], k, d * \[Chi]] * utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Gamma]], k, d 
        * \[Chi]] * d ^ utilities`CountCycles[\[Alpha], k] * d ^ utilities`CountCycles[\[Sigma],
         k] * d ^ utilities`CountCycles[\[Beta] \[PermutationProduct] InversePermutation[\[Gamma]], k] * \[Chi] ^ utilities`CountCycles[
        \[Sigma], k] * \[Chi] ^ (utilities`CountCycles[\[Beta], k] / 2) * \[Chi] ^ (utilities`CountCycles[
        \[Gamma], k] / 2) * \[Chi] ^ (utilities`CountCycles[\[Beta] \[PermutationProduct] InversePermutation[\[Zeta]], k]
         / 2) * \[Chi] ^ (utilities`CountCycles[\[Epsilon] \[PermutationProduct] InversePermutation[\[Gamma]], k] / 2),
         {\[Beta], utilities`GetPermutations[k]}, {\[Gamma], utilities`GetPermutations[k]},
         {\[Sigma], utilities`GetPermutations[k]}], {\[Alpha], utilities`GetPermutations[k]
        }, {\[Epsilon], utilities`GetPermutations[k]}, {\[Zeta], utilities`GetPermutations[k
        ]}]]


tr[k_, d_, \[Chi]_, matrix_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Beta] \[PermutationProduct] InversePermutation[
        \[Alpha]], k, d * \[Chi]] * utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Gamma]], k, d 
        * \[Chi]] * Tr[utilities`P[\[Sigma], k, d] . Nest[KroneckerProduct[#, matrix]&, matrix,
         k - 1]] * d ^ utilities`CountCycles[\[Alpha], k] * d ^ utilities`CountCycles[
        \[Beta] \[PermutationProduct] InversePermutation[\[Gamma]], k] * \[Chi] ^ utilities`CountCycles[\[Sigma], k] * \[Chi] ^
         (utilities`CountCycles[\[Beta] \[PermutationProduct] InversePermutation[\[Zeta]], k] / 2) * \[Chi] ^ (utilities`CountCycles[
        \[Epsilon] \[PermutationProduct] InversePermutation[\[Gamma]], k] / 2), {\[Sigma], utilities`GetPermutations[k]}
        ], {\[Alpha], utilities`GetPermutations[k]}, {\[Beta], utilities`GetPermutations[k
        ]}, {\[Gamma], utilities`GetPermutations[k]}, {\[Epsilon], utilities`GetPermutations[
        k]}, {\[Zeta], utilities`GetPermutations[k]}]]


ttr[k_, d_, \[Chi]_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Beta] \[PermutationProduct] InversePermutation[
        \[Alpha]], k, d * \[Chi]] * utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Gamma]], k, d 
        * \[Chi]] * d ^ utilities`CountCycles[\[Alpha], k] * d ^ utilities`CountCycles[\[Sigma],
         k] * d ^ utilities`CountCycles[\[Beta] \[PermutationProduct] InversePermutation[\[Gamma]], k] * \[Chi] ^ utilities`CountCycles[
        \[Sigma], k] * \[Chi] ^ (utilities`CountCycles[\[Beta], k] / 2) * \[Chi] ^ (utilities`CountCycles[
        \[Gamma], k] / 2), {\[Sigma], utilities`GetPermutations[k]}], {\[Alpha], utilities`GetPermutations[
        k]}, {\[Beta], utilities`GetPermutations[k]}, {\[Gamma], utilities`GetPermutations[
        k]}]]


tt[k_, d_, \[Chi]_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Beta] \[PermutationProduct] InversePermutation[
        \[Alpha]], k, d * \[Chi]] * utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Gamma]], k, d 
        * \[Chi]] * d ^ utilities`CountCycles[\[Alpha], k] * d ^ utilities`CountCycles[\[Sigma],
         k] * d ^ utilities`CountCycles[\[Beta] \[PermutationProduct] InversePermutation[\[Gamma]], k] * \[Chi] ^ utilities`CountCycles[
        \[Sigma] \[PermutationProduct] InversePermutation[\[Delta]], k] * \[Chi] ^ (utilities`CountCycles[\[Beta], k] / 2)
         * \[Chi] ^ (utilities`CountCycles[\[Gamma], k] / 2), {\[Sigma], utilities`GetPermutations[
        k]}], {\[Alpha], utilities`GetPermutations[k]}, {\[Beta], utilities`GetPermutations[
        k]}, {\[Gamma], utilities`GetPermutations[k]}, {\[Delta], utilities`GetPermutations[
        k]}]]


ttl[k_, d_, \[Chi]_] :=
    FullSimplify[Table[Sum[utilities`Weingarten[\[Beta] \[PermutationProduct] InversePermutation[
        \[Alpha]], k, d * \[Chi]] * utilities`Weingarten[\[Sigma] \[PermutationProduct] InversePermutation[\[Gamma]], k, d 
        * \[Chi]] * d ^ utilities`CountCycles[\[Alpha], k] * d ^ utilities`CountCycles[\[Sigma],
         k] * d ^ utilities`CountCycles[\[Beta] \[PermutationProduct] InversePermutation[\[Gamma]], k] * \[Chi] ^ utilities`CountCycles[
        \[Alpha], k] * \[Chi] ^ utilities`CountCycles[\[Sigma] \[PermutationProduct] InversePermutation[\[Delta]], k] * \[Chi] ^
         (utilities`CountCycles[\[Beta], k] / 2) * \[Chi] ^ (utilities`CountCycles[\[Gamma], k]
         / 2), {\[Alpha], utilities`GetPermutations[k]}, {\[Sigma], utilities`GetPermutations[
        k]}], {\[Beta], utilities`GetPermutations[k]}, {\[Gamma], utilities`GetPermutations[
        k]}, {\[Delta], utilities`GetPermutations[k]}]]


End[];


EndPackage[];
