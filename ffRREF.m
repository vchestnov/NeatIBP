(* ::Section::Closed:: *)
(*dependency*)

Get["FiniteFlow`"];

(* ::Subsection::Closed:: *)
(*TM*)

(* adapted from `utils.m` by Vitaly Magerya *)
(* https://github.com/magv/alibrary *)
SetAttributes[TM, HoldFirst];
TM[ex_] := AbsoluteTiming[ex] // (Print[HoldForm[ex], ": ", #[[1]], " sec"]; #[[2]])&;
TM[str_String] := Function[ex, AbsoluteTiming[ex] // (Print[str, ": ", #[[1]], " sec"]; #[[2]])&, HoldFirst];

(* ::Subsection::Closed:: *)
(*todata*)

todata[xs:(_List | _SparseArray)] := xs // RightComposition[
    ArrayRules,
    Most,
    SortBy[First],
    Map[Apply[List]],
    Transpose,
    (* edge case for empty `data` *)
    If[SameQ[#, {}], {{}, {}}, #]&,
    MapAt[
        Rule[#, # // Length // Range]& /* Thread /* (SparseArray[#, xs // Dimensions]&),
        #,
        {1}
    ]&,
    Identity
];

(* ::Subsection::Closed:: *)
(*reconstruct*)

ClearAll @ reconstruct;
reconstruct[data_, post_:Identity] := RightComposition[
    Rule[
        data // RightComposition[
            ArrayRules,
            Most,
            SortBy[Last],
            Part[#, All, 1]&,
            Identity
        ],
        #
    ]&,
    Thread,
    post,
    SparseArray[#, data // Dimensions]&,
    Identity
];

(* ::Subsection::Closed:: *)
(*sparsesol*)

ClearAll @ sparsesol;
sparsesol[learn_][m:(_List | _SparseArray)] := learn // RightComposition[
    Part[#, 1;;2, 2]&,
    MapAt[Length /* Range, #, {1}]&,
    Thread,
    Map[Thread],
    Apply[Join],
    (* this works not as expected when the 2nd arg is a tensor, see
     * Inner[f, {2, 1}, {{1}, {1}}, g]
     *)
    (* Inner[List /* Thread, #[[1, 2]], #[[2, 2]], Join]&, *)
    Rule[#, # // Length // Range]&,
    Thread,
    SparseArray[
        #,
        {learn[[1, 2]] // Length, m // Dimensions // Last}
    ]&,
    (* (1* Remove the leading `DepVars` columns *1) *)
    (* Part[#, All, Span[learn[[1, 2]] // Length // Add[1], All]]&, *)
    Identity
];

(* ::Subsection::Closed:: *)
(*densesol*)

ClearAll @ densesol;
densesol[learn_][m:(_List | _SparseArray)] := learn // RightComposition[
    Outer[List, #[[1, 2]] // Length // Range, #[[2, 2]]]&,
    Flatten[#, 1]&,
    Rule[#, # // Length // Range]&,
    Thread,
    SparseArray[
        #,
        {learn[[1, 2]] // Length, m // Dimensions // Last}
    ]&,
    (* (1* Remove the leading `DepVars` columns *1) *)
    (* Part[#, All, Span[needed + 1, All]]&, *)
    Identity
];

(* ::Section::Closed:: *)
(*main*)

(* ::Subsection::Closed:: *)
(*ffRowReduce*)

(* FIXME fails if matrix contains only 0 *)
ClearAll @ ffRowReduce;
Options[ffRowReduce] = {
    SolverSparseOutput -> True,
    Reconstruct        -> False,
    PrimeNo            -> 0,
    OnlyLearn          -> False,
    Nothing
};
Condition[
    ffRowReduce[matrix:(_List | _SparseArray), opt:OptionsPattern[]],
    And[
        SameQ[matrix // ArrayDepth[#, AllowedHeads -> "ListLike"]&, 2],
        True
    ]
] := Module[
    {
        g, data, vals,
        res, rref
    },
    {data, vals} = matrix // SparseArray[#, # // Dimensions]& // todata // TM["todata"];
    FFNewGraph[g, "in", {}];
    FFAlgRatNumEval[g, "vals", vals] // TM["FFAlgRatNumEval"];
    FFAlgNodeSparseSolver[
        g, "solver", {"vals"},
        data["AdjacencyLists"],
        data // Dimensions // Last // Range
    ] // TM["FFAlgNodeSparseSolver"];
    FFSolverOnlyHomogeneous[g, "solver"];
    If[OptionValue["SolverSparseOutput"],
        FFSolverSparseOutput[g, "solver"]
    ];
    FFGraphOutput[g, "solver"];
    learn = FFSparseSolverLearn[
        g,
        data // Dimensions // Last // Range
    ] // TM["FFSparseSolverLearn"];
    If[OptionValue["OnlyLearn"],
        Return[learn]
    ,
        FFSparseSolverMarkAndSweepEqs[g, "solver"];
        FFSparseSolverDeleteUnneededEqs[g, "solver"];
        If[OptionValue["Reconstruct"],
            res = FFReconstructNumeric[
                g,
                "PrintDebugInfo" -> 1,
                "MaxPrimes" -> 100
            ] // TM["FFReconstructNumeric"]
        ,
            res = FFGraphEvaluate[g, {}, PrimeNo -> OptionValue["PrimeNo"]] // TM["FFGraphEvaluate"]
        ];
        FFDeleteGraph[g];
        rref = (-1) res // RightComposition[
            reconstruct[
                data // If[OptionValue["SolverSparseOutput"],
                    sparsesol[learn],
                    densesol[learn]
                ],
                Join[#, learn[[1, 2]] // MapIndexed[{#2[[1]], #1} -> 1&, #]&]&
            ],
            Permute[#, learn[[1, 2]] // FindPermutation // InversePermutation]&,
            Identity
        ];
        Return[rref]
    ]
];
(* ffRowReduce[xs__] := CompoundExpression[ *)
(*     Print["ffRowReduce: wrong arguments: ", xs], *)
(*     Throw[$Failed], *)
(*     Null *)
(* ]; *)

(* ::Subsection::Closed:: *)
(*ffFindPivots*)

Condition[
    ffFindPivots[matrix:(_List | _SparseArray)],
    And[
        SameQ[matrix // ArrayDepth[#, AllowedHeads -> "ListLike"]&, 2],
        True
    ]
] := "DepVars" // ReplaceAll[ffRowReduce[matrix, OnlyLearn -> True]] // Sort;
