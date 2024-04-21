(* ::Package:: *)

BeginPackage["TensorOperations`"];


TensorOperations::usage = "Provides functions and operations for tensor algebra and tensor analysis."


TensorOperationsPalette::usage = "creates palette of tensor algebra/analysis operations, operators and symbols."


CreateTensor::usage = "creates TensorType object with certain parameters."


CreateChristoffelSymbols::usage = "creates ChristoffelSymbols object with certain parameters."


PrintTensor::usage = "prints table of all nonzero components of TensorType"


PrintComponents::usage = "prints sequence of tables of components for TensorType and ChristoffelSymbols"


Convolution::usage = "convolute certain tensor"


ChangeCLC::usage = "changes tensor components cooresponding to certain curvilinear coordinates change"


NChangeCLC::usage = "numerically changes tensor components cooresponding to certain curvilinear coordinates change"


SwapUpIndicies::usage = "swaps two up indecies of certain tensor"


SwapDownIndicies::usage = "swaps two down indecies of certain tensor"


PermuteUpIndicies::usage = "permutes bunch of up indecies of certain tensor"


PermuteDownIndicies::usage = "permutes bunch of down indecies of certain tensor"


SimplifyComponents::usage = "simplifies components of certain tensor"


CovariantD::usage = "covariantly differentiates certain tensor"


KroneckerDeltaTensor::usage = "creates Kronecker delta tensor of type (1, 1)"


RiemannTensor::usage = "creates certain the Riemann curvature tensor"


AllowedAsCoordQ::usage = "returns true, if argument is allowed as coordinate for tensor analysis functions. Otherwise returns false"


\[SelectionPlaceholder];\[Placeholder];\[EmptyDownTriangle];


TensorType::usage = "represents certain tensor"


ChristoffelSymbols::usage = "represents certain set of Christoffel symbols"


Affine\:0421onnection::usage = "represents certain affine connection"


Begin["Private`"];


AllowedAsCoord=_Symbol|_[_Symbol,__];


(* ::Text:: *)
(*Palette*)


TensorOperationsPalette[] := CreatePalette[Grid[{
	{"\:0418\:043d\:0434\:0435\:043a\:0441\:0438\:0440\:043e\:0432\:0430\:043d\:0438\:0435:",SpanFromLeft,SpanFromLeft}
	,
	{
		PasteButton[Subsuperscript[\[SelectionPlaceholder],{\[Placeholder]},{\[Placeholder]}]],
		PasteButton[Subscript[\[SelectionPlaceholder],{\[Placeholder]}]],
		PasteButton[Superscript[\[SelectionPlaceholder],{\[Placeholder]}]]
	}
	,
		{"\:041e\:043f\:0435\:0440\:0430\:0446\:0438\:0438:",SpanFromLeft,SpanFromLeft}
	,
	{
		PasteButton[\[Placeholder]\[CircleTimes]\[Placeholder]],
		PasteButton[\[Del]\[SelectionPlaceholder]],
		SpanFromLeft
	},
		{"\:0421\:0438\:043c\:0432\:043e\:043b\:044b:",SpanFromLeft,SpanFromLeft}
	,
	{
		PasteButton[\[EmptyDownTriangle]],
		SpanFromLeft,
		SpanFromLeft
	}
}]]


(* ::Text:: *)
(*Generating functions for TensorType*)


CreateTensor[dimensions_Integer,type:{_Integer, _Integer}]:=
	TensorType[<|"dim"->dimensions,
				"type"->type,
				"components"->Table@@Join[{0},Table[dimensions,type[[1]]],
				Table[dimensions,type[[2]]]]|>
]/;And@@NonNegative[{dimensions,type[[1]],type[[2]]}];

CreateTensor[dimensions_Integer,
			type:{_Integer, _Integer},
			components_]:=
				TensorType[<|"dim"->dimensions,
							"type"->type,
							"components"->components|>
]/;And@@NonNegative[{dimensions,type[[1]],type[[2]]}]&&
	Dimensions[components, AllowedHeads->List]==Table[dimensions,type[[1]]+type[[2]]];


(* ::Text:: *)
(*Generating functions for ChristoffelSymbols*)


CreateChristoffelSymbols[dim_Integer]:=
	ChristoffelSymbols[<|"dim"->dim,
						"components"->Array[0&,Table[dim,3]]|>
]/;Positive@dim;

CreateChristoffelSymbols[dim_Integer,components_List]:=
	ChristoffelSymbols[<|"dim"->dim,
						"components"->components|>
]/;Positive@dim&&Dimensions[components, AllowedHeads->List]==Table[dim,3];

CreateChristoffelSymbols[g_?SquareMatrixQ,x:{AllowedAsCoord..}]:=
	Module[{gInv,dim,dgdx},
		gInv=Inverse@g;
		dim=Length@g;
		dgdx=Table[D[g[[i,j]],x[[k]]],{i,dim},{j,dim},{k,dim}];
		ChristoffelSymbols[<|"dim"->dim,
							"components"->Table[
								Simplify[
									1/2 \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(\[Alpha] = 1\), \(dim\)]\(gInv[\([i, \[Alpha]]\)] \((dgdx[\([\[Alpha], j, k]\)] + dgdx[\([\[Alpha], k, j]\)] - dgdx[\([j, k, \[Alpha]]\)])\)\)\)
								],{i,dim},{j,dim},{k,dim}
							]|>
						]
]/;Length@x==Length@g;


(* ::Text:: *)
(*Accessing and setting for components of TensorType and ChristoffelSymbols*)


TensorType/:Subsuperscript[T_TensorType,{dIndicies__Integer},{uIndicies__Integer}]:=T[[1]][["components"]][[uIndicies,dIndicies]];
TensorType/:Subsuperscript[T_TensorType,{dIndicies__Integer},{}]:=T[[1]][["components"]][[dIndicies]];
TensorType/:Subsuperscript[T_TensorType,{},{uIndicies__Integer}]:=T[[1]][["components"]][[uIndicies]];
TensorType/:Subsuperscript[T_TensorType,{},{}]:=T[[1]][["components"]];

Congruent[Subsuperscript[T_TensorType,{dIndicies__Integer},{uIndicies__Integer}], val_]:=Set[T[[1]][["components"]][[uIndicies,dIndicies]],val];
Congruent[Subsuperscript[T_TensorType,{dIndicies__Integer},{}], val_]:=Set[T[[1]][["components"]][[dIndicies]],val];
Congruent[Subsuperscript[T_TensorType,{},{uIndicies__Integer}], val_]:=Set[T[[1]][["components"]][[uIndicies]],val];
Congruent[Subsuperscript[T_TensorType,{},{}], val_]:=Set[T[[1]][["components"]],val];

Congruent[Subsuperscript[S_Symbol,{dIndicies__Integer},{uIndicies__Integer}], val_]:=Set[S[[1]][["components"]][[uIndicies,dIndicies]],val]/;Head@S==TensorType;
Congruent[Subsuperscript[S_Symbol,{dIndicies__Integer},{}], val_]:=Set[S[[1]][["components"]][[dIndicies]],val]/;Head@S==TensorType;
Congruent[Subsuperscript[S_Symbol,{},{uIndicies__Integer}], val_]:=Set[S[[1]][["components"]][[uIndicies]],val]/;Head@S==TensorType;
Congruent[Subsuperscript[S_Symbol,{},{}], val_]:=Set[S[[1]][["components"]],val]/;Head@S==TensorType;

TensorType/:Superscript[T_TensorType,{uIndicies___Integer}]:=T[[1]][["components"]][[uIndicies]];
Congruent[Superscript[T_TensorType,{uIndicies___Integer}], val_]:=Set[T[[1]][["components"]][[uIndicies]],val];
Congruent[Superscript[S_Symbol,{uIndicies___Integer}], val_]:=Set[S[[1]][["components"]][[uIndicies]],val]/;Head@S==TensorType;

(*
Unprotect[Power];
TensorType/:Power[T_TensorType,{uIndicies__Integer}]:=T[[1]][["components"]][[uIndicies]];Power[S_Symbol,{uIndicies__Integer}]:=S[[1]][["components"]][[uIndicies]]/;Head@S==TensorType;
Congruent[Power[T_TensorType,{uIndicies__Integer}], val_]:=Set[T[[1]][["components"]][[uIndicies]],val];Congruent[Power[S_Symbol,{uIndicies__Integer}], val_]:=Set[S[[1]][["components"]][[uIndicies]],val]/;Head@S==TensorType;
Protect[Power];
*)

TensorType/:Subscript[T_TensorType,{dIndicies___Integer}]:=T[[1]][["components"]][[dIndicies]];
Congruent[Subscript[T_TensorType,{dIndicies___Integer}], val_]:=Set[T[[1]][["components"]][[dIndicies]],val];
Congruent[Subscript[S_Symbol,{dIndicies___Integer}], val_]:=Set[S[[1]][["components"]][[dIndicies]],val]/;Head@S==TensorType;

Congruent~SetAttributes~HoldFirst;


ChristoffelSymbols/:
Subsuperscript[\[CapitalGamma]_ChristoffelSymbols,
				{dIndicies__Integer},
				{uIndicies_Integer}] := \[CapitalGamma][[1]][["components"]][[uIndicies,dIndicies]];

Congruent[
	Subsuperscript[\[CapitalGamma]_ChristoffelSymbols,
					{dIndicies__Integer},
					{uIndicies_Integer}]
	,
	val_] := Set[\[CapitalGamma][[1]][["components"]][[uIndicies,dIndicies]],val];

Congruent[
	Subsuperscript[S_Symbol,
					{dIndicies__Integer},
					{uIndicies_Integer}]
	,
	val_]:=Set[S[[1]][["components"]][[uIndicies,dIndicies]],val]/;Head@S==ChristoffelSymbols;


(* ::Text:: *)
(*Print formats for TensorType and ChristoffelSymbols*)


PrintTensor[T_TensorType,TensorName_String:"T"]:=Grid[
	Partition[
		Grid[
			{
				{   
					Subsuperscript[TensorName,
					Take[#,-T[[1,"type",2]]],
					Take[#,T[[1,"type",1]]]]
				},
				{
					Extract[T[[1,"components"]],#]
				}
			},
			Dividers->{None,{2->Gray}}
		] &/@Position[T[[1,"components"]],(*x_/;x!=0*)
		Except[0|List],{Total@T[[1,"type"]]}],
		UpTo[6]
	]~
	Append~
	If[MemberQ[T[[1,"components"]],0,{Total@T[[1,"type"]]}],
		Prepend[
			Table[SpanFromLeft,5],
			If[
				MemberQ[T[[1,"components"]],
						Except[0],
						{Total@T[[1,"type"]]}
				],
				"\:041e\:0441\:0442\:0430\:043b\:044c\:043d\:044b\:0435 \:043a\:043e\:043c\:043f\:043e\:043d\:0435\:043d\:0442\:044b \:0440\:0430\:0432\:043d\:044b \:043d\:0443\:043b\:044e",
				"\:0412\:0441\:0435 \:043a\:043e\:043c\:043f\:043e\:043d\:0435\:043d\:0442\:044b \:0440\:0430\:0432\:043d\:044b \:043d\:0443\:043b\:044e"
			]
		]
		,
		Nothing
	],
	Frame->True,Dividers->All
];
	
PrintTensor[S_Symbol/;Head[S]==TensorType]:=
	PrintTensor[Evaluate[S],ToString[Unevaluated@S]];

SetAttributes[PrintTensor,HoldFirst]


PrintComponents[\[CapitalGamma]_ChristoffelSymbols,name_String:"\[CapitalGamma]"]:=
Module[{comps},
	Grid[
		Table[
			{
				Row[{Subsuperscript[name,{"i","j"},
					{top}],":"}],
				(
					comps=Table[Subsuperscript[\[CapitalGamma],{i,j},{top}],{i,\[CapitalGamma][[1,"dim"]]},
							{j,\[CapitalGamma][[1,"dim"]]}];
					comps=PadLeft[comps,
								{\[CapitalGamma][[1,"dim"]]+1,
								\[CapitalGamma][[1,"dim"]]+1}];
					comps[[1,1]]="i \\ j";
					Do[comps[[k+1,1]]=comps[[1,k+1]]=k;,
						{k,\[CapitalGamma][[1,"dim"]]}];
					Grid[comps,
						Frame->All,
						Spacings->{2,1},
						Alignment->Center]
				)
			}
			,{top,\[CapitalGamma][[1,"dim"]]}
		],
		Spacings->{1.5,2}
	]
];

PrintComponents[T_TensorType/;Total@T[[1,"type"]]>=2,
				name_String:"T"] :=
Module[{comps,up,down,ijs},
	Grid[
		Table[
			{
				(
					{down,up}={Take[firstInds,
								-Max[T[[1,"type",2]]-2,0]]
								,
								Take[firstInds,
									T[[1,"type",1]]-
									Max[2-T[[1,"type",2]],0]]
								};
					ijs=Switch[T[[1,"type",2]],
								0,{{},{"i","j"}},
								1,{{"j"},{"i"}},
								_,{{"i","j"},{}}
								];
					down=Join[down,ijs[[1]]];
					up=Join[up,ijs[[2]]];
					Row[{Subsuperscript[name,down,up],":"}]
				),
				(
					comps=Table[Subsuperscript[T,down/.{"i"->i,"j"->j},up/.{"i"->i,"j"->j}],
								{i,T[[1,"dim"]]},
								{j,T[[1,"dim"]]}
								];
					comps=PadLeft[comps,
								{T[[1,"dim"]]+1,
								T[[1,"dim"]]+1}
								];
					comps[[1,1]]="i \\ j";
					Do[comps[[k+1,1]]=comps[[1,k+1]]=k;,
						{k,T[[1,"dim"]]}
						];
					Grid[comps,
						Frame->All,
						Spacings->{2,1},
						Alignment->Center
						]
				)
			},
			{
				firstInds,
				Tuples[Range[T[[1,"dim"]]],
				Total@T[[1,"type"]]-2]
			}
		],
		Spacings->{1.5,2}
	]
];

PrintComponents[T_TensorType/;Total@T[[1,"type"]]==1,
				name_String:"T"] := PrintTensor[T,name];
PrintComponents[T_TensorType/;Total@T[[1,"type"]]==0,
				name_String:"T"] :=
					Row[{name<>" = ",T[[1,"components"]]}];

PrintComponents[S_Symbol/;MatchQ[Head[S],
				TensorType|ChristoffelSymbols]]:=
					PrintComponents[Evaluate[S],
									ToString[Unevaluated@S]];

PrintComponents[
	expr:Except[_TensorType|_ChristoffelSymbols|_Symbol]
] := PrintComponents[Evaluate[expr],"("<>ToString[Unevaluated@expr]<>")"];

SetAttributes[PrintComponents,HoldFirst]


(* ::Text:: *)
(*Tensor operations*)


TensorType/:
T_TensorType + R_TensorType := 
CreateTensor[T[[1,"dim"]],
			T[[1,"type"]],
			T[[1,"components"]]+R[[1,"components"]]
]/;T[[1,"dim"]]==R[[1,"dim"]]&&T[[1,"type"]]==R[[1,"type"]];

TensorType/:
T_TensorType - R_TensorType := 
CreateTensor[T[[1,"dim"]],
			T[[1,"type"]],
			T[[1,"components"]]-R[[1,"components"]]
]/;T[[1,"dim"]]==R[[1,"dim"]]&&T[[1,"type"]]==R[[1,"type"]];


TensorType/:
Times[\[Lambda]:Except[TensorType],T_TensorType]:=
CreateTensor[T[[1,"dim"]],
			T[[1,"type"]],
			\[Lambda]*T[[1,"components"]]
];


TensorType/:
CircleTimes[T_TensorType,R_TensorType]:=
CreateTensor[T[[1,"dim"]],T[[1,"type"]]+R[[1,"type"]],
	Module[{prod,uProd,dProd},
		prod = Array[0&, Table[
							T[[1,"dim"]],
							T[[1,"type",1]]+
							R[[1,"type",1]]+
							T[[1,"type",2]]+
							R[[1,"type",2]]
							]];
		Do[
			uProd=uT~Join~uR;
			dProd=dT~Join~dR;
			(*Subsuperscript[prod, dProd, uProd]\[Congruent]Subsuperscript[T, dT, uT]*Subsuperscript[R, dR, uR]*);
			(prod[[##]]=Subsuperscript[T,dT,uT]*Subsuperscript[R,dR,uR])&@@Join[uT,uR,dT,dR],
			
			{uT,Tuples[Range[T[[1,"dim"]]],T[[1,"type",1]]]},
			{uR,Tuples[Range[R[[1,"dim"]]],R[[1,"type",1]]]},
			{dT,Tuples[Range[T[[1,"dim"]]],T[[1,"type",2]]]},
			{dR,Tuples[Range[R[[1,"dim"]]],R[[1,"type",2]]]}
		];
		prod
	]
]/;T[[1,"dim"]]==R[[1,"dim"]];

TensorType/:
CircleTimes[T_TensorType,R_TensorType,other:_TensorType..]:=
	CircleTimes[(T\[CircleTimes]R),other]/;T[[1,"dim"]]==R[[1,"dim"]];

SetAttributes[CircleTimes,Flat];


Convolution[T_TensorType,uIndex_Integer,dIndex_Integer]:=
CreateTensor[T[[1,"dim"]],T[[1,"type"]]-{1,1},
	Module[{conv,i,row},

		conv=Array[0&,Table[T[[1,"dim"]],Total@T[[1,"type"]]-2]];
		Do[
			row=Join[left,{i},mid,{i},right];
			(conv[[##]]=Sum[Extract[T[[1,"components"]],row],{i,T[[1,"dim"]]}])&@@Join[left,mid,right];
			,
			{left,Tuples[Range[T[[1,"dim"]]],Max[uIndex-1,0]]},
			{mid,Tuples[Range[T[[1,"dim"]]],Max[T[[1,"type",1]]-uIndex+dIndex-1,0]]},
			{right,Tuples[Range[T[[1,"dim"]]],Max[T[[1,"type",2]]-dIndex,0]]}
		];
		
		conv
	]
]/;NonNegative[uIndex]&&NonNegative[dIndex];

Convolution[T_TensorType,sumIndicies:{{_Integer,_Integer}..}]:=
Module[{uId,dId,curIndecies=sumIndicies,curConv=T},
	Do[
		uId=curIndecies[[i,1]];
		dId=curIndecies[[i,2]];
		curConv=Convolution[curConv,uId,dId];
		curIndecies=curIndecies/.{x_,y_}/;x>uId:>{x-1,y};
		curIndecies=curIndecies/.{x_,y_}/;y>dId:>{x,y-1};
		,
		{i,Length@curIndecies}];
	curConv
]/;And@@Flatten@NonNegative[sumIndicies];


ChangeCLC=.

AllowedAsCoordQ[coord_]:=MatchQ[coord,AllowedAsCoord];

ChangeCLC[T_TensorType,oldToNew:{(AllowedAsCoord->_)..},new:{AllowedAsCoord..}]:=
CreateTensor[T[[1,"dim"]],T[[1,"type"]],
	Module[{comps,jacobian,invJ},
		comps=Array[0&,Table[T[[1,"dim"]],Total@T[[1,"type"]]]];
		jacobian=Table[D[oldToNew[[i,2]],new[[j]]],
						{i,T[[1,"dim"]]},
						{j,T[[1,"dim"]]}];
		invJ=Inverse@jacobian;
		Do[
			comps[[Sequence@@Join[up,down]]]=Simplify@Sum[
				(Subsuperscript[T,sumDown,sumUp]/.oldToNew)
				 *
				Product[jacobian[[up[[i]],sumUp[[i]]]],{i,T[[1,"type",1]]}]
				 *
				Product[invJ[[sumDown[[j]],down[[j]]]],{j,T[[1,"type",2]]}]
				,
				{sumUp,Tuples[Range[T[[1,"dim"]]],T[[1,"type",1]]]},
				{sumDown,Tuples[Range[T[[1,"dim"]]],T[[1,"type",2]]]}
			]
			,
			{up,Tuples[Range[T[[1,"dim"]]],T[[1,"type",1]]]},
			{down,Tuples[Range[T[[1,"dim"]]],T[[1,"type",2]]]}
		];
		
		comps
	]
]/;Length@oldToNew==T[[1,"dim"]]&&Length@new==T[[1,"dim"]];

ChangeCLC[T_TensorType,old:{AllowedAsCoord..},
		newToOld:{(AllowedAsCoord->_)..}]:=
ChangeCLC[T,
		First@Solve[newToOld/.Rule->Equal,old],
		newToOld/.Rule[x_,_]:>x
]/;Length@old==T[[1,"dim"]]&&Length@newToOld==T[[1,"dim"]];

NChangeCLC[T_TensorType,old:{AllowedAsCoord..},
		newToOld:{(AllowedAsCoord->_)..}]:=
ChangeCLC[T,
		First@NSolve[newToOld/.Rule->Equal,old],
		newToOld/.Rule[x_,_]:>x
]/;Length@old==T[[1,"dim"]]&&Length@newToOld==T[[1,"dim"]];


ClearAll[SwapDownIndicies,SwapUpIndicies]

SwapUpIndicies[T_TensorType,
				{f_Integer?Positive,s_Integer?Positive}]:=
Module[{res,resUps,TUps},
	res=CreateTensor[T[[1,"dim"]],T[[1,"type"]]];
	Do[
		resUps=Join[left,{i},mid,{j},right];
		res[[1,"components",Sequence@@Join[resUps,down]]]
		=
		Subsuperscript[T,down,Join[left,{j},mid,{i},right]];
		,
		{left,Tuples[Range[T[[1,"dim"]]],Max[f-1,0]]},
		{mid,Tuples[Range[T[[1,"dim"]]],Max[s-f-1,0]]},
		{right,Tuples[Range[T[[1,"dim"]]],Max[T[[1,"type",1]]-s-1,0]]},
		{down,Tuples[Range[T[[1,"dim"]]],T[[1,"type",2]]]},
		{i,Range[T[[1,"dim"]]]},
		{j,Range[T[[1,"dim"]]]}
	];
	res
]/;s<=T[[1,"type",1]]&&f<s;

SwapUpIndicies[T_TensorType,
				{f_Integer?Positive,s_Integer?Positive}]:=
SwapUpIndicies[T,{s,f}]/;f>s;

SwapUpIndicies[T_TensorType,{f_Integer?Positive,f_}]:=T;

SwapDownIndicies[T_TensorType,
				{f_Integer?Positive,s_Integer?Positive}]:=
Module[{res,resUps,TUps},
	res=CreateTensor[T[[1,"dim"]],T[[1,"type"]]];
	Do[
		resUps=Join[left,{i},mid,{j},right];
		res[[1,"components",Sequence@@Join[up,resUps]]]=Subsuperscript[T,Join[left,{j},mid,{i},right],up];
		,
		{left,Tuples[Range[T[[1,"dim"]]],Max[f-1,0]]},
		{mid,Tuples[Range[T[[1,"dim"]]],Max[s-f-1,0]]},
		{right,Tuples[Range[T[[1,"dim"]]],Max[T[[1,"type",2]]-s-1,0]]},
		{up,Tuples[Range[T[[1,"dim"]]],T[[1,"type",1]]]},
		{i,Range[T[[1,"dim"]]]},
		{j,Range[T[[1,"dim"]]]}
	];
	res
]/;s<=T[[1,"type",2]]&&f<s;

SwapDownIndicies[T_TensorType,
				{f_Integer?Positive,s_Integer?Positive}]:=
SwapUpIndicies[T,{s,f}]/;f>s;

SwapDownIndicies[T_TensorType,{f_Integer?Positive,f_}]:=T;

PermuteUpIndicies[T_TensorType, perm_]:=Module[{res},
	res=CreateTensor[T[[1,"dim"]],T[[1,"type"]]];
	Do[
		res[[1,"components",Sequence@@Join[up,down]]]=Subsuperscript[T,down,Permute[up,perm]];
		,
		{up,Tuples[Range[T[[1,"dim"]]],T[[1,"type",1]]]},
		{down,Tuples[Range[T[[1,"dim"]]],T[[1,"type",2]]]}
	];
	res
]

PermuteDownIndicies[T_TensorType, perm_]:=Module[{res},
	res=CreateTensor[T[[1,"dim"]],T[[1,"type"]]];
	Do[
		res[[1,"components",Sequence@@Join[up,down]]]=Subsuperscript[T,Permute[down,perm],up];
		,
		{up,Tuples[Range[T[[1,"dim"]]],T[[1,"type",1]]]},
		{down,Tuples[Range[T[[1,"dim"]]],T[[1,"type",2]]]}
	];
	res
]


SimplifyComponents[T_TensorType]:=Module[{res},
	res=Array[0&,Table[T[[1,"dim"]],Total@T[[1,"type"]]]];
	Do[
		res[[Sequence@@Join[up,down]]]=Simplify[Subsuperscript[T,down,up]],
		{up,Tuples[Range[T[[1,"dim"]]],T[[1,"type",1]]]},
		{down,Tuples[Range[T[[1,"dim"]]],T[[1,"type",2]]]}
	];
	CreateTensor[T[[1,"dim"]],T[[1,"type"]],res]
]

SimplifyComponents[\[CapitalGamma]_ChristoffelSymbols]:=Module[{res},
	res=Array[0&,Table[\[CapitalGamma][[1,"dim"]],3]];
	Do[
		res[[Sequence@@Join[up,down]]]=Simplify[Subsuperscript[\[CapitalGamma],down,up]],
		{up,Tuples[Range[\[CapitalGamma][[1,"dim"]]],1]},
		{down,Tuples[Range[\[CapitalGamma][[1,"dim"]]],2]}
	];
	CreateChristoffelSymbols[\[CapitalGamma][[1,"dim"]],res]
]


(* ::Text:: *)
(*Affine Connectivity operations*)


CovariantD=.
Affine\:0421onnection=.

CovariantD[T_TensorType,
			\[CapitalGamma]_ChristoffelSymbols,
			x:{AllowedAsCoord...}]:=
CreateTensor[T[[1,"dim"]],T[[1,"type"]]+{0,1},
	Module[{comps,TensoredGamma,\[CapitalChi],p,q,Transfer},
		comps=Array[0&,Table[T[[1,"dim"]],Total@T[[1,"type"]]+1]];
		TensoredGamma=CreateTensor[\[CapitalGamma][[1,"dim"]],{1,2},\[CapitalGamma][[1,"components"]]];
		\[CapitalChi]=T\[CircleTimes]TensoredGamma;
		p=T[[1,"type",1]];
		q=T[[1,"type",2]];
		(*\:041f\:043e\:0440\:044f\:0434\:043e\:043a \:0432\:0440\:043e\:0434\:0435 \:0434\:043e\:043b\:0436\:0435\:043d \:0431\:044b\:0442\:044c \:0432\:0430\:0436\:0435\:043d \:043f\:0440\:0438 \:043e\:0442\:0441\:0443\:0442\:0441\:0442\:0432\:0438\:0438 \:043f\:0440\:0435\:0434\:0443\:0441\:043b\:043e\:0432\:0438\:044f*)
		Transfer[list_,from_,to_]:=Permute[list,Range[to,from,-1]]/;from!=to;
		Transfer[list_,from_,from_]:=list;
		Do[
			comps[[Sequence@@up,k,Sequence@@down]]
			 =
			 D[Subsuperscript[T,down,up],x[[k]]]
			 +
			 Sum[Subsuperscript[Convolution[\[CapitalChi],s,q+1],Append[down,k],Transfer[up,s,p]],{s,p}]
			 +
			 Sum[Subsuperscript[Convolution[\[CapitalChi],p+1,s],Transfer[Append[down,k],s,q],up],{s,q}];
			,
			{up,Tuples[Range[T[[1,"dim"]]],T[[1,"type",1]]]},
			{k,T[[1,"dim"]]},
			{down,Tuples[Range[T[[1,"dim"]]],T[[1,"type",2]]]}
		];
		comps
	]
]/;T[[1,"dim"]]==\[CapitalGamma][[1,"dim"]];

CovariantD[\[CapitalGamma]_ChristoffelSymbols,x:{AllowedAsCoord...}]:=Affine\:0421onnection[\[CapitalGamma],x];
Affine\:0421onnection[\[CapitalGamma]_ChristoffelSymbols,x:{AllowedAsCoord...}][T_TensorType]:=CovariantD[T,\[CapitalGamma],x]/;T[[1,"dim"]]==\[CapitalGamma][[1,"dim"]];


(* ::Text:: *)
(*Special tensors*)


KroneckerDeltaTensor[dimensions_Integer]:=
CreateTensor[
	dimensions,
	{1,1},
	IdentityMatrix[dimensions]
]/;NonNegative[dimensions]


RiemannTensor[\[CapitalGamma]_ChristoffelSymbols,
				x:{AllowedAsCoord...}]:=
Module[{R,dim,val},
	R=CreateTensor[\[CapitalGamma][[1,"dim"]],{1,3}];
	dim=\[CapitalGamma][[1,"dim"]];
	Do[
		val=D[Subsuperscript[\[CapitalGamma],{q,l},{i}],x[[k]]]-D[Subsuperscript[\[CapitalGamma],{q,k},{i}],x[[l]]]+\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(p = 1\), \(dim\)]\(\*
TemplateBox[{"\[CapitalGamma]", RowBox[{"{", RowBox[{"q", ",", "l"}], "}"}], RowBox[{"{", "p", "}"}]},
"Subsuperscript"] \*
TemplateBox[{"\[CapitalGamma]", RowBox[{"{", RowBox[{"p", ",", "k"}], "}"}], RowBox[{"{", "i", "}"}]},
"Subsuperscript"]\)\)-\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(p = 1\), \(dim\)]\(\*
TemplateBox[{"\[CapitalGamma]", RowBox[{"{", RowBox[{"q", ",", "k"}], "}"}], RowBox[{"{", "p", "}"}]},
"Subsuperscript"] \*
TemplateBox[{"\[CapitalGamma]", RowBox[{"{", RowBox[{"p", ",", "l"}], "}"}], RowBox[{"{", "i", "}"}]},
"Subsuperscript"]\)\);
		R[[1,"components",i,q,k,l]]=val
		,
		{i,dim},
		{q,dim},
		{k,dim},
		{l,dim}
	];
	R
];

RiemannTensor[Affine\:0421onnection[\[CapitalGamma]_ChristoffelSymbols,x:{AllowedAsCoord...}]]:=RiemannTensor[\[CapitalGamma],x]/;\[CapitalGamma][[1,"dim"]]==Length@x;


End[];


EndPackage[];
