(* ::Package:: *)

(*  ColorJones.m                                                               *)
(*  Author: Jesse S. F. Levitt                                           *)
(*    Date: Sept 2017                                                      *)
(* Version: 0.1 ( initial implementation )                                 *)
<<NC`
<<NCAlgebra`

BeginPackage[ "ColorJones`",{"KnotTheory`",(*"NC`","NCAlgebra`",*)"NCPolyInterface`","NCDot`","NonCommutativeMultiply`","NCPoly`"}];

CJ::usage = "To calculate the Colored Jones Polynomial of a Braid using the Approaches of Armond, Hunyh and L\[EHat]."

Begin["`Private`"];


(*<<Combinatorica`*)
(* This material added since combinatorica was depricated *)
MInversions[{}] := 0
MInversions[p_?MPermutationQ] := Apply[Plus,MToInversionVector[p]]
MPermutationQ[e_List] := (Sort[e] === Range[Length[e]])
MToInversionVector[p_?MPermutationQ] :=
	Block[{i,inverse=InversePermutation[p]},
		Table[ Length[ Select[Take[p,inverse[[i]]], (# > i)&] ], {i,Length[p]-1}]
	] /; (Length[p] > 0)


(* package variables for use *)

CJP`q; CJP`a; CJP`b; CJP`c;



detq[q_, m_, Ncrs_]:=(*detq[q, m, Ncrs]=*)Module[{QD,mlen,n,pl,l,keys,ncvLen=3*Ncrs+1},

mlen=Length[m];
n=Permutations[Range[mlen]];
pl=Length[n];

(*Notes:

1-The following (g[i_,j_])function does the following :

Recall that the permutation is given by 

Underscript[\[Sum], \[Sigma]\[Element]S^n](sgn \[Sigma]) \[InvisiblePrefixScriptBase]Subscript[mlen, \[Sigma](1)1]... Subscript[mlen, \[Sigma](n)n]

What I want to find here is Subscript[mlen, \[Sigma](i)i] for a specific \[Sigma] 
In order to do that we need a function g[i_,j_] that takes two arguements i and j and gives out Subscript[mlen, \[Sigma](i)i]
"i" refers to "i" in Subscript[mlen, \[Sigma](i)i] and j indexes some permutation(i.e j indexes \[Sigma] ) so j should vary from 1 to the mlen (the length of the matrix m)

so in summary g[the index of the permutation,i]

2-Recall that the way we extract an element Subscript[m,ij] from a matrix m is :m[[i,j]] *)

(*g[i_,j_]:=m[[n[[j,i]],i ]];*)

(* The following argument finds the multiplication \[InvisiblePrefixScriptBase]Subscript[mlen, \[Sigma](1)1]... Subscript[mlen, \[Sigma](n)n] for a fixed \[Sigma]
since \[Sigma] is indexed by some integer s from s=1 to s=mlen then
we can define this function to be a function that takes some integer and spits out this multplication so \[InvisiblePrefixScriptBase]
k[\[Sigma]]:=k[some integer s that parametrizes \[Sigma]]=Subscript[mlen, \[Sigma](1)1]... Subscript[mlen, \[Sigma](n)n]
*)

(*	Do[ t=t**g[i,s],{i,1,mlength}];*)
detq`k[s_, mlength_]:=Module[{Ki,j,t},
	t=1;
	Do[ t=NCE[t**m[[n[[s,Ki]],Ki ]]];
		If[t==0,Break[]];
		(* Implement lemma 4a *)
		Do[
			t[[2]]=Association[DeleteCases[t[[2]]//Normal,
													HoldPattern[keys_List->_]/;
														(keys[[ncvLen-j-2*Ncrs]]+keys[[ncvLen-j-Ncrs]])>1|| (* ai+ci *)
														(keys[[ncvLen-j-2*Ncrs]]+keys[[ncvLen-j]])>1]];  (* ai+bi *)
			If[t==0,Break[]]
			,{j,1,Ncrs}
		];
	,{Ki,1,mlength}];
	t
];

QD=NCE[Sum[(-q)^MInversions[n[[l]]]**(detq`k[l,mlen]),{l,pl}]];

Return[QD]]
(*
Note: to make sure that the quantum determinate is correct try : sub q=-1 and 
then try CommuteEverything[Expand[detq[m]]]
should should equal to the usual Det[m]


Example of calculations
a=(-1)^Inversions[{1,2,4,3}]
Inversions[{2,1,4,3}]
m=(q	3	-8	-10	-6	-3
0	(1-q)	8	-10	5	7
3	-2	-6	-9	-1	2
10	-3	-2	-9	2	-2
7	2	7	7	4	-9
-4	-2	10	6	9	7

)

*)


(* vars represents that variable list of the Braid used by NCPoly, *)
Brep[Braid_, vars_]:=Module[{FI=IdentityMatrix[Max[Braid]+1], Ncrs=Length[Braid], M, NCvars, p},
M=ConstantArray[FI,Ncrs];
NCvars=NCToNCPoly[#,vars]&/@ vars;

Do[
	p=Braid[[i]][[1]];
	If[\!\(TraditionalForm\`Braid\)[[i]][[2]]==1,
		M[[i]]=ReplacePart[M[[i]],{
					{p,p}->NCvars[[i+2*Ncrs]],  {p,p+1}->NCvars[[i]],
					{p+1,p}->NCvars[[i+Ncrs]],{p+1,p+1}->0}],
		M[[i]]=ReplacePart[M[[i]],{
					{p,p}->0,              {p,p+1}->NCvars[[i+Ncrs]],
					{p+1,p}->NCvars[[i]],{p+1,p+1}->NCvars[[i+2*Ncrs]]}]
	],{i,Ncrs}
];

Do[FI=NCDot[FI,M[[i]]],{i,1,Ncrs}]; (* Verified ordering by comparison with Trefoil Example 0.1.4 from Huynh Le*)

Return[FI]]


(* This is the B-matrix with the first row and first column deleted. It also mulitplies every element by q  *)
RBrep[q_, M_]:=NCE[q**Drop[M, 1, 1]]


(* Input a matrix, Output a List of submatrices depending on the power set of the index set of the dimension of the input matrix *)
SSubMatrices[M_]:=Module[{T,DSU,Ar},

(* T gives the a sequence of integers that starts at 1 and ends at the dimensions of the input matrix M *)
T=Range[Length[M]];

(* DSU gives the set of sets of the table T but ignores the empty set *)
DSU=Delete[Subsets[T],1];

(* Ar, which is the output, is a list that stores of all the symmetric submatrices of the input matrix M.
The following algorithm calculates Ar. It runs over every element of DSU and for every single element for Ln it gives a submatrix of M *)
Ar=Array[M[[DSU[[#]],DSU[[#]]]]&,Length[DSU]];

Return[Ar]]


(* This function evaluates C.
For definition see "On the colored Jones Polynomial and the Kashaev invariant" by V. Huynh and T. Le - page 2 *)
(*CEE[q_, K_]:=Total[Array[(-1)^((Length[K[[#]]])-1)*detq[q, K[[#]]]&,Length[K]]]*)
CEE[q_, K_, Ncrs_]:=Fold[Plus,Array[(-1)^((Length[K[[#]]])-1)*detq[q, K[[#]], Ncrs]&,Length[K]]]


(* This is the sum of simple walks.
Input a braid and output a sum of simple walks *)

(* Load precomputed values if possible *)
<<"walk-model-to-compute-the-colored-jones-polynomial/simplewalks.m";

SimpleWalkCalculator[Braid_Knot,NCvars_,q_]:=SimpleWalkCalculator[Array[List[Abs[BR[Braid][[2]][[#]]],Sign[BR[Braid][[2]][[#]]]]&,Length[BR[Braid][[2]]]],NCvars,q]

SimpleWalkCalculator[Braid_BR,NCvars_,q_]:=SimpleWalkCalculator[Array[List[Abs[Braid[[2]][[#]]],Sign[Braid[[2]][[#]]]]&,Length[Braid[[2]]]],NCvars,q]

SimpleWalkCalculator[brd_, NCvars_, q_]:=SimpleWalkCalculator[brd, NCvars, q]=Module[{simpleWalks,Ncrs=Length[brd],ncvLen=Length[NCvars]+1},
simpleWalks=NCE[CEE[q, SSubMatrices[RBrep[q, Brep[brd, NCvars]]], Quotient[Length[NCvars],3]]];

(*simpleWalks=Timing[NCE[CEE[q, SSubMatrices[RBrep[q, Brep[brd, NCvars]]], Quotient[Length[NCvars],3]]]];*)
(*Print[simpleWalks[[1]]];
simpleWalks=simpleWalks[[2]];*)

	(* Implement lemma 4a *)
	Do[
		simpleWalks[[2]]=Association[DeleteCases[simpleWalks[[2]]//Normal,
													HoldPattern[keys_List->_]/;
														(keys[[ncvLen-i-2*Ncrs]]+keys[[ncvLen-i-Ncrs]])>1|| (* ai+ci *)
														(keys[[ncvLen-i-2*Ncrs]]+keys[[ncvLen-i]])>1]];  (* ai+bi *)
		If[simpleWalks==0,Break[]]
		,{i,1,Ncrs}
	];

(* Figure out how to add to simplewalks.m? *)
(*(SimpleWalkCalculator[brd, NCvars, q]=simpleWalks)>>>"walk-model-to-compute-the-colored-jones-polynomial/simplewalks.m"*)

(*Print[Length[simpleWalks[[2]]]];*)

Return[simpleWalks]
]


ScriptE[q_,n_,cr_,ad_,sign_]:=ScriptE[q,n,cr,ad,sign]=If[sign>0,SCRIPTEP[q,n,cr,ad],SCRIPTEN[q,n,cr,ad]]


SCRIPTEP[q_,n_,cr_,ad_]:=Block[{SEPval=1},
	If[ad!=0,SEPval*=Product[(1-q^(n-cr-k)),{k,ad}]];
	If[cr!=0,SEPval*=q^(cr*(n-1-ad))];

SEPval]



SCRIPTEN[q_,n_,cr_,ad_]:=Block[{SENval=1},
	If[ad!=0,SENval*=Product[(1-q^(cr+k-n)),{k,ad}]];
	If[cr!=0,SENval*=q^(-cr*(n-1))];

SENval]



MonomialBuilder[aList_, bList_, cList_, Ncrs_]:=MonomialBuilder[aList, bList, cList, Ncrs]=Block[
{MBexponents=Join[bList,cList,aList],MBdigits={},MBlength=3*Ncrs,MBposition=1,MBi,MBj},
(* Rebuild MBexponents to minimize the number of Keys *)
MBdigits=ConstantArray[0,Total[MBexponents]];
For[MBi=0,MBi<MBlength,MBi++,
	For[MBj=0,MBj<MBexponents[[MBi+1]],MBj++,MBdigits[[MBposition]]=MBi;MBposition++];
	];

Return[Join[Reverse[MBexponents],{FromDigits[MBdigits, 3*Ncrs]}]]
(*Return[Join[Reverse[MBexponents],{NCFromDigits[MBdigits, 3*Ncrs][[2]]}]]*)
]



(* A helper function for BMEC, to slow memory loading *)
BraidMonomialHelper[ ncPart_, Ncrs_, Signs_]:=BraidMonomialHelper[ ncPart, Ncrs, Signs]=Block[
(* Initialize the degree count lists *)
{BMHlocalMonomial, BMHword, BMHcrossing, BMHaList=ConstantArray[0,Ncrs], BMHbList=ConstantArray[0,Ncrs], BMHcList=ConstantArray[0,Ncrs], BMHqdegree=0},

(*BMHlocalMonomial=NCIntegerDigits[{Total[Most[ncPart]],Last[ncPart]},3*Ncrs];*)
BMHlocalMonomial=PadLeft[IntegerDigits[Last[ncPart],3*Ncrs],Total[Most[ncPart]]];

Do[
	BMHword=BMHlocalMonomial[[i]];
	BMHcrossing=Mod[BMHword,Ncrs]+1;
	If[Signs[[BMHcrossing]]>0,
		Switch[Quotient[BMHword,Ncrs],
			2,BMHaList[[BMHcrossing]]++, (* a is ordered last so we don't need to check how many b's or c's have already appeared *)
			0,BMHbList[[BMHcrossing]]++; BMHqdegree-=(2*BMHcList[[BMHcrossing]]), (* b is ordered first, but commutes with a's, so we need to account for c's *)
			1,BMHcList[[BMHcrossing]]++; BMHqdegree+=BMHaList[[BMHcrossing]] (* c is ordered middle, account for all the a's it needs to cross *)
		],
		Switch[Quotient[BMHword,Ncrs],
			2,BMHaList[[BMHcrossing]]++, (* a is ordered last so we don't need to check how many b's or c's have already appeared *)
			0,BMHbList[[BMHcrossing]]++; BMHqdegree+=(2(BMHaList[[BMHcrossing]] + BMHcList[[BMHcrossing]])), (* b is ordered first, so we need to account for a's and c's it will pass *)
			1,BMHcList[[BMHcrossing]]++; BMHqdegree-=BMHaList[[BMHcrossing]] (* c is ordered middle, account for all the a's it needs to cross *)
		]
	]
	,{i,1,Length[BMHlocalMonomial]}
];

List[BMHqdegree,BMHaList,BMHbList,BMHcList]
]


(* A function for calculating all the relevant information from the exponents without reordering the polynomial *)
BMEC[ monomial_,  Ncrs_, Signs_, q_]:=BraidMonomialExponentCounter[monomial,Ncrs,Signs, q]

(* The function returns a list of 4 elements, with the first being one element and the rest Lists containing as many elements as the braid has crossings *)
BraidMonomialExponentCounter[ monomialRule_, Ncrs_, Signs_, q_]:=Block[{BMECcoefficient, BMECexponentList},
(* pull out all coefficient pieces *)

BMECexponentList=BraidMonomialHelper[ monomialRule[[1]], Ncrs, Signs];
BMECcoefficient=monomialRule[[2]]*q^BMECexponentList[[1]];

List[BMECcoefficient, BMECexponentList[[2]], BMECexponentList[[3]], BMECexponentList[[4]]]
]


CJ[q_,NC_,Braid_Knot]:=CJ[q,NC,Array[List[Abs[BR[Braid][[2]][[#]]],Sign[BR[Braid][[2]][[#]]]]&,Length[BR[Braid][[2]]]]]

CJ[q_,NC_,Braid_BR]:=CJ[q,NC,Array[List[Abs[Braid[[2]][[#]]],Sign[Braid[[2]][[#]]]]&,Length[Braid[[2]]]]]

CJ[q_,NC_,Braid_List]:=Module[
{stackHeight=1, loopDone=False, CJP=1, TPW, Ncrs, walks, simpleWalks, numStrands, keys, ncvLen, writhe, LNG, ML, walkWeights, NCvars, i, j, localBraid},

(*  Ensure we are using our default type of Braid Word.
    If its a dimension 1 list, we assume its a Braid Word, such as {1,-2,1,-2} for the Figure 8 knot.
    If its a dimension 2 list, we assume it has a {crossing, sign} form, such as {{1,1},{2,-1},{1,1},{2,-1}} for the Figure 8 knot.
    Otherwise, we would like to return an Error.
    Following this, tabulate the number of crossings - 'Ncrs' - as well as the number of strands in the braid representation and the writhe. *)
If[MatrixQ[Braid]!=True,
	localBraid=Array[List[Abs[Braid[[#]]],Sign[Braid[[#]]]]&,Length[Braid]],
	localBraid=Braid
];
Ncrs=Length[localBraid];
numStrands=Max[localBraid]+1;
writhe=Sum[localBraid[[i,2]],{i,Ncrs}];

(*  All NonCommutative variables are generated dynamically and kept track of using the NCvars List.
	This accomidates varied knots using a standardized notation.
	Maintaining the order of this List: {CJP`b1, CJP`b2, ... , CJP`c1, ... , CJP`a1, ... , CJP`a'Ncrs'} is critical to the functionality of calls to this List.
	This reflects the choice to speed computation wherever possible by using integer math over calls to symbol name lookups.
	The standard q value 'CJP`q' is set Commutative and the rest NonCommutative.
	Finally we set ncvLen to record an integer controlling access to the NCPoly data structure for later use.
	Specifically, NCPoly stores variable term data in reverse order with an extra data term. *)
SetCommutative[CJP`q];
NCvars = Flatten[Symbol/@StringJoin/@Tuples[{{"CJP`b","CJP`c","CJP`a"},ToString/@Range[Ncrs]}]]; (* each crossing can either be positive Xor negative *)
SetNonCommutative[NCvars];
ncvLen=Length[NCvars]+1;

(*  The simple walks over a Braid are calculated using the reduced Burau representation.
	These will be calculated dynamically if necessary or pulled from data tables if possible.
	It will be returned with Lemma 4a already applied. *)
simpleWalks=SimpleWalkCalculator[localBraid, NCvars, CJP`q];
If[ NC==2, simpleWalks[[2]]=Map[Sign[Coefficient[#,CJP`q,Exponent[#,CJP`q]]]*#&,simpleWalks[[2]]]];
(*Print[NCPolyDisplay[simpleWalks,NCvars]];*)

(*  Useful for batch runs as a way to update the data tables *)
(* Definition[SimpleWalkCalculator]>>"simplewalks.m";*)

While[loopDone!=True,

(*  If we are looping, rebuild TPW *)
	If[stackHeight==1,
		TPW=simpleWalks,

		walks=Array[MonomialBuilder[ML[[#]][[2]],ML[[#]][[3]],ML[[#]][[4]],Ncrs]->ML[[#]][[1]]&,LNG];
		(*TPW=NCPoly@@{TPW[[1]],Merge[walks,Expand[Total[#]]&]}*)
		TPW=NCPoly@@{TPW[[1]],Merge[walks,Total]};
		TPW=NCExpand[NCPolyProduct[simpleWalks,TPW]]; (* TPW,simpleWalks vs. simpleWalks,TPW *)

(* Implement lemma 4b *)
		If[stackHeight>1,
			Do[
				TPW[[2]]=Association[DeleteCases[TPW[[2]]//Normal,
												HoldPattern[keys_List->_]/;
													(keys[[ncvLen-i-2*Ncrs]]+keys[[ncvLen-i-Ncrs]])>=NC|| (* ai+ci *)
													(keys[[ncvLen-i-2*Ncrs]]+keys[[ncvLen-i]])>=NC]];  (* ai+bi *)
				If[TPW==0,Break[]]
				,{i,1,Ncrs}
			]
		]
(* Print[NCPolyDisplay[TPW,NCvars]];*)
	];

	If[!SameQ[TPW,0],

		walks=Normal[TPW[[2]]];
		LNG=Length[walks];
		ML=Array[BraidMonomialExponentCounter[walks[[#]],Ncrs,localBraid[[All,2]],CJP`q]&,LNG];

		walkWeights=Sum[ML[[j]][[1]]*
						Product[ScriptE[CJP`q,NC,ML[[j]][[4]][[i]],ML[[j]][[2]][[i]],localBraid[[i]][[2]]],{i,Ncrs}]
						,{j,LNG}];

(*		Do[
			If[Exponent[ML[[j]][[1]]*
						Product[ScriptE[CJP`q,NC,ML[[j]][[4]][[i]],ML[[j]][[2]][[i]],localBraid[[i]][[2]]],{i,Ncrs}],CJP`q,Max]>=Exponent[walkWeights,CJP`q,Max],
			Print[(((NC-1)*(writhe-numStrands+1))/2)," Exponent:",Exponent[ML[[j]][[1]]*
						Product[ScriptE[CJP`q,NC,ML[[j]][[4]][[i]],ML[[j]][[2]][[i]],localBraid[[i]][[2]]],{i,Ncrs}],CJP`q,Max],
					" Product: ",ML[[j]][[1]]*
						Product[ScriptE[CJP`q,NC,ML[[j]][[4]][[i]],ML[[j]][[2]][[i]],localBraid[[i]][[2]]],{i,Ncrs}],
					" walk: ", StringReplace[ToString[NCPolyDisplay[NCPoly@@{TPW[[1]],Association[walks[[j]]]},NCvars],StandardForm],"CJP`"->""]]]
		,{j,LNG}];*)


		CJP+=walkWeights;
		loopDone=SameQ[walkWeights,0];
(*		Print[Collect[walkWeights,CJP`q]/.CJP`q->q];*)
		stackHeight++,
		
		loopDone=True
	]
];

CJP*=(CJP`q^(((NC-1)*(writhe-numStrands+1))/2));

(* We collect the q terms to ensure usable output.
   This doubles runtime on average. *)
CJP=Collect[CJP,CJP`q];
If[!NumericQ[q],SetCommutative[q]];
CJP/.CJP`q->q
]

End[]

EndPackage[]

