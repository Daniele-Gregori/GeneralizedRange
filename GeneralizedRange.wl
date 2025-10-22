(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["DanieleGregori`GeneralizedRange`"];


AlgebraicRange::usage=
"AlgebraicRange[x] gives the range of square roots Sqrt[Range[1, x^2]], for x > 1;
AlgebraicRange[x, y] gives the range of square roots Sqrt[Range[x^2, y^2]], for x, y > 0;
AlgebraicRange[x, y, s] gives a square root range with steps bounded above by s > 0;
AlgebraicRange[x, y, s, d] requires the steps of the square root range to be bounded below by d > 0;
AlgebraicRange[{r}, {x}] gives the range of algebraic numbers Range[1, x^r]^(1/r), for x > 1;
AlgebraicRange[{r}, {x, y}] gives the range of algebraic numbers Range[x^r, y^r]^(1/r), for x, y > 0;
AlgebraicRange[{r}, {x, y, s}] gives an algebraic range with steps bounded above by s > 0;
AlgebraicRange[{r}, {x, y, s}, d] requires the steps of the algebraic range to be bounded below by d > 0;
AlgebraicRange[{r1, r2, ...}, {x, y, s}, d] generates the algebraic numbers of root orders r1, r2, ...;
AlgebraicRange[r, {x, y, s}, d] generates all the algebraic numbers of integer root orders up to r.";


Begin["`Private`"];


(* ::Section:: *)
(*AlgebraicRange*)


(* ::Subsection:: *)
(*Helper functions*)


(* ::Subsubsection::Closed:: *)
(*FormulaComplexity*)


(* ::Input::Initialization:: *)
ClearAll[formulaComplexity]

digitSum[int_Integer]:=If[$VersionNumber>=14,DigitSum[int],Total@IntegerDigits[int]]

formulaComplexity[form_?NumericQ]:=
	N@Total[Cases[
			Inactivate[form]
		/.const_?(Quiet@MemberQ[Attributes[#],Constant]&):>1
			/.c_Complex:>ReIm[c]
				/.r:Rational[i1_Integer,i2_Integer]:>{i1,i2}
					/.Inactive[Sqrt][arg_]:>Inactive[Sqrt[{arg,arg}]]
						/.Alternatives[
							Inactive[Power][b_,Inactive[Times][m_,Inactive[Power][n_,-1]]|{m_,n_}],
							Inactive[Power][{b_},Inactive[Times][m_,Inactive[Power][n_,-1]]|{m_,n_}]]:>
								Table[b,Abs[n]+Abs[m]],
			_Integer,{0,Infinity}]/. j_Integer?NonPositive:>-j+1
				/.i_Integer:>Mean[1/2{5IntegerLength[i],digitSum[i],Total[Last/@FactorInteger[i]],Sqrt[Abs[N[i]]]}]]


(* ::Subsubsection::Closed:: *)
(*Utilities*)


(* ::Input::Initialization:: *)
falseQ[prop_]:=
	If[prop===False,True,False]


(* ::Input::Initialization:: *)
combNQ[opts:OptionsPattern[AlgebraicRange]]:=
	Apply[And,falseQ/@OptionValue[
						{"LinearCombinations",
						"FractionalCombinations",
						"ProductCombinations",
						"NestedCombinations"}]]


(* ::Input::Initialization:: *)
realReplace[x_]:=If[Head[x]===Real,RootApproximant[x],x]


(* ::Subsubsection::Closed:: *)
(*Error management*)


(* ::Input::Initialization:: *)
failureThrow[arg_]:=
	If[MemberQ[arg,_Failure|$Failed,{0,Infinity}],
		Throw@First@Union@Cases[arg,_Failure|$Failed,{0,Infinity}],
		arg]


(* ::Subsection:: *)
(*Basic range*)


(* ::Subsubsection::Closed:: *)
(*Elementary range*)


(* ::Input::Initialization:: *)
ClearAll[elemRange]
elemRange[{ord_},{r1_},opts:OptionsPattern[AlgebraicRange]]/;r1>=1:=
	Range[1,r1^ord]^(1/ord)
elemRange[{ord_},{r1_},opts:OptionsPattern[AlgebraicRange]]/;r1<1:=
	{}

elemRange[{ord_},{r1_,r2_},opts:OptionsPattern[AlgebraicRange]]/;0<=r1<=r2:=
	Range[r1^ord,r2^ord]^(1/ord)
elemRange[{ord_},{r1_,r2_},opts:OptionsPattern[AlgebraicRange]]/;r1<0&&r2>=0:=
	Join[-elemRange[{ord},{0,-r1},opts],elemRange[{ord},{0,r2},opts]]//cleanSort
elemRange[{ord_},{r1_,r2_},opts:OptionsPattern[AlgebraicRange]]/;r1<=r2<=0:=
	-elemRange[{ord},{-r2,-r1},opts]//cleanSort
elemRange[{ord_},{r1_,r2_},opts:OptionsPattern[AlgebraicRange]]/;r2<r1:=
	{}


elemRange[{ord_},{r1_,r2_,-1},opts:OptionsPattern[AlgebraicRange]]/;r1>=r2>=0:=
	Range[r1^ord,r2^ord,-1]^(1/ord)
elemRange[{ord_},{r1_,r2_,-1},opts:OptionsPattern[AlgebraicRange]]/;r2<0&&r1>=0:=
	Join[-elemRange[{ord},{-r2,0,-1},opts],elemRange[{ord},{r1,0,-1},opts]]//cleanSort//Reverse
elemRange[{ord_},{r1_,r2_,-1},opts:OptionsPattern[AlgebraicRange]]/;r2<=r1<=0:=
	-elemRange[{ord},{-r2,-r1,-1},opts]//cleanSort//Reverse
elemRange[{ord_},{r1_,r2_,-1},opts:OptionsPattern[AlgebraicRange]]/;r2>r1:=
	{}


(* ::Input::Initialization:: *)
fareyRange[r1_,r2_,r3_]/;r3>0:=
	If[r3>=1,
		ResourceFunction["FareyRange"][r1,r2,r3],
		If[MatchQ[r3,Rational[1,_]],
			ResourceFunction["FareyRange"][r1,r2,1/r3],
			$Failed]]


(* ::Input::Initialization:: *)
elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;0<=r1<=r2&&r3>0:=
	If[!OptionValue["FareyRange"],
		Range[r1^ord,r2^ord,r3^ord]^(1/ord),
		fareyRange[r1^ord,r2^ord,r3^ord]^(1/ord)]

elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<0&&r2>=0&&r3>0:=
	Join[-elemRange[{ord},{0,-r1,r3},opts],elemRange[{ord},{0,r2,r3},opts]]//cleanSort
elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<=r2<=0&&r3>0:=
	-elemRange[{ord},{-r2,-r1,r3},opts]

elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;0<=r2<=r1&&r3<0:=
	Range[r1^ord,r2^ord,-(-r3)^ord]^(1/ord)
elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<0&&r1>=0&&r3<0:=
	Join[-elemRange[{ord},{-r2,0,r3},opts],elemRange[{ord},{r1,0,r3},opts]]//cleanSort
elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<=r1<=0&&r3<0:=
	-elemRange[{ord},{-r2,-r1,r3},opts]

elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<r1&&r3>=0:=
	{}
elemRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<r2&&r3<=0:=
	{}


(* ::Subsubsection::Closed:: *)
(*Step range*)


(* ::Input::Initialization:: *)
ClearAll[factorRange]
factorRange[{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]:=
	Block[{max},
	max=Max[Abs[r1],Abs[r2]];
	If[!OptionValue["FareyRange"],
		If[r3>0,
			Range[0,max,r3],
			-Range[0,-max,r3]],
		If[r3>0,
			#,
			Reverse[#]]
		&@fareyRange[0,max,Abs@r3]//failureThrow]]


(* ::Input::Initialization:: *)
ClearAll[outerRange]
outerRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<=r2&&r3>0:=
	Select[
	Outer[
		Times,
		elemRange[{ord},{r1,r2},opts],
		factorRange[{r1,r2,r3},opts]
		]//Flatten//cleanSort,
	r1<=#<=r2&]
outerRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<=r1&&r3<0:=
	Select[
	Outer[
		Times,
		elemRange[{ord},{r1,r2,-1},opts],
		factorRange[{r1,r2,r3},opts]
		]//Flatten//cleanSort//Reverse,
	r2<=#<=r1&]
outerRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r2<r1&&r3>=0:=
	{}
outerRange[{ord_},{r1_,r2_,r3_},opts:OptionsPattern[AlgebraicRange]]/;r1<=r2&&r3<=0:=
	{}


(* ::Input::Initialization:: *)
ClearAll[stepRange]
stepRange[{ord_},{r1_,r2_,r3_:1},opts:OptionsPattern[AlgebraicRange]]:=
	Which[
	OptionValue["StepMethod"]==="Outer",
		outerRange[{ord},{r1,r2,r3},opts],	
	OptionValue["StepMethod"]==="Root",
		elemRange[{ord},{r1,r2,r3},opts]]


(* ::Subsubsection::Closed:: *)
(*Restricted range*)


cleanSort[list_List]:=SortBy[DeleteDuplicates[list],N]


(* ::Input::Initialization:: *)
complexitySelect[list_List,c_]:=
	Select[list,formulaComplexity[#]<=c&]

ClearAll[stepSelect]
stepSelect[list_List,d_]:=
	Block[{sel,eln,i},
	eln=list[[1]];
	sel={eln};
	
	For[i=2,i<=Length[list],i++,
		
		If[Abs[list[[i]]-eln]>=d,

			eln=list[[i]];
			AppendTo[sel,eln],
			
			Continue[]]];
	
	sel]~Quiet~N::meprec

stepSelect[{},d_,t_:0]:=
	{}


(* ::Input::Initialization:: *)
restrictRange[main_,compl_,d_:0]:=
	If[d!=0,stepSelect[#,d],#]&[complexitySelect[main,compl]]


(* ::Subsection:: *)
(*Combined range*)


(* ::Subsubsection::Closed:: *)
(*Combinations operations*)


(* ::Input::Initialization:: *)
generateLinear[list___]:=
	Outer[Plus,list]//Flatten//DeleteDuplicates
generateLinear[{list__}]:=
	generateLinear[list]
generateLinear[{list_}]:=
	list


(* ::Input::Initialization:: *)
ClearAll[generateFractional]
generateFractional[{list1_List,list2_List}]:=
	DeleteCases[
		Quiet[
			Outer[#1/#2&,generateLinear[list1],generateLinear[list2]]
			//Flatten//DeleteDuplicates,
			{Power::infy,Infinity::indet}],
		Alternatives[ComplexInfinity,Indeterminate,_DirectedInfinity]]
generateFractional[list_List]/;ArrayDepth[list]===1:=
	DeleteCases[
		Quiet[
			Outer[#1/#2&,list,list]
			//Flatten//DeleteDuplicates,
			{Power::infy,Infinity::indet}],
		Alternatives[ComplexInfinity,Indeterminate,_DirectedInfinity]]


(* ::Input::Initialization:: *)
generateProduct[list___]:=
	Outer[Times,list]//Flatten//DeleteDuplicates


(* ::Input::Initialization:: *)
ClearAll[discardNest]
discardNest[list_List,ord_?NumericQ]:=
	DeleteCases[list,_?(MemberQ[#,Power[_,Rational[_,ord]],{0,Infinity}]&)]
discardNest[list_List,ordL_List]:=
	DeleteCases[list,_?(MemberQ[#,Power[_,Rational[_,Alternatives@@ordL]],{0,Infinity}]&)]
discardNest[list_List,{ord_}]:=
	discardNest[list,ord]
		
ClearAll[rootNested]
rootNested[ord_List]:=
	Block[{len,slots,roots},
	len=Length[ord];
	slots=Table[Slot[i],{i,len}];
	roots=PadRight[Map[Function[{x},x^(1/#)]&,ord],len,ord[[-1]]];
	Module[{f=roots[[-1]][slots[[-1]]]},
		MapThread[(f=#2[#1+f])&,{Reverse@Drop[slots,-1],Reverse@Drop[roots,-1]}];
		f]]

ClearAll[generateNested]
generateNested[list_List,ord_List,opt_]:=
	Block[{fun,outer,simp,real},
	fun=rootNested[ord];
	outer=Outer[Evaluate@fun&,Sequence@@Table[list,Length@ord]]//Flatten//DeleteDuplicates;
	simp=Which[
			opt===False,
				outer,
			MatchQ[opt,_?NumericQ|{_?NumericQ..}],
				discardNest[outer,opt],
			True,
				$Failed]//failureThrow;
	real=Cases[simp,_?(FreeQ[N@#,_Complex]&)]]


(* ::Subsubsection::Closed:: *)
(*Generate combinations*)


ClearAll[generateCombination]
generateCombination[{ord_},{r1_,r2_,r3_},base_List,type_String,opts:OptionsPattern[AlgebraicRange]]:=
	Block[{optL,optF,optN,optD,optP,optS,comb},
	{optL,optF,optN,optD,optP,optS}=OptionValue[{"LinearCombinations","FractionalCombinations","NestedCombinations","NestDiscard","ProductCombinations","BasicRange"}];
	comb=Switch[type,
			"Linear",
				Which[
					optL===False,
						{},
					optL===True,
						generateLinear[base,base],
					IntegerQ[optL],
						generateLinear[Sequence@@Table[base,optL]],
					True,
						$Failed],
			"Fractional",
				Which[
					optF===False,
						{},
					optF===True||optF===1||optF==={1,1},
						generateFractional[base],
					IntegerQ[optF],
						generateFractional[Table[Table[base,optF],2]],
					ListQ[optF]&&IntegerQ[optF[[1]]]&&IntegerQ[optF[[2]]],
						generateFractional[Map[Table[base,optF[[#]]]&,Range[2]]],
					True,
						$Failed],
			"Product",
				Which[
					optP===False,
						{},
					optP===True,
						generateProduct[base,base],
					IntegerQ[optP],
						generateProduct[Sequence@@Table[base,optP]],
					MatchQ[optP,{_Integer..}],
						generateLinear@Map[generateProduct[Sequence@@Table[base,#]]&,optP],
					True,
						$Failed],
			"Nested",
				Which[
					optN===False,
						{},
					optN===True,
						generateNested[base,{2,2},optD],
					IntegerQ[optN],
						generateNested[base,{optN,optN},optD],
					MatchQ[optN,{_?NumericQ..}],
						generateNested[base,optN,optD],
					True,
						$Failed]];
		Join[-comb,comb]]


(* ::Subsubsection::Closed:: *)
(*Combined ranges*)


(* ::Input::Initialization:: *)
ClearAll[combinedRange]
combinedRange[{ord_},{r1_,r2_,r3_},base_List,opts:OptionsPattern[AlgebraicRange]]:=
	Module[{comb,join,selQ,sel,sort},
comb=Map[generateCombination[{ord},{r1,r2,r3},base,#,opts]&,{"Linear","Fractional","Product","Nested"}]//Flatten//DeleteDuplicates;
join=If[OptionValue["BasicRange"],Join[comb,base],comb]//DeleteDuplicates;
selQ=If[r3>0,r1<=#<=r2&,r2<=#<=r1&];
sel=Select[join,selQ];
sort=SortBy[sel,N];
If[r3>0,sort,Reverse@sort]]


(* ::Input::Initialization:: *)
ClearAll[combineRestrictRange]
combineRestrictRange[{ord_},{r1_,r2_,r3_},d_,base_List,opts:OptionsPattern[AlgebraicRange]]:=
	Block[{restrrange},
			If[!OptionValue["RestrictCombinations"],

						combinedRange[{ord},{r1,r2,r3},base,opts],

						If[OptionValue["FormulaComplexity"]===Infinity&&d==0,$Failed]//failureThrow;
						restrrange=restrictRange[base,OptionValue["FormulaComplexity"],d];
						combinedRange[{ord},{r1,r2,r3},restrrange,opts]]]	


(* ::Subsection::Closed:: *)
(*Main definition*)


(* ::Input::Initialization:: *)
ClearAll[AlgebraicRange,iAlgebraicRange]

Options[AlgebraicRange]={"FareyRange"->False,"FormulaComplexity"->Infinity,"StepMethod"->"Outer","LinearCombinations"->False,"FractionalCombinations"->False,"ProductCombinations"->False,"NestedCombinations"->False,"BasicRange"->True,"NestDiscard"->False,"RestrictCombinations"->False};

iAlgebraicRange[{ord_?NumericQ},{r1_,r2_,r3_:1},d_:0,opts:OptionsPattern[AlgebraicRange]]:=
	Block[{o,x,y,s,mainrange,fullrange},

		{o,x,y,s}=realReplace/@{ord,r1,r2,r3};
		
		mainrange=If[r3===1,
					elemRange[{o},{x,y}],
					stepRange[{o},{x,y,s},opts]];

		fullrange=If[combNQ[opts],
					mainrange,
					combineRestrictRange[{o},{x,y,s},d,mainrange,opts]]//failureThrow//Catch;

		restrictRange[fullrange,OptionValue["FormulaComplexity"],d]//failureThrow]//Catch

AlgebraicRange[{ord_?NumericQ},{r1_,r2_,r3_:1},d_:0,opts:OptionsPattern[AlgebraicRange]]/;d>=0:=
	iAlgebraicRange[{ord},{r1,r2,r3},d,opts]

AlgebraicRange[{ord_?NumericQ},{r1_},d_:0,opts:OptionsPattern[AlgebraicRange]]/;d>=0:=
	iAlgebraicRange[{ord},{1,r1,1},d,opts]

AlgebraicRange[ordL_List,rL_List,d_:0,opts:OptionsPattern[AlgebraicRange]]/;(Length[ordL]>=2&&d>=0):=
	Block[{stepNegQ,join,sort},
	stepNegQ=Length[rL]==3&&rL[[3]]<0;
	join=Join@@Map[AlgebraicRange[{#},rL,d,opts]&,ordL]//failureThrow;
	sort=If[stepNegQ,Reverse[#],#]&@cleanSort@join;
	If[d!=0,stepSelect[sort,d],sort]]//Catch

AlgebraicRange[ord_Integer,rL_List,d_:0,opts:OptionsPattern[AlgebraicRange]]/;d>=0:=
	AlgebraicRange[Range[2,ord],rL,d,opts]

AlgebraicRange[r1_?NumericQ,r2_?NumericQ,r3_:1,d_:0,opts:OptionsPattern[AlgebraicRange]]/;NumericQ[r3]&&d>=0:=
	AlgebraicRange[2,{r1,r2,r3},d,opts]

AlgebraicRange[r1_?NumericQ,opts:OptionsPattern[AlgebraicRange]]:=
	AlgebraicRange[2,{1,r1,1},0,opts]

AlgebraicRange[_,_List,d_,opts:OptionsPattern[AlgebraicRange]]/;d<0:=
	$Failed


(* ::Section:: *)
(*Package Footer*)


End[];
EndPackage[];
