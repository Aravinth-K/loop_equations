(* ::Package:: *)

BeginPackage["LoopEquationsGenerator`"];

GenerateAllResolventLoopEquations::usage="Generate all resolvent loop equations.";
GenerateIndividualResolventLoopEquation::usage="Generate an individual resolvent loop equation.";
GenerateAllCorrelatorLoopEquations::usage="Generate all correlator loop equations.";
GenerateIndividualCorrelatorLoopEquation::usage="Generate an individual correlator loop equation.";
InitializeLoopEquationsPackage::usage="Initialize the package with action, fundamentalMatrix, and maxLevel.";
GetResolventVariables::usage="Return list of resolvent variables for a given level."
GetCorrelatorVariables::usage="Return list of correlator variables for a given level."
GetAllResolventVariables::usage="Return list of all resolvent variables.";
GetAllCorrelatorVariables::usage="Return list of all correlator variables.";
GetResolventLoopEquationLevel::usage="Get level of an input resolvent loop equation.";
GetCorrelatorLoopEquationLevel::usage="Get level of an input correlator loop equation.";
GetLongestCorrelatorVariable::usage="Get a single correlator variable with the longest index.";
GetVariationList::usage="Get a list of all possible words corresponding to variations.";

Begin["`Private`"];

extractIndices[term_,symbol_]:=Module[{factors,mFactors,subs},
If[AtomQ[term],Return[{}]];
If[term===symbol||Head[term]===Subscript&&term[[1]]===symbol,If[Head[term]===Subscript,Return[Sort[Sequence@@term[[2;;]]]],Return[{}]]];
factors=List@@term;
mFactors=Select[factors,!FreeQ[#,Subscript[symbol,_]]&];
subs=Flatten[Replace[mFactors,{Subscript[_,sub_]:>{sub},Power[Subscript[_,sub_],pow_]:>Table[sub,{pow}]},{1}]];
Sort[subs]];

augmentList[listOfLists_]:=Module[{reversed,augmented},
reversed=Reverse/@listOfLists;
augmented=Join[listOfLists,reversed];
DeleteDuplicates[augmented]
];

extractAllActionIndices[expr_]:=Module[{rawIndices},
rawIndices=DeleteDuplicates[Map[extractIndices[#,M]&,List@@Expand[expr]]];
Reverse[Sort[ augmentList[rawIndices]]]
];

getLoopSchema[action_]:=Module[{vars},
vars=DeleteDuplicates[Cases[action,Subscript[M,_],Infinity]];
derivatives=Expand@Simplify@D[action,#]&/@vars;
Reverse@Sort[DeleteDuplicates[Flatten[Map[extractAllActionIndices,derivatives],1]]]
];

matrixProductFromIndexList[list_]:=Times@@(Subscript[M,#]&/@list);

extractCoefficients[S_,matrixIndex_,schema_]:=If[
schema==Reverse[schema],
Coefficient[D[S,Subscript[M, matrixIndex]],matrixProductFromIndexList[schema]],
1/2 Coefficient[D[S,Subscript[M, matrixIndex]],matrixProductFromIndexList[schema]]
];

createAllResolventWords[length_]:=If[
length==1,Tuples[DeleteCases[matrixIndexRange,0],1],
If[
length==2,Tuples[DeleteCases[matrixIndexRange,0],2],
Flatten[Table[Prepend[Append[inner,last],first],{first,DeleteCases[matrixIndexRange,0]},{last,DeleteCases[matrixIndexRange,0]},{inner,Tuples[matrixIndexRange,length-2]}],2]]
];

checkIfResolventWordRedundant[word_,positionInList_]:=Module[{length, remainingWordsList},
length=Length[word];
remainingWordsList=Part[Reverse[createAllResolventWords[length]],positionInList+1;;];
If[MemberQ[remainingWordsList,Reverse[word]],0,word]];

createUniqueResolventWords[level_]:=DeleteCases[
Table[
checkIfResolventWordRedundant[Reverse[createAllResolventWords[level]][[i]],i],
{i,1,Length[createAllResolventWords[level]]}
],
0
];

createAllCorrelatorWords[level_]:=Module[{iteratorList},
iteratorList=Table[{Subscript[i, j],matrixIndexRange},{j,1,level}];
Flatten[Table[Table[Subscript[i, j],{j,1,level}], Sequence@@iteratorList//Evaluate],level-1]
];

checkIfCorrelatorWordRedundant[word_,precedingWordPositionInList_]:=Module[
{length,remainingWordsList, wordIncludingHermitianConjugateList},
length=Length[word];
remainingWordsList=Part[createAllCorrelatorWords[length],;;precedingWordPositionInList];
wordIncludingHermitianConjugateList={word,Reverse[word]};
Do[wordIncludingHermitianConjugateList[[k]]=NestList[RotateRight,wordIncludingHermitianConjugateList[[k]],length-1],{k,1,2}];
If[IntersectingQ[remainingWordsList,Join@@wordIncludingHermitianConjugateList],0,wordIncludingHermitianConjugateList[[1,1]]]
];

createUniqueCorrelatorWords[level_]:=Module[{x,allCorrelatorWords,WordsByTraceSymmetry},
allCorrelatorWords=createAllCorrelatorWords[level];
DeleteCases[
Table[
checkIfCorrelatorWordRedundant[
allCorrelatorWords[[Length[allCorrelatorWords]+1-i]],
Length[allCorrelatorWords]-i
],
{i,1,Length[allCorrelatorWords]}
],
0]
];

createVariations[level_]:=Module[{uniquePartitions,createTableIterator, createWordPartitions},
If[
level!=0,
uniquePartitions=Table[If[i!=0,Partition[Table[0,{j,1,level}],UpTo[level-i]],{Table[0,{k,1,level}],{}}],{i,0,Floor[level/2]}];
createTableIterator[partition_]:=If[Length[partition[[2]]]!=0,Join[Table[{Subscript[i, j],matrixIndexRange},{j,1,Length[partition[[1]]]-1}],{{Subscript[i, Length[partition[[1]]]],DeleteCases[matrixIndexRange,0]}},{{Subscript[j, Length[partition[[2]]]],DeleteCases[matrixIndexRange,0]}},Table[{Subscript[j, i],matrixIndexRange},{i,1,Length[partition[[2]]]-1}]],Join[Table[{Subscript[i, j],matrixIndexRange},{j,1,Length[partition[[1]]]-1}],{{Subscript[i, Length[partition[[1]]]],DeleteCases[matrixIndexRange,0]}}]];
createWordPartitions[partition_]:=Flatten[Table[{Table[Subscript[i, j],{j,1,Length[partition[[1]]]}],If[Length[partition[[2]]]!=0,Table[Subscript[j, i],{i,1,Length[partition[[2]]]}],{}]}, Sequence@@createTableIterator[partition]//Evaluate],level-1];
Flatten[Map[createWordPartitions,uniquePartitions],1],
{{},{}}
]
];

InitializeLoopEquationsPackage[action_,matrixDOF_,orientationMatrix_,maxLevelValue_,resolventSymbol_,correlatorSymbol_,argumentSymbol_]:=Module[{localAction,originalMatrixVars,originalMatrixIndexRange,orientationInverse,transformation},

orientationInverse=Simplify@PowerExpand[Inverse[orientationMatrix]];
transformation=(orientationInverse . Table[Subscript[M, i],{i,0,Length[matrixDOF]-1}]);
S=action/. Thread[matrixDOF->transformation];

matrixVars=DeleteDuplicates[Cases[S,Subscript[M,_],Infinity]];
matrixIndexRange=matrixVars/. Subscript[M,n_]:>n;

loopSchema=getLoopSchema[S];
actionCoefficients=Simplify@Table[
(extractCoefficients[S,matrixIndex,schema]/. Thread[matrixVars->0]),
{matrixIndex,matrixIndexRange},
{schema,loopSchema}
];

maxLevel=maxLevelValue;
Do[resolventWords[level]=createUniqueResolventWords[level],{level,1,maxLevel}];
Do[correlatorWords[level]=createUniqueCorrelatorWords[level],{level,1,maxLevel}];
Do[variations[level]=createVariations[level],{level,0,maxLevel-2}];

\[Omega]=resolventSymbol;
p=correlatorSymbol;
z=argumentSymbol;
Subscript[p, {}]=1;
Subscript[p, Null]=1;
Subscript[\[Omega], {}]=\[Omega];
Subscript[\[Omega], Null]=\[Omega];
];

correlatorWordLookup[word_]:=Module[{length,symmetricWordList,symmetricWord},
length=Length[word];
If[length==0,{},
symmetricWordList=Flatten[Table[Subscript[symmetricWord, {i,j}],{i,1,2},{j,1,maxLevel}]];
Subscript[symmetricWord, {1,1}]=word;
For[i=2,i<=length,i++,Subscript[symmetricWord, {1,i}]=RotateRight[Subscript[symmetricWord, {1,(i-1)}]]];
Subscript[symmetricWord, {2,1}]=Reverse[word];
For[i=2,i<=length,i++,Subscript[symmetricWord, {2,i}]=RotateRight[Subscript[symmetricWord, {2,(i-1)}]]];
Which@@Flatten[Table[{MemberQ[correlatorWords[length],Subscript[symmetricWord, {i,j}]],Subscript[symmetricWord, {i,j}]},{i,1,2},{j,1,length}],2]
]];

resolventWordLookup[word_]:=Module[{length,symmetricWord},
length=Length[word];
If[length==0,{},
Subscript[symmetricWord, 1]=word;
Subscript[symmetricWord, 2]=Reverse[word];
Which[MemberQ[resolventWords[length],Subscript[symmetricWord, 1]],Subscript[symmetricWord, 1],MemberQ[resolventWords[length],Subscript[symmetricWord, 2]],Subscript[symmetricWord, 2]]
]
];

splitWordOnResolventLetter[word_]:=Module[{x,rightmostResolventLetterPosition,subwordsListAfterSplit},
If[
Length[word]!=0,
If[
Length[word]!=Length[Position[word,0]],
rightmostResolventLetterPosition=(Position[word,_?(#!=0&),1,1]-{{1}}+Position[Reverse[word],_?(#!=0&),1,1]-{{1}});
subwordsListAfterSplit={Table[0,{i,1,rightmostResolventLetterPosition[[1]][[1]]}],Table[word[[j]],{j,Position[word,_?(#!=0&),1,1][[1]][[1]],Length[word]-Position[Reverse[word],_?(#!=0&),1,1][[1]][[1]]+1}]};,
subwordsListAfterSplit={Table[0,{i,1,Length[Position[word,0]]}],{}};
],
subwordsListAfterSplit={};
];
subwordsListAfterSplit
];

splitWordResolventWordLookup[word_]:=If[Length[word]!=0,{splitWordOnResolventLetter[word][[1]],resolventWordLookup[splitWordOnResolventLetter[word][[2]]]},{{},{}}]

\[CapitalDelta][word_,numberResolventLettersToAdd_]:=Module[{remainingWord,remainingCorrelatorWord,n},
n=numberResolventLettersToAdd;
remainingWord=splitWordResolventWordLookup[word][[2]];
remainingCorrelatorWord[lettersAdded_]:=correlatorWordLookup[Flatten[Append[remainingWord,Table[0,{j,1,lettersAdded-1}]]]];
If[
n==0,
Subscript[\[Omega], remainingWord],
z^n Subscript[\[Omega], remainingWord]-Sum[z^(n-m)  Subscript[p, remainingCorrelatorWord[m]],{m,1,n}]
]
];

createWordsGeneratedByActionVariation[wordList_]:=Flatten[Append[#,wordList[[1]]]]&/@(Flatten[Prepend[#,wordList[[2]]]]&/@loopSchema);

resolventActionContribution[wordList_,matrixNumber_]:=Module[{coefficients,wordsGeneratedByActionVariation,splitAndReducedWords, resolventExpressions},
coefficients=actionCoefficients[[matrixNumber+1]];
wordsGeneratedByActionVariation=createWordsGeneratedByActionVariation[wordList];splitAndReducedWords=Map[splitWordResolventWordLookup,wordsGeneratedByActionVariation];
resolventExpressions=Table[\[CapitalDelta][splitAndReducedWords[[i,2]],Length[splitAndReducedWords[[i,1]]]],{i,1,Length[loopSchema]}];
coefficients . resolventExpressions
];

splitWordListOnLetter[wordList_,matrixNumber_]:=Module[{resolventLetterPositionList, splitWordList},
resolventLetterPositionList=Position[wordList,matrixNumber];
splitWordList[splitPointList_]:=If[
splitPointList[[1]]==1,
{wordList[[1]][[;;splitPointList[[2]]-1]],Join[wordList[[2]],wordList[[1]][[splitPointList[[2]]+1;;]]]},
{wordList[[2]][[splitPointList[[2]]+1;;]],Join[wordList[[2]][[;;splitPointList[[2]]-1]],wordList[[1]]]}];
splitWordList/@resolventLetterPositionList
];

resolventJacobianContribution[wordList_,matrixNumber_]:=Module[{splitWordList, left, right,resolventContribution,wordContributionResolvents,wordContributionCorrelatorWords,wordContribution},
left=wordList[[1]];
right=wordList[[2]];
splitWordList=splitWordListOnLetter[wordList,matrixNumber];
resolventContribution=\[CapitalDelta][left,Length[splitWordResolventWordLookup[left][[1]]]]*\[CapitalDelta][right,Length[splitWordResolventWordLookup[right][[1]]]];
wordContributionResolvents=Table[\[CapitalDelta][splitWordList[[i,2]],Length[splitWordResolventWordLookup[splitWordList[[i,2]]][[1]]]],{i,1,Length[splitWordList]}];
wordContributionCorrelatorWords=Table[correlatorWordLookup[splitWordList[[i,1]]],{i,1,Length[splitWordList]}];
wordContribution=wordContributionResolvents . (List@@(Subscript[p,#]&/@wordContributionCorrelatorWords));
If[matrixNumber==0,
resolventContribution+wordContribution,
wordContribution
]
];

createResolventLoopEquation[wordList_,matrixNumber_]:=resolventActionContribution[wordList,matrixNumber]-resolventJacobianContribution[wordList,matrixNumber];

correlatorActionContribution[wordList_,matrixNumber_]:=Module[{coefficients,wordsGeneratedByActionVariation,reducedWords,correlatorList},
coefficients=actionCoefficients[[matrixNumber+1]];
wordsGeneratedByActionVariation=createWordsGeneratedByActionVariation[wordList];
reducedWords=Map[correlatorWordLookup,wordsGeneratedByActionVariation];
correlatorList=List@@(Subscript[p,#]&/@reducedWords);
coefficients . correlatorList
];

correlatorJacobianContribution[wordList_,matrixNumber_]:=Module[{splitWordList,leftJacobianIndex,rightJacobianIndex},
splitWordList=splitWordListOnLetter[wordList, matrixNumber];
If[splitWordList!={},
leftJacobianIndices=Table[correlatorWordLookup[splitWordList[[splitNumber,1]]],{splitNumber,1,Length[splitWordList]}];
rightJacobianIndices=Table[correlatorWordLookup[Flatten[Append[splitWordResolventWordLookup[splitWordList[[splitNumber,2]]][[2]],Table[0,{j,1,Length[splitWordResolventWordLookup[splitWordList[[splitNumber,2]]][[1]]]}]]]],{splitNumber,1,Length[splitWordList]}];
(List@@(Subscript[p,#]&/@leftJacobianIndices)) . (List@@(Subscript[p,#]&/@rightJacobianIndices)),
0
]];
createCorrelatorLoopEquation[wordList_,matrixNumber_]:=correlatorActionContribution[wordList,matrixNumber]-correlatorJacobianContribution[wordList,matrixNumber];

getVariationList[level_]:=If[
level==0,
{{},{}},
Join[{{{},{}}},Flatten[Table[variations[i],{i,1,level}],1]]
];

GenerateAllResolventLoopEquations[level_]:=Module[{variationList},
variationList=getVariationList[level];
loopEquations=Flatten@Table[createResolventLoopEquation[variation,matrixNumber],{variation,variationList},{matrixNumber,matrixIndexRange}]
];

GenerateIndividualResolventLoopEquation[wordList_,matrixNumber_]:=Module[{},
createResolventLoopEquation[wordList,matrixNumber]
];

GenerateAllCorrelatorLoopEquations[level_]:=Module[{variationList},
variationList=getVariationList[level];
Flatten@Table[createCorrelatorLoopEquation[variation,matrixNumber],{variation,variationList},{matrixNumber,matrixIndexRange}]
];

GenerateIndividualCorrelatorLoopEquation[wordList_,matrixNumber_]:=Module[{},
createCorrelatorLoopEquation[wordList,matrixNumber]
];

GetResolventVariables[level_]:= (List@@(Subscript[\[Omega],#]&/@resolventWords[level]));

GetCorrelatorVariables[level_]:=(List@@(Subscript[p,#]&/@correlatorWords[level]));

GetAllResolventVariables[maxLevel_]:=Module[{resolventWordsList},
resolventWordsList=Flatten[Table[resolventWords[i],{i,1,maxLevel}],1];
(List@@(Subscript[\[Omega],#]&/@resolventWordsList))
];

GetAllCorrelatorVariables[maxLevel_]:=Module[{correlatorWordsList},
correlatorWordsList=Flatten[Table[correlatorWords[i],{i,1,maxLevel}],1];
(List@@(Subscript[p,#]&/@correlatorWordsList))
];

GetResolventLoopEquationLevel[loopEquation_]:=Max[Map[Length,Map[extractIndices[#,\[Omega]]&,List@@Expand[loopEquation]]]];

GetCorrelatorLoopEquationLevel[loopEquation_]:=Max[Map[Length,Map[extractIndices[#,p]&,List@@Expand[loopEquation]]]];

GetLongestCorrelatorVariable[loopEquation_]:=Module[{indices,indexLengths,indexPosition,index},
indices=Map[extractIndices[#,p]&,List@@Expand[loopEquation]];
indexLengths=Map[Length,Map[extractIndices[#,p]&,List@@Expand[loopEquation]]];
indexPosition=First@First@Position[indexLengths,GetCorrelatorLoopEquationLevel[loopEquation]];
index=Part[indices,indexPosition];
Subscript[p, index]
]

GetVariationList[level_]:=getVariationList[level];

End[]

EndPackage[]
