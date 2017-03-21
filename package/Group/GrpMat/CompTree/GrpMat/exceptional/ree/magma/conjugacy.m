/*******************************************************************************
 *    conjugate.m    Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-06-04
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 09:05:48 +0000 (mÃ¥n, 15 dec 2008)$:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: conjugate.m 1605 2008-12-15 09:05:48Z jbaa004                  $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose ReeConjugacy, 10;

import "standard.m" : getReeInfSylowGenMatrix, exceptionalOuterAutomorphism,
    checkOctonionAlgebra, getReeMagmaForm;
import "ree.m": ReeReductionFormat, ReeReductionMaps;

import "../../../util/basics.m" : getMapFunction, MatSLP, EvaluateMatTup;

import "../../../../classical/rewriting/standard.m" : SLChosenElements;
import "../../../../recog/magma/mathom.m" : RefinedSummandSeries;

forward ConjugationCommonInvCentraliser;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic TestReeConjugacy(startM :: RngIntElt, stopM :: RngIntElt, conjugates :: RngIntElt) -> BoolElt
    {}
        
    for m in [startM .. stopM] do
	F := GF(3, 2 * m + 1);
	S := Ree(F);
	
	print m;
	for i in [1 .. conjugates] do
	    print i;
	    G := RandomConjugate(S);
	    //assert ReeConjugateRecogniser(G);
	    conj := ReeConjugacy(G);
	end for;
	
	S := ChevalleyGroup("2G", 2, F);
	
	for i in [1 .. conjugates] do
	    print i;
	    G := RandomConjugate(S);
	    //assert ReeConjugateRecogniser(G);
	    conj := ReeConjugacy(G);
	end for;
    end for;
    
    return true;
end intrinsic;

function ConjugateRee(G, S, C, CS)
    F := CoefficientRing(G);
    m := (Degree(F) - 1) div 2;
    t := 3^m;
    q := #F;
    
    MA := MatrixAlgebra(F, Degree(G));

    MG := GModule(C);
    MS := GModule(CS);

    M1 := sub<MS | MS.2, MS.4, MS.6>;
    M2 := sub<MS | MS.1, MS.3, MS.5, MS.7>;
    baseMS := MA !
	      ([x * Morphism(M1, MS) : x in Basis(M1)] cat
	       [x * Morphism(M2, MS) : x in Basis(M2)]);

    cbmS := Generic(G) ! baseMS^(-1);
	   	   
    sumG := IndecomposableSummands(MG);

    M1 := rep{M : M in sumG | Dimension(M) eq 3};
    M2 := rep{M : M in sumG | Dimension(M) eq 4};
    baseMG := MA !
	      ([x * Morphism(M1, MG) : x in Basis(M1)] cat
	       [x * Morphism(M2, MG) : x in Basis(M2)]);

    cbmG := Generic(G) ! baseMG^(-1);
    
    CG4 := sub<GL(4, F) | [Submatrix(g, 4, 4, 4, 4) :
	g in UserGenerators(C^cbmG)]>;
    CS4 := sub<GL(4, F) | [Submatrix(g, 4, 4, 4, 4) :
	g in UserGenerators(CS^cbmS)]>;

    sl2Time := Cputime();
    S2 := SL(2, F);
    flag, isoG4, invG4, g2slpG := RecogniseSL2(CG4, #F);
    assert flag;
    flag, isoS4, invS4, g2slpS := RecogniseSL2(CS4, #F);
    assert flag;
    sl2Time := Cputime(sl2Time);

    CS4_stdGens := [Function(invS4)(g) : g in UserGenerators(S2)];
    CG4_stdGens := [Function(invG4)(g) : g in UserGenerators(S2)];
    
    slpsG := [Function(g2slpG)(g) : g in CG4_stdGens];
    slpsS := [Function(g2slpS)(g) : g in CS4_stdGens];

    CG4_fix := sub<Generic(C) | Evaluate(slpsG, UserGenerators(C))>;
    CS4_fix := sub<Generic(CS) | Evaluate(slpsS, UserGenerators(CS))>;

    CG_fix := sub<Generic(G) | UserGenerators(CG4_fix)>;
    CS_fix := sub<Generic(G) | UserGenerators(CS4_fix)>;
    
    CG3 := sub<GL(3, F) | [Submatrix(g, 1, 1, 3, 3) :
	g in UserGenerators(CG_fix^cbmG)]>;
    CS3 := sub<GL(3, F) | [Submatrix(g, 1, 1, 3, 3) :
	g in UserGenerators(CS_fix^cbmS)]>;

    flag, form := SymmetricBilinearForm(S^cbmS);
    assert flag;
    
    form3 := Submatrix(form, 1, 1, 3, 3);
    form4 := Submatrix(form, 4, 4, 4, 4);
    
    CS3_stdGens := UserGenerators(CS3);
    CG3_stdGens := UserGenerators(CG3);

    MG4 := GModule(S2, CG4_stdGens);
    MS4 := GModule(S2, CS4_stdGens);
    twist := 0;
    for i in [1 .. Degree(F)] do
	flag, cbm4 := IsIsomorphic(MG4, FrobeniusImage(MS4, S2, i));
	if flag then
	    twist := i;
	    break;
	end if;
    end for;
    assert flag;
    cbm4 := Generic(CG4) ! cbm4;
    
    MG3 := GModule(S2, CG3_stdGens);
    MS3 := GModule(S2, CS3_stdGens);

    flag, cbm3 := IsIsomorphic(MG3, FrobeniusImage(MS3, S2, twist));
    assert flag;
    cbm3 := Generic(CG3) ! cbm3;
    
    cbm := DiagonalJoin(cbm3, cbm4);
    conj := Generic(G) ! (cbmG * cbm * cbmS^(-1));

    flag, form33 := SymmetricBilinearForm(CG3^cbm3);
    assert flag;
    assert form3 eq form33;

    flag, form44 := SymmetricBilinearForm(CG4^cbm4);
    assert flag;
    assert form4 eq form44;
    
    flag, form := SymmetricBilinearForm(S);
    assert flag;
    
    for g in UserGenerators(C^conj) do
	assert g * form * Transpose(g) eq form;
	assert SpinorNorm(g, form) eq 0;
    end for;

    flag, f1 := SymmetricBilinearForm(G^conj);
    assert flag;

    a := f1[2, 6];
    b := f1[4, 4];
    c := f1[1, 7];
    
    flag, x := IsSquare(-b);
    assert flag;
    flag, y := IsSquare(a);
    assert flag;
    assert c eq 1;
    z := 1;
    
    assert a eq -b;
    assert x eq y;

    conj *:= Generic(G) ! DiagonalMatrix(F, [z, x, z, x, z, x, z]);

    for g in UserGenerators(G^conj) do
	assert g * form * Transpose(g) eq form;
	assert SpinorNorm(g, form) eq 0;
    end for;
    
    return conj, sl2Time;
end function;
    

intrinsic ReeConjugacy(G :: GrpMat : Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true, wordGroup := WordGroup(G)) -> Map, GrpMatElt, RngIntElt
    {G \leq GL(7, q) is a conjugate of Ree(q).

    Return an explicit isomorphism to the standard copy H = G^x,
    as well as such an element x. }

    if CheckInput then
	if not (Degree(G) eq 7 and ReeGeneralRecogniser(G)) then
	    error "Ree conjugation: G must be a Ree conjugate";
	end if;
    end if;
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;
    
    F := CoefficientRing(G);
    q := #F;
    m := (Degree(F) - 1) div 2;
    S := Ree(F);
    WS := WordGroup(S);
    WG := WordGroup(G);
    
    assert ReeStandardRecogniser(S);
    S`RandomProcess := RandomProcessWithWords(S :
	WordGroup := WS, Scramble := 1);

    flag, stdForm := SymmetricBilinearForm(S);
    assert flag;
    
    flag, form := SymmetricBilinearForm(G);
    assert flag;
    
    jS := S.2^((q - 1) div 2);
    SC := sub<Generic(G) | jS, S.1, S.2, getReeInfSylowGenMatrix(F, 0, 1, 0)>;
    SC_PSL := DerivedGroupMonteCarlo(SC : NumberGenerators := 5);
    
    M := GModule(SC_PSL);
    M1 := sub<M | M.2, M.4, M.6>;
    M2 := sub<M | M.1, M.3, M.5, M.7>;
    assert Dimension(M1) eq 3;
    assert Dimension(M2) eq 4;

    conj := Identity(G);
    found := false;
    
    flag, jG := RandomElementOfPrimeOrder(G, 2 : Randomiser := G`RandomProcess);
    assert flag;
    
    completion := func<G, C, g | NumberOfGenerators(C) ge 5>;
    GC := CentraliserOfInvolution(G, jG :
	CompletionCheck := completion,
	Randomiser := G`RandomProcess);
    GC_PSL := DerivedGroupMonteCarlo(GC : NumberGenerators := 5);

    totalSL2Time := 0;
    repeat
	conj2, sl2Time := ConjugateRee(G, S, GC_PSL, SC_PSL);
	totalSL2Time +:= sl2Time;
	
	X := G^conj2;
	flag, form := SymmetricBilinearForm(X);
	assert flag;
	assert form eq stdForm;
	
	if ReeStandardRecogniser(X) then
	    conj *:= conj2;
	    found := true;
	    break;
	end if;
    until found;
        
    ree := G^conj;
    assert ReeStandardRecogniser(ree);
    
    // Construct explicit isomorphism to standard copy
    homo := hom<G -> Generic(ree) | x :-> x^conj>;
    iso := hom<G -> ree | x :-> Function(homo)(x)>;

    if not assigned G`ReeReductionData then
	G`ReeReductionData := rec<ReeReductionFormat |
	    maps := rec<ReeReductionMaps | conjugation := iso>,
	    conjugator := conj>;
    else
	G`ReeReductionData`conjugator := conj;
	if not assigned G`ReeReductionData`maps then
	    G`ReeReductionData`maps :=
		rec<ReeReductionMaps | conjugation := iso>;
	else
	    G`ReeReductionData`maps`conjugation := iso;
	end if;
    end if;
    
    return iso, conj, totalSL2Time;
end intrinsic;
