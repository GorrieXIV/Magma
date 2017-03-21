/******************************************************************************
 *
 *    centraliser.m    Large Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Mark Stather & Henrik B‰‰rnhielm
 *    Dev start : 2005-07-10
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: centraliser.m 1605 2008-12-15 09:05:48Z jbaa004                $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare attributes GrpMat : BigReeCentraliserLayersData;

import "../../../util/section.m" : AllLTModules;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

/* Code contributed by Mark Stather.
 * Cosmetic changes by Henrik B‰‰rnhielm.
 * 
 * Solves the constructive membership problem in an involution centraliser of
 * SL2-type in Big Ree.
 *
 * G is the centraliser, and meatAxeData and filtration are structures
 * returned by MeatAxeMaps.
 *
 * Return maps that writes an element as an SLP in the generators of G.
 */
function SolveWordReeCentraliser(G, meatAxeData, filtration)
    tm := Cputime();
    assert assigned G`BigReeCentraliserLayersData;
    L, phi := AllLTModules(G, G`BigReeCentraliserLayersData);
    vprint LargeReeInvolution, 2 : "Taken ", RealField(5) ! Cputime(tm),
	" to compute all LT modules";
    
    D := G`BigReeCentraliserLayersData;
    M := D[1];
    E := D[2];
    F := D[3];
    mat := D[4];

    K := CoefficientRing(G);
    q := #K;
    p := Characteristic(K);
    e := Degree(K);

    i := rep{i : i in [1 .. #F] | Dimension(F[i]) eq 2};
    count := Dimension(E[i]) - 1;
    type := "2B";
    db := 2;
    OpOrd := q^9;

    alpha := meatAxeData[i]`mprojGen;
    gens := UserGenerators(G);
    ims := UserGenerators(meatAxeData[i]`image);
    W, WtoG := WordGroup(G);
    gens2 := [G.j : j in meatAxeData[i]`genIndices];
    words2 := [W.j : j in meatAxeData[i]`genIndices];

    S := meatAxeData[i]`image;
    flag, _, _, StoW2, W2toS := RecogniseSL2(S);
    if flag eq false then
	return false, _, _;
    end if;
    
    WS := Codomain(StoW2);
    slpEval := meatAxeData[i]`slpMap;
    slpCoercion := meatAxeData[i]`slpCoercion;
    WW := Domain(slpCoercion);
    assert NumberOfGenerators(WW) eq NumberOfGenerators(WS);
    smallSLPCoercion :=
	hom<WS -> WW | [WW.i : i in [1 .. NumberOfGenerators(WW)]]>;
    
    kelts := [* [GL(26, q) | ] : i in [1 .. (#L + 1)] *];
    kwords := [* [W | ] : i in [1 .. (#L + 1)] *];
    
    // Construct Random elements of the Kernel
    R := G`RandomProcess;
    
    for tries in [1 .. 10] do
	relts := [GL(26, q) | ];
	rwords := [W | ];
	
	for i in [1 .. (7 * e)] do
	    relts[i], rwords[i] := Random(R);
	end for;
	
	rims := [GL(db, q) | Function(alpha)(relts[i]) : i in [1 .. #relts]];
	tm := Cputime();
	
	rimwords := [Function(StoW2)(rims[i]) : i in [1 .. #rims]];
	vprint LargeReeInvolution, 2 : "Taken ", Cputime(tm),
	    " to compute words of images";
	
	tm := Cputime();
	preims := Evaluate(rimwords, gens2);
	prewords := Evaluate(rimwords, words2);
	
	vprint LargeReeInvolution, 2 : "Taken ", Cputime(tm),
	    " to compute preimages";
	
	kelts[1] := kelts[1] cat [GL(26,q) | relts[i] * preims[i]^(-1) :
	    i in [1 .. #relts]];
	kwords[1] := kwords[1] cat [W | rwords[i] * prewords[i]^(-1) :
	    i in [1 .. #relts]];
	
	// Now move down the layers
	V := [VectorSpace(L[i]) : i in [1 .. #L]];
	InvIms := [[GL(26, q) | ] : i in [1 .. #L]];
	InvImsWords := [[W | ] : i in [1 .. #L]];
	
	IL := [];
	IV := [* *];
	ILSLP := [];
	ILtoSLP := [* *];
	
	for i in [1 .. #L] do
	    vprint LargeReeInvolution, 2 : "In Layer ", i;
	    
	    ims := [phi[i](kelts[i][j]) : j in [1 .. #kelts[i]]];
	    IL[i] := sub<L[i] | ims>;
	    
	    // Find a basis for IL[i] as a vector space
	    B := [V[i] | ];  
	    for j in [1 .. #ims] do
		if IsIndependent(B cat [V[i] ! ims[j]]) then
		    Append(~B, V[i] ! ims[j]);
		    Append(~InvIms[i], kelts[i][j]); 
		    Append(~InvImsWords[i], kwords[i][j]);
		end if;
	    end for;
	    
	    // Add Random conjugates until dim(IV[i]) eq dim(IM[i])  
	    for j in [1 .. (Dimension(IL[i]) - #B)] do
		repeat
		    g, gword := Random(R);
		    r := Random([1 .. #kelts[i]]);
		    k := kelts[i][r]^g;
		    im := phi[i](k);
		until IsIndependent(B cat [V[i] ! im]);
		
		Append(~B, V[i] ! im);
		kword := kwords[i][r]^gword;
		
		Append(~ims, im);
		Append(~InvIms[i], k); 
		Append(~InvImsWords[i], kword);
		Append(~kelts[i], k);
		Append(~kwords[i], kword);
	    end for;
	    
	    phi[i] := function(g : test := true)
		if not test then
		return phi[i](g);
	    end if;
	    
	    im := phi[i](g); 
	    if im notin IL[i] then
		return false;
	    end if;
	    return im;
	end function;
	
	IV[i] := VectorSpaceWithBasis(B);
	ILSLP[i] := SLPGroup(#B);
	if #B gt 0 then
	    ILtoSLP[i] := map<IL[i] -> ILSLP[i] | x :->
	    &*[ILSLP[i].j^(IntegerRing() ! t[j]) : j in [1 .. #B] ]
		where t := Coordinates(IV[i], V[i] ! (L[i] ! x))>;
	else
	    ILtoSLP[i] := map<IL[i] -> ILSLP[i] | x :-> ILSLP[i] ! 1>;
	end if;
	
	// Construct Random Elements of the kernel of phi[i]
	RK := RandomProcess(SLPGroup(#kelts[i]));
	rwords := [Random(RK) : j in [1 .. #kelts[i]]];
	relts := Evaluate(rwords, kelts[i]);
	rwords := Evaluate(rwords, kwords[i]);
	
	rims := [phi[i](relts[j]) : j in [1 .. #relts]];
	rimwords := [ILtoSLP[i](rims[j]) : j in [1 .. #rims]];
	
	prewords := Evaluate(rimwords, InvImsWords[i]);
	preims := Evaluate(rimwords, InvIms[i]);
	
	kelts[i + 1] := kelts[i + 1] cat
	    [GL(26, q) | relts[j] * preims[j]^(-1) : j in [1 .. #preims]];
	kwords[i + 1] := kwords[i + 1] cat [W | rwords[j] * prewords[j]^(-1) :
	    j in [1 .. #preims]];
    end for;

    if &*[#IL[i] : i in [1 .. #IL] ] eq OpOrd then
	break;
    end if;

    if tries eq 10 then
	return false, _, _;
    end if;
    vprint LargeReeInvolution, 2 :
	"Failed to find entire O_p(G), trying harder!";
end for;

GtoW := function(g)
    x := Function(alpha)(g); 
if x cmpeq false then
    return false; 
end if;

wx := Function(StoW2)(Generic(Domain(StoW2)) ! x);
if wx cmpeq false then
    return false;
end if;

w := (smallSLPCoercion * slpCoercion)(wx);
h := (smallSLPCoercion * slpEval)(wx);

g2 := [Generic(G) | ];
w2 := [W | ];

g2[1] := g * h^(-1);
if not IsLowerTriangular(mat * g2[1] * mat^(-1)) then
    return false;
end if;

for i in [1 .. #L] do
    im := phi[i](g2[i] : test := true);
    if im cmpeq false then
	return false;
    end if;
    
    imSLP := ILtoSLP[i](im);
    h := Evaluate(imSLP, InvIms[i]);
    w2[i] := Evaluate(imSLP, InvImsWords[i]);
    g2[i + 1] := g2[i] * h^(-1);
end for;

w := &*[w2[i] : i in [#w2 .. 1 by (-1)]] * w;
return w;
end function;

return true, GtoW, WtoG, smallSLPCoercion;
end function;    


