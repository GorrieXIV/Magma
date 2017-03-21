freeze;

//$Id:: dihedral.m 1605 2008-12-15 09:05:48Z jbaa004                       $:

import "basics.m" : MatSLP;

MyAreInvolutionsConjugateWithoutWords := function (G, x, y: 
                                         Central := false, MaxTries := 100)
    
    if Central then fct := CentralOrder; else fct := Order; end if;
    R := RandomProcess (G);
    i := 0;
    repeat
	p := Random(R);
	z := x^p;
	q, r := Quotrem(fct(y * z), 2);
	i +:= 1;
    until r eq 1 or i ge MaxTries;

    if i ge MaxTries then
        return false, _;
    else 
        return true, p * (y * z)^q;
    end if;
end function;

intrinsic AreInvolutionsConjugate (G :: GrpMat, x :: GrpMatElt, y :: GrpMatElt: 
    Central := false, MaxTries := 100) -> BoolElt, GrpMatElt
    {Monte Carlo algorithm to construct element c of G which
     conjugates involution x to involution y. 
     If such c is found, then return true and c, else false.
     If Central then x and y may be projective involutions.
     At most MaxTries random elements are considered.
    }
    if Central then fct := CentralOrder; else fct := Order; end if;
    require fct(x) eq 2 and fct (y) eq 2: "x and y must be involutions";
    return MyAreInvolutionsConjugateWithoutWords (G, x, y: 
           Central := Central, MaxTries := MaxTries);
end intrinsic;

intrinsic AreInvolutionsConjugate (G :: GrpPerm, x :: GrpPermElt, y :: GrpPermElt: 
     Central := false, MaxTries := 100) -> BoolElt, GrpPermElt
    {Monte Carlo algorithm to construct element c of G which
     conjugates involution x to involution y. 
     If such c is found, then return true and c, else false.
     If Central then x and y may be projective involutions.
     At most MaxTries random elements are considered.
    }
    if Central then fct := CentralOrder; else fct := Order; end if;
    require fct(x) eq 2 and fct(y) eq 2: "x and y must be involutions";

    return MyAreInvolutionsConjugateWithoutWords (G, x, y: Central := Central,
         MaxTries := MaxTries);
end intrinsic;

MyAreInvolutionsConjugate :=  function (G, x, wx, y, wy: Central := false, 
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    MaxTries := 100) 

    local p, slp_p, z, q, r, i;

    if Central then fct := CentralOrder; else fct := Order; end if;

    x := rec <MatSLP | mat := x, slp := wx>;
    y := rec <MatSLP | mat := y, slp := wy>;
    
    R := Randomiser;
    i := 0;
    repeat
	p, slp_p := Random(R);
	z := rec<MatSLP | mat := x`mat^p, slp := x`slp^slp_p>;
	q, r := Quotrem(fct(y`mat * z`mat), 2);
	i +:= 1;
    until r eq 1 or i ge MaxTries;

    if i ge MaxTries then
        return false, _, _; 
    else 
        return true, p * (y`mat * z`mat)^q, slp_p * (y`slp * z`slp)^q;
    end if;
end function;

intrinsic AreInvolutionsConjugate (G :: GrpMat, x :: GrpMatElt, wx :: GrpSLPElt,
    y :: GrpMatElt, wy :: GrpSLPElt:  Central := false, 
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    MaxTries := 100) -> BoolElt, GrpMatElt, GrpSLPElt

    {Monte Carlo algorithm to construct element c of G which
     conjugates involution x to involution y. 
     The corresponding SLPs for x and y are wx and wy.
     If such c is found, then return true, c and SLP for c, else false.
     We assume that wx and wy lie in the word group of the 
     random process supplied as Randomiser.
     If Central then x and y may be projective involutions.
     At most MaxTries random elements are considered. 
    }
    if Central then fct := CentralOrder; else fct := Order; end if;
    require fct(x) eq 2 and fct(y) eq 2: "x and y must be involutions";
    return MyAreInvolutionsConjugate (G, x, wx, y, wy: 
        Central := Central, Randomiser := Randomiser, MaxTries := MaxTries);
end intrinsic;

intrinsic AreInvolutionsConjugate (G :: GrpPerm, x :: GrpPermElt, 
    wx :: GrpSLPElt, y :: GrpPermElt, wy :: GrpSLPElt:  Central := false, 
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    MaxTries := 100) -> BoolElt, GrpPermElt, GrpSLPElt

    {Monte Carlo algorithm to construct element c of G which
     conjugates involution x to involution y. 
     The corresponding SLPs for x and y are wx and wy.
     If such c is found, then return true, c and SLP for c, else false.
     We assume that wx and wy lie in the word group of the random process
     supplied as Randomiser. 
     If Central then x and y may be projective involutions.
     At most MaxTries random elements are considered.
    }
    if Central then fct := CentralOrder; else fct := Order; end if;
    require fct(x) eq 2 and fct(y) eq 2: "x and y must be involutions";
    return MyAreInvolutionsConjugate (G, x, wx, y, wy: 
           Central := Central, Randomiser := Randomiser, MaxTries := MaxTries);
end intrinsic;

function DihedralTrick(x, y, R : MaxTries := 1000)
    G := Parent(x`mat);
    flag, g, slp := AreInvolutionsConjugate(G, x`mat, x`slp, y`mat, y`slp :
	Randomiser := R, MaxTries := MaxTries);
    assert flag;

    return rec<MatSLP | mat := g, slp := slp>;
end function;
