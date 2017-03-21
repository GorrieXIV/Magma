freeze;

/////////////////////////////////////////////////////////////////////////
// directproduct.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 26429 $
// $Date: 2010-05-04 12:15:40 +1000 (Tue, 04 May 2010) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculates the direct product of two or more toric varieties.
/////////////////////////////////////////////////////////////////////////

import "../geometry/map.m": CreateToricVarietyMap;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic '*'(X::TorVar, Y::TorVar) -> TorVar
{The product of toric varieties X and Y}
    Z:=DirectProduct(X,Y);
    return Z;
end intrinsic;

intrinsic DirectProduct(S::[TorVar]) -> TorVar,SeqEnum[TorMap]
{The product of the toric varieties in S, together with the sequence of projection maps}
    // Sanity checks
    require #S ne 0: "Argument 1 must be non-empty";
    k:=BaseRing(Representative(S));
    require &and[BaseRing(X) cmpeq k : X in S]:
        "The varieties must be defined over the smae base ring";
    require IsField(k): "Base ring must be a field";
    
    // First we build the product Cox ring data
    // Construct the product of the coordinate rings
    RZ:=PolynomialRing(k,&+[Rank(CoordinateRing(X)) : X in S]);
    // Now we need to lift the data
    offset:=0;
    IZ:=Ideal(Identity(RZ));
    ZZ:=[PowerSequence(Integers())|];
    QZ:=[PowerSequence(Rationals())|];
    for X in S do
        r:=Rank(CoordinateRing(X));
        // First the contribution from the irrelevant ideal
        emb:=hom<CoordinateRing(X) -> RZ | [RZ.(i+offset) : i in [1..r]]>;
        IZ *:= Ideal([emb(x) : x in Basis(IrrelevantIdeal(X))]);
        // Now append the Z-gradings
        pre:=ZeroSequence(Integers(),offset);
        post:=ZeroSequence(Integers(),Rank(RZ) - r - offset);
        ZZ cat:= [PowerSequence(Integers()) | pre cat grad cat post :
                                                           grad in Gradings(X)];
        // And finally the Q-gradings
        pre:=ZeroSequence(Rationals(),offset);
        post:=ZeroSequence(Rationals(),Rank(RZ) - r - offset);
        QZ cat:= [PowerSequence(Rationals()) | pre cat grad cat post :
                                                   grad in QuotientGradings(X)];
        // Move on
        offset +:= r;
    end for;
    
    // Create the toric variety and assign the product data
    Z:=ToricVariety(RZ,[IZ],ZZ,QZ);
    C:=CoxRing(Z);
    C`summands:=[CoxRing(X) : X in S];
    
    // Now we build the projection maps
    projs:=[];
    offset:=0;
    for X in S do
        // Create the embedding
        r:=Rank(CoordinateRing(X));
        emb:=hom<CoordinateRing(X) -> RZ | [RZ.(i+offset) : i in [1..r]]>;
        // Create the projection data
        is_zero_cone:=ZeroCone(OneParameterSubgroupsLattice(X));
        is_zero_seq:=[Booleans() | false : j in [1..r]];
        principals:=BasisOfRationalFunctionField(X);
        pullback_of_principals:=[FieldOfFractions(RZ) |
                     emb(Numerator(f)) / emb(Denominator(f)) : f in principals];
        // Create the projection map
        proj:=CreateToricVarietyMap(Z,X,principals,pullback_of_principals,
                                      is_zero_seq : is_zero_cone:=is_zero_cone);
        Append(~projs,proj);
        // We can assign a few properties whilst we're here
        proj`is_regular:=true;
        description:=[FamilyOfMultivaluedSections(Z) |
                                                   RZ.(j+offset) : j in [1..r]];
        proj`description:=description;
        proj`is_description_good:=true;
        // Move on
        offset +:= r;
    end for;
    
    // Return the data
    return Z,projs;
end intrinsic;
