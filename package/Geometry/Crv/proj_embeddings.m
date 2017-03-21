freeze;

////////////////////////////////////////////////////////////////////////
//            Projective Maps from Linear Systems on Curves           //
//            Revised from orginal code of Gavin Brown                //
//            David Kohel, June 2002                                  //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                      Riemann-Roch Spaces                           // 
////////////////////////////////////////////////////////////////////////

intrinsic RiemannRochSpace(D::DivCrvElt) -> ModFld, Map
    {A vector space and the isomorphism from this space to
    the Riemann-Roch space of function field elements for
    the divisor D.}
    C := Curve(D);
    F := FunctionField(C);
    _,m := AlgorithmicFunctionField(F);
    V,phi := RiemannRochSpace(FunctionFieldDivisor(D));

    /*
    The following was changed to the form below by AKS (Jan 2010)
    to handle the fact that HasPreimage will get runtime error
    in the rule map form otherwise.
    */

    //phi1 := map< V -> F | x :-> phi(x) @@ m, y :-> m(y) @@ phi >;
    phi1 := phi * Inverse(m);

    return V, phi1;
end intrinsic;

intrinsic Basis(D::DivCrvElt) -> SeqEnum
    {A basis of function field elements for the Riemann-Roch space L(D).}
    return [ Codomain(phi) | phi(b) : b in Basis(V) ] where
	V, phi is RiemannRochSpace(D);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                      Projective Embeddings                         //
////////////////////////////////////////////////////////////////////////

/*** Is this function necessary!? Will comment out for now *******
 *****   and replece its use below.

function curve_map(C,P,S)
    // the map of curves C -> P defined by the sequence S 
    // of function field elements.
    R := CoordinateRing(Ambient(C));
    x := R.1; y := R.2; z := R.3; 
    S := [ RationalFunction(f) : f in S ];
    den := LCM([ Denominator(f) : f in S ]);
    S := [ Evaluate(Numerator(f*den),[x,y]) : f in S ];
    deg := Max([ TotalDegree(f) : f in S ]);
    S := [ Homogenization(f,z,deg) : f in S ];
    return map< C -> P | S >;
end function;

***************************************************************/

intrinsic DivisorMap(D::DivCrvElt) -> MapSch
    {The map determined by the complete linear system of D.}
    C := Curve(D);
    V, m := RiemannRochSpace(D);
    dim := Dimension(V)-1; 
    require dim ge 0:
       "Argument 1 must determine a nontrivial Riemann-Roch space.";
    P := ProjectiveSpace(BaseRing(C),dim);
    return map<C->P | [ m(b) : b in Basis(V) ]>;
end intrinsic;

intrinsic DivisorMap(D::DivCrvElt,P::Prj) -> MapSch
    {The map determined by the complete linear system of D
    with image in the projective space P.}
    C := Curve(D);
    require BaseRing(P) cmpeq BaseRing(C) : 
	"The base rings of the arguments must be equal.";
    V, m := RiemannRochSpace(D);
    dim := Dimension(V)-1; 
    require dim ge 0:
       "Argument 1 must determine a nontrivial Riemann-Roch space.";
    require Dimension(P) eq dim : 
	"Dimension of argument 2 must be " * IntegerToString(dim);
    return map<C->P | [ m(b) : b in Basis(V) ]>;
end intrinsic;

intrinsic CanonicalEmbedding(C::Crv) -> Map
    {The projective map determined by the canonical divisor of C}
    return CanonicalMap(C);
end intrinsic;

intrinsic CanonicalMap(C::Crv) -> Map
{"} // "
    V, m := RiemannRochSpace(CanonicalDivisor(C));
    dim := Dimension(V)-1; 
    require dim ge 0:
       "Argument 1 must determine a nontrivial Riemann-Roch space.";
    P := ProjectiveSpace(BaseRing(C),dim);
    return map<C->P | [ m(b) : b in Basis(V) ]>;
end intrinsic;

intrinsic CanonicalEmbedding(C::Crv, P::Prj) -> Map
    {The projective map determined by the canonical divisor of C 
     with image in the projective space P.}
    return CanonicalMap(C,P);
end intrinsic;

intrinsic CanonicalMap(C::Crv,P::Prj) -> Map
{"} // "
    require BaseRing(P) eq BaseRing(C):
	"Base rings of the two arguments must be equal";
    V, m := RiemannRochSpace(CanonicalDivisor(C));
    dim := Dimension(V)-1; 
    require dim ge 0:
       "Argument 1 must determine a nontrivial Riemann-Roch space.";
    require Dimension(P) eq dim : 
	"Dimension of argument 2 must be " * IntegerToString(dim);
    return map<C->P | [ m(b) : b in Basis(V) ]>;
end intrinsic;
 
intrinsic DivisorMap(C::Crv,p::Pt,n::RngIntElt) -> Map
    {The map determined by the complete linear system of D = n*[p],
    where p is a nonsingular point on C}
    //require IsProjective(C) : "Argument must be a projective curve.";
    require Scheme(Parent(p)) cmpeq C and Ring(Parent(p)) cmpeq BaseRing(C) :
        "Argument 2 must be a point over the base field of argument 1.";
    require IsNonsingular(p) : "Argument 2 must be nonsingular.";
    V, m := RiemannRochSpace(n*Divisor(p));
    dim := Dimension(V)-1; 
    require dim ge 0:
       "Argument 2 and 3 must determine a nontrivial Riemann-Roch space.";
    P := ProjectiveSpace(BaseRing(C),dim);
    return map<C->P | [ m(b) : b in Basis(V) ]>;
end intrinsic;
 

