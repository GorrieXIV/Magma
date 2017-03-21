freeze;
/////////////////////////////////////////////////////////////////////////////////
//          PARAMETRISATION OF DEGREE 6 DEL PEZZO SURFACES                     //
//                 Main function. mch - 05/06                                  //
/////////////////////////////////////////////////////////////////////////////////

declare verbose ParamDP, 2;

import "p6.m": D6Case;
import "p3.m": D3Case;
import "p2.m": D2Case1, D2Case2,D2Case3;
import "p1_4.m": D1Case, D4Case;

function BasicCheck(I)
    H,d := HilbertPolynomial(EasyIdeal(I));
    return (Coefficients(H) eq [Rationals()|1,3,3]) and (d eq 0);
end function;

intrinsic ParametrizeDegree6DelPezzo(X::Sch :
 	ExistenceOnly := false) -> BoolElt, MapIsoSch
{Determines whether a degree 6 DelPezzo surface is parametrisable.
 If so, it returns a parametrisation. X must be non-singular
 (and anticanonically embedded in P^6)}

    P6 := Ambient(X);
    k := BaseRing(X);
    require (k cmpeq Rationals()) or ISA(Type(k), FldAlg):
	"Surface should be defined over Q or a number field.";
    require IsOrdinaryProjective(X) and (Dimension(P6) eq 6):
	"Scheme is not a degree 6 Del Pezzo.";
    Qs := DefiningEquations(X);
    if (#Qs ne 9) or &or[TotalDegree(f) ne 2 : f in Qs] then
	Saturate(~X);
    end if;
    require BasicCheck(Ideal(X)):
	"Scheme is not a degree 6 Del Pezzo.";

    L := FindLieAlgebra(Ideal(X));
    assert Dimension(L) eq 2;
    L := Basis(L);

    // first find "distinguished" hyperplane whose coefficients
    // are given by non-zero vector in the (1-D) intersection of
    // the kernels of matrices in L
    vecs := &meet[Kernel(Transpose(b)) : b in L];
    assert Dimension(vecs) eq 1;
    //change coords so that hyperplane is x0=0 and restrict to
    //affine patch x0 != 0
    W := sub<V|[e*Transpose(L[1]) : e in Basis(V)] cat
	  [e*Transpose(L[2]) : e in Basis(V)]> where V is Generic(vecs);
    M := Transpose(Matrix(Basis(vecs) cat Basis(W)));
    Minv := M^(-1);
    L := [Minv*l*M : l in L];
    L := [Submatrix(l,2,2,6,6) : l in L];
    mp1 := iso<P6->P6|[&+[Minv[i,j]*P6.j:j in [1..7]]: i in [1..7]],
	[&+[M[i,j]*P6.j:j in [1..7]]: i in [1..7]] : Check := false>;
    X1 := mp1(X);
    mp1 := iso<X1->X|InverseDefiningPolynomials(mp1),
		DefiningPolynomials(mp1) : Check := false>;

    // We now want to find the associative subalgebra of M_6(k)
    // generated by L. The decomposition of this (commutative, semisimple)
    // algebra into simple factors determines the torus type of T
    // where T is the connected component of the automorphism gp of the
    // surface. In fact, we know for the possible types, the algebra
    // generated by any single, non-zero elt of L is the full algebra
    // except in some cases, when either l1,l2 or l1+l2 will
    // generate the full algebra (L=[l1,l2]) unless T is the product
    // of 2 1D tori. In this case either l1+2l2 or L1-2l2 works.
    // Thus we can work directly with the Jordan decomposition of a
    // single elt of L
    for rs in [[1,0],[0,1],[1,1],[1,2],[1,-2]] do
	Lgen := rs[1]*L[1]+rs[2]*L[2];
	_,_,facts := JordanForm(Lgen);
	if &or[facts[i][1] eq facts[j][1]: j in [i+1..#facts], 
			i in [1..#facts]] then
             continue;
	end if;
	break;
    end for;
    assert &and[facts[i][1] ne facts[j][1]: j in [i+1..#facts],i in [1..#facts]];
    assert &and[f[2] eq 1: f in facts]; // Lgen is semi-simple
    facts := [f[1] : f in facts];
    // probably good to check that L[1] & L[2] are both in the algebra
    // generated by this semi-simple elt. !

    //now deal with the individual cases
    degs := Sort([Degree(f): f in facts]);
    case degs:
	when [1,1,1,1,1,1]: //split torus
	    boo,prm := D1Case(Lgen,facts,X1,not ExistenceOnly);
	when [1,1,2,2]: //1st K* [K:k]=2 case
	    boo,prm := D2Case1(Lgen,facts,X1,not ExistenceOnly);
	when [2,2,2]: //(K*)[norm=1] x (K*)[norm=1] [K:k]=2
		      //  or 2nd K* [K:k]=2 case
	    if &and[Coefficient(f,1) eq 0 : f in facts] then
		boo,prm := D2Case3(Lgen,facts,X1,not ExistenceOnly);
	    else
		boo,prm := D2Case2(Lgen,facts,X1,not ExistenceOnly);
	    end if;
	when [3,3]:   //(K*)[norm=1] [K:k]=3
	    boo,prm := D3Case(Lgen,facts,X1,not ExistenceOnly);
	when [2,4]:   //(L*)[normL/K1=1] L=K1.K2 [Ki:k]=2
	    boo,prm := D4Case(Lgen,facts,X1,not ExistenceOnly);
	when [6]:     //(L*)[normL/K1=normL/K2=1] L=K1.K2 [K1:k]=3 [K2:k]=2
	    boo,prm := D6Case(Lgen,X1,not ExistenceOnly);
    else //default
	error "Unknown problem occurred with the Lie algebra of the surface.";
    end case;
    if ExistenceOnly or (not boo) then 
	return boo,_;
    else
	return true,Expand(prm*mp1);
    end if;

end intrinsic;