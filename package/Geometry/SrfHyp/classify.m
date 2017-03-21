// *********************************************************************
// * Package: classify.mag                                             *
// * =====================                                             *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 11.1.2007                                                 *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Classify surfaces according to adjoint maps.                    *
// *                                                                   *
// * TODO:                                                             *
// * -----                                                             *
// *                                                                   *
// *   - Improve image/inverse computation because degrees are known.  *
// *   - Simplify procedure for decision between cases '3a' and '3b'.  *
// *   - Improve cases '3a' and '4' using the extra knowledge of the   *
// *     map that makes the pencil explicit                            *
// *                                                                   *
// *********************************************************************
freeze;

import "adjoints.m": homAdjoints;


// ============================================================================
// = Workaround/bugfix for MAGMA's rational inversion (in Geometry/Sch/map.m) =
// ============================================================================
// (Bug is reported and should be fixed in versions later than V2.14-7.
//  Delete the following then!)

function Combine(L)
  if #L eq 1 then
    return [[l]:l in L[1]];
  else
    M:=$$(L[2..#L]);
    return [ [a] cat l : a in L[1], l in M];
  end if;
end function;

function myInvertible(phi : Maximal:=false)
  if HasKnownInverse(phi) then
    return true, Inverse(phi);
  end if;

  X:=Domain(phi);
  Y:=Codomain(phi);
  
  phi:=Expand(phi);

  //Presently, we assume X and Y are irreducible, i.e., if we have
  //an affine patch Xa of X with Dimension(Xa) eq Dimension(X), then
  //there is no component of X at infinity. A better, but slightly more
  //expensive test would apply for equidimensional X: As soon has we have a
  //patch Xa of X such that HyperPlaneAtInfinity(Ambient(Xa)) meet X
  //has dimension smaller than X, we know there's no component at infinity.
  
  if IsAffine(X) then
    Xa:=X;
    XaPC:=IdentityMap(X);
  else
    if not #Gradings(X) eq 1 then error
      "Domain is only allowed to have 1 grading.";
    end if;
    if not exists(Xa){AffinePatch(X,i): i in [1..Length(X)]|
       HasAffinePatch(X, i) and Dimension(AffinePatch(X,i)) eq Dimension(X)}
       then error
         "None of the standard patches seems to work for X";
    end if;
    XaPC:=map<Xa->X|DefiningPolynomials(f),InverseDefiningPolynomials(f)>
      where f:=ProjectiveClosureMap(Ambient(Xa));
  end if;
  
  if IsAffine(Y) then
    Ya:=Y;
    YaPC:=IdentityMap(Y);
  else
    if not #Gradings(X) eq 1 then error
      "Codomain is only allowed to have 1 grading.";
    end if;
    if not exists(Ya){AffinePatch(Y,i): i in [1..Length(Y)]|
       HasAffinePatch(Y, i) and Dimension(AffinePatch(Y,i)) eq Dimension(Y)}
       then error
         "None of the standard patches seems to work for Y";
    end if;
    YaPC:=map<Ya->Y|DefiningPolynomials(f),InverseDefiningPolynomials(f)>
        where f:=ProjectiveClosureMap(Ambient(Ya));
  end if;
  
  XatoYa:=XaPC*phi*Inverse(YaPC);
  
  fs:=Parent([[FieldOfFractions(Parent(Xa.1))|]])!
                                          AllDefiningPolynomials(XatoYa);
  
  //although we want to eliminate the first variables eventually, we only
  //want to do that on one component of the graph. To find that component,
  //we need to eliminate the last variables first. That explains the present
  //order. We'll change it later to the other way around.
  
  A:=PolynomialRing(BaseRing(Xa),Length(Xa)+Length(Ya),"elim",
             [Length(Xa)+1..Length(Xa)+Length(Ya)]);
  xA:=[A.i:i in [1..Length(Xa)]];
  yA:=[A.i:i in [Length(Xa)+1..Length(Xa)+Length(Ya)]];
  xXa:=[Xa.i: i in [1..Length(Xa)]] cat [0: i in [1..#yA]];
  yYa:=[0: i in [1..#xA]] cat [Ya.i: i in [1..Length(Ya)]];
  J:=ideal<A | [Evaluate(g,xA):g in DefiningEquations(Xa)] cat
              [Evaluate(g,yA):g in DefiningEquations(Ya)] cat
              &cat[[Evaluate(Denominator(f[i]),xA)*yA[i]-
                    Evaluate(Numerator(f[i]),xA):
                  i in [1..#yA]]:f in fs]>;
                  
  //Remove unwanted component
  
  badJ:=ideal<A|[Evaluate(g,xA):g in DefiningEquations(BaseScheme(XatoYa))] cat
              [Evaluate(g,yA):g in DefiningEquations(Ya)]>;
  Jpr := Saturation(J,badJ);
  if Ideal(Domain(XatoYa)) ne ideal<Universe(xXa) |
       [Evaluate(g,xXa): g in Basis(EliminationIdeal(Jpr,Seqset(xA)))]> then
    //print "Computed component does not project back to domain.";
    return false,_;
  end if;
        
  Jpr:=ChangeOrder(Jpr,"elim",[1..#xA]);
  
  //We take a Groebner basis & reverse it
  //We sort out the basis elements in the following way:
  //L[i] contains all elements from bs that have degree 1 in xA[i] and
  //degree 0 in xA[j] for j in [1..i-1].
  
  bs:=Reverse(GroebnerBasis(Jpr));
  L:=[[]:i in [1..#xA]];
  for v in Reverse([1..#xA]) do
    L[v]:=[g: g in bs | Degree(g,v) eq 1 and
                  forall{ i : i in [1..v-1] | Degree(g,i) eq 0}];
  end for;

  if exists{b:b in L|#b eq 0} then
    return false,_;
  end if;

  img:=[b:b in bs | forall{i: i in [1..#xA] | Degree(b,i) eq 0}];
  img:=[Evaluate(f,yYa):f in img];
  if Ideal(Scheme(Ambient(Ya),img)) ne Ideal(Ya) then
    //print "Map does not seem to be dominant.";
    return false,_;
  end if;
  
  //if only one patch is required, throw away the other equations.
    
  if not(Maximal) then
    L:=[[l[#l]]:l in L];
  end if;

  L:=Combine(L);

  R:=[];
  for j in [1..#L] do
    sol:=ChangeUniverse(xA cat yA,FieldOfFractions(A));
    for v in Reverse([1..#xA]) do
      f:=L[j][v];
      assert Degree(f,v) eq 1;
      fsol:=Evaluate(f,sol);
      if Type(fsol) eq FldFunRatMElt then
        num:=Numerator(fsol);
        den:=Denominator(fsol);

        // The denominator better be irrelevant. 
        assert Degree(den,v) eq 0;
      else
        num:=fsol;
      end if;
      sol[v]:=-Term(num,v,0)/Term(num,v,1)*xA[v];
    end for;
    R[#R+1]:=[MyEval(f,yYa):f in sol[1..#xA]];
  end for;
  
  YatoXa:=map<Ya->Xa|R>;
  fi:=AllDefiningPolynomials(Inverse(YaPC)*YatoXa*XaPC);
  return true,Prune(map<Y->X|fi,AllDefiningPolynomials(phi)>);
end function;


// ======================================
// = Auxillary functions (not exported) =
// ======================================

// test whether the map of case 3 is surjective
// --------------------------------------------
// input:  univariate polynomial 'p' and the map as polynomial sequence 'map'
// output: label "3a" or "3b"
function TestCase3(p, map)
	vprint Classify: "----------- Entering TestCase3 ------------";
	P := Parent(p); Q := BaseRing(P);
	
	// wrong dimension => case 3a
	if not #map eq 3 then
		vprint Classify: "----------- Leaving TestCase3 -------------";
		return "3a";
	end if;
	
	// otherwise test if dominant
	D := Scheme(ProjectiveSpace(Parent(p)), p);
	I := ProjectiveSpace(Q, 2);
	m := map<D -> I | map>;
	vprint Classify: "Testing for dominance...";
	if IsDominant(m) then
		vprint Classify: "----------- Leaving TestCase3 -------------";
		return "3b";
	else
		vprint Classify: "----------- Leaving TestCase3 -------------";
		return "3a";
	end if;
end function;

// compute image and inverse of a birational map
// ---------------------------------------------
// input:  a projective scheme 'X', and ambient projective space 'A'
//         and defining equations 'defpols' for a rational transformation
//         from 'X' into 'A'
// output: closure 'Y' of image of 'X' under transformation,
//         retricted map 'X-->Y' and inverse (if 'birational = true');
function ImageAndInverse(X, A, defpols : birational := false)
	m := map<X -> A | defpols>; Y := m(X);
	m := Restriction(m, X, Y : Check := false);
	
	// maybe invert a birational map
	if birational then
		_, mi := myInvertible(m);
		return Y, m, mi;
	else
		return Y, m;
	end if;
end function;


// crossmultiply generators
// ------------------------
// input:  the defining polynomial 'p',
//         a sequence 'seq' of sequences of forms
// output: all forms crossmultiplied and reduced modulo 'p'
function CrossMultiply(p, seq)
	res := seq[1];
	for k := 2 to #seq do
		raux := [];
		for j := 1 to #seq[k] do
			raux := raux cat [r*seq[k][j] : r in res];
		end for;
		raux := {NormalForm(r, [p]) : r in raux};
		res := [r : r in raux];
	end for;
	return res;
end function;


// find linearly independent element
// ---------------------------------
// input:  a set 'B' of generators for some space of forms (of degree 'd'),
//         another set 'D' of forms (also of degree 'd') containing a linearly
//         independent form
// output: an element of 'D' which is linearly independed from 'B'
function IndepElement(B, D)
	P := Universe(B); Q := BaseRing(P);
	
	// find a monomial basis
	basis := {};
	for f in (B cat D) do
		basis := basis join {LeadingMonomial(t) : t in Terms(f)};
	end for;
	basis := [b : b in basis];
	
	// rewrite as vectors and reduce to basis
	QV := KSpace(Q, #basis);
	Dvec := [QV ! [MonomialCoefficient(f, b) : b in basis] : f in D];
	Bvec := [QV ! [MonomialCoefficient(f, b) : b in basis] : f in B];
	space := sub<QV | Bvec>;
	
	// find a linearly independent new vector
	for j := 1 to #D do
		if not Dvec[j] in space then
			return D[j];
		end if;
	end for;
	
	// never reached for correct input!
	error "Could not find linearly independent form in 'D'!";
end function;

// isolated out the functionality of ClassifyProjectiveSurface so
// that ClassifyProjectiveSurface can return more meaningful data. 
// bufd is true to force a formal desingularization to be used if
// there is a choice between that and a blow-up desing. (the default)
function classify_proj_srfc(S, bufd)

	p := DefiningPolynomial(S);
	
	// 2nd plurigenus
	V02 := HomAdjoints(2, 0, S : UseFormalDesing := bufd);
	PG2 := #V02;
	
	// arithmetic genus
	V11 := HomAdjoints(1, 1, S : UseFormalDesing := bufd);
	V21 := HomAdjoints(1, 2, S : UseFormalDesing := bufd);
	AG := TotalDegree(p) + 2*#V11 - #V21 - 1;
	
	// case 0 (not rational) ?
	if not (PG2 eq 0 and AG eq 0) then
		return "0", [], "Not rational";
	end if;
	
	// compute mu
	V := []; i := 0; while true do
		V[i+1] := HomAdjoints(i, 1, S : UseFormalDesing :=bufd);
		if #(V[i+1]) eq 0 then
			mu := i-1; break;
		end if;
		i := i+1;
	end while;
	V1mu := V[mu+1];
	
	// case 1 ?
	if #V1mu eq 3 then
		V22mu := HomAdjoints(2*mu, 2, S : UseFormalDesing := bufd);
		if #V22mu eq 6 then
			return "1", [V1mu], "P^2";
		end if;
	end if;
	
	// case 2 ?
	V22muP := HomAdjoints(2*mu+1, 2, S : UseFormalDesing := bufd);
	if #V22muP eq 1 then
		return "2", [V1mu], "Quadric surface";
	end if;
	
	// case 3 ?
	if #V22muP gt 1 then
		type := TestCase3(p, V22muP);
		if type eq "3a" then
			return type, [V22muP, V1mu], "Rational scroll";
		else
			return type, [V22muP], "P^2";
		end if;
	end if;
	
	// case 4 ?
	if #V1mu gt 1 then
		V22muM := HomAdjoints(2*mu-1, 2, S : UseFormalDesing := bufd);
		return "4", [V1mu, V22muM], "Conic bundle";
	end if;
	
	// case 5A ?
	if mu gt 1 then
		V1muM := V[mu];
		if #V1muM gt 3 then
			return "5Aa", [V1muM], "Del Pezzo degree " cat 
					IntegerToString((#V1muM)-1);
		end if;
		V22muMM := HomAdjoints(2*mu-2, 2, S : UseFormalDesing := bufd);
		if #V1muM eq 3 then
			return "5Ab", [V1muM, V22muMM], "Del Pezzo degree 2";
		end if;
		V33muMMM := HomAdjoints(3*mu-3, 3, S : UseFormalDesing := bufd);
		return "5Ac", [V1muM, V22muMM, V33muMMM], "Del Pezzo degree 1";
	end if;
	
	// else: case 5B !
	return "5B", [V21], "Del Pezzo degree " cat IntegerToString((#V21)-1);

end function;


// ======================
// = Exported functions =
// ======================

// compute the class of the surface and nice adjoint maps
intrinsic ClassifyRationalSurface(S::Srfc : UseFormalDesing := false)
-> Srfc, List, MonStgElt
{
S should be a (generally singular) surface in P^3.
Classifies S into either not (geometrically) rational or rational and birationally
isomorphic to a rational surface Y of special type over the base field.
The first return value is S in the first case or Y in the second.
The second return value is a list of 1 or 2 maps. The first is a birational
map of S to itself or Y. There is only a second when Y is a
rational scroll or conic bundle, when the second map gives the
corresponding fibration map from S to a rational normal curve.
The third return value is a string that giving 
an English language description of the type of Y (e.g. "Del Pezzo degree >= 3")
or "Not rational". S should be defined over a number field or have only point
singularities.
A resolution of singularities, either of formal or blow-up type is needed here
and it is computed at the start if one has not already been stored for S. To force
the use of a formal desingularisation rather than a blow-up one (the default) in
the case where S has only point singularities and the base field is a number field,
set parameter UseFormalDesing to true. 
}
	P3 := Ambient(S);
	Q := BaseRing(S);
	require IsOrdinaryProjective(S) and Dimension(P3) eq 3:
	  "S must be a surface in ordinary projective 3-space";
	boo := (t cmpeq FldRat) or ISA(t,FldAlg) where t is Type(Q);
	require boo or (Dimension(SingularSubscheme(S)) le 0):
	  "S must be defined over a number field or have only point singularities";
	p := DefiningPolynomial(S);

	type,adjs,s2 := classify_proj_srfc(S,boo and UseFormalDesing);

	// case distinction
	if type eq "0" then
		// non-rational surfaces
		Y := S;
		mps := [* IdentityMap(S) *];
	elif type in {"1", "3b"} then
		Y := Surface(ProjectiveSpace(Q,2),[]); //just P2!
		mp := map<S->Y|adjs[1]>;
		mps := [* mp *];
	elif type eq "2" then
		Y,mp := ImageAndInverse(S, P3, adjs[1]);
		mps := [* mp *];
	elif type in {"3a", "4"} then
		Pn := ProjectiveSpace(Q,#adjs[1]-1);
		_, pencil := ImageAndInverse(S, Pn, adjs[1]);
		Y,mp := ImageAndInverse(S, ProjectiveSpace(Q,#adjs[2]-1), adjs[2]);
		mps := [* mp, pencil *];
	elif type in {"5Aa", "5Ab", "5Ac", "5B"} then
		space := adjs[1];
		forms := space; degs := [1 : p in forms];
		if type in {"5Ab", "5Ac"} then
			// add a polynomial from second adjoint space
			space := CrossMultiply(p, [space, adjs[1]]);
			elt := IndepElement(space, adjs[2]);
			Append(~space, elt);
			Append(~forms, elt);
			Append(~degs, 2);
		end if;
		if type eq "5Ac" then
			// add a polynomial from third adjoint space
			space := CrossMultiply(p, [space, adjs[1]]);
			elt := IndepElement(space, adjs[3]);
			Append(~space, elt);
			Append(~forms, elt);
			Append(~degs, 3);
		end if;
		// the Del Pezzo surface
		if type in {"5Ab", "5Ac"} then
			Pn := ProjectiveSpace(Q, degs);
		else
			Pn := ProjectiveSpace(Q, #degs-1);
		end if;
		Y, mp := ImageAndInverse(S, Pn, forms);
		mps := [* mp *];
	end if;

	return Y,mps,s2;
end intrinsic;

// try to parametrize surface
intrinsic ParametrizeProjectiveHypersurface(X::Srfc, P2::Prj
    : UseFormalDesing := false)
-> BoolElt, MapSch
{
Given a (generally singular) projective surface X in P^3 and a projective
plane P2 over Q. Return 'false' if the surface is not rational over Q, or 'true'
and a parametrization over Q.
A resolution of singularities, either of formal or blow-up type is needed here
and it is computed at the start if one has not already been stored for S. To force
the use of a formal desingularisation rather than a blow-up one (the default) in
the case where S has only point singularities,
set parameter UseFormalDesing to true.
}
	require IsOrdinaryProjective(X) and Dimension(Ambient(X)) eq 3:
	  "X must be a surface in ordinary projective 3-space";
	require IsOrdinaryProjective(P2) and Dimension(P2) eq 2:
	  "P2 must be an ordinary projective plane";
	require (Type(BaseRing(X)) cmpeq FldRat) and (Type(BaseRing(P2)) cmpeq FldRat):
	  "X and P2 must both be defined over the rational numbers";

	vprint Classify: "--- Entering ParametrizeProjectiveHypersurface ----";
	p := DefiningPolynomial(X); P3 := AmbientSpace(X);
	P := Parent(p); Q := BaseRing(P);
	
	// classify the surface
	vprint Classify: "Classifying...";
	type, adjs :=
	    classify_proj_srfc(X,UseFormalDesing);
	vprintf Classify: "Surface is of type %o.\n", type;
	
	// case distinction
	if type eq "0" then
		// non-rational surfaces
		ispara := false;
	else if type in {"1", "3b"} then
		vprint Classify: "Inverting...";
		_, _, param :=
		  ImageAndInverse(X, P2, adjs[1] : birational := true);
		ispara := true;
	else if type eq "2" then
		vprint Classify: "Transforming to quadric surface...";
		Y, _, mi :=
		  ImageAndInverse(X, P3, adjs[1] : birational := true);
		vprint Classify: "Parametrizing quadric surface...";
		ispara, param := ParametrizeQuadric(Y, P2);
		if ispara then param := Expand(param*mi); end if;
	else if type in {"3a", "4"} then
		vprint Classify: "Transforming to pencil...";
		// the pencil
		Pn := ProjectiveSpace(Q,#adjs[1]-1);
		Y, pencil := ImageAndInverse(X, Pn, adjs[1]);
		vprint Classify: "Parametrizing pencil...";
		ispara, param := ParametrizePencil(pencil, P2);
	else if type in {"5Aa", "5Ab", "5Ac", "5B"} then
		vprint Classify: "Transforming to Del Pezzo...";
		// start with polynomials in first adjoint space
		space := adjs[1];
		forms := space; degs := [1 : p in forms];
		if type in {"5Ab", "5Ac"} then
			// add a polynomial from second adjoint space
			space := CrossMultiply(p, [space, adjs[1]]);
			elt := IndepElement(space, adjs[2]);
			Append(~space, elt);
			Append(~forms, elt);
			Append(~degs, 2);
		end if;
		if type eq "5Ac" then
			// add a polynomial from third adjoint space
			space := CrossMultiply(p, [space, adjs[1]]);
			elt := IndepElement(space, adjs[3]);
			Append(~space, elt);
			Append(~forms, elt);
			Append(~degs, 3);
		end if;
		// the Del Pezzo surface
		if type in {"5Ab", "5Ac"} then
			Pn := ProjectiveSpace(Q, degs);
		else
			Pn := ProjectiveSpace(Q, #degs-1);
		end if;
		Y, m, mi :=
		  ImageAndInverse(X, Pn, forms : birational := true);
		vprint Classify: "Parametrizing Del Pezzo...";
		ispara, param := ParametrizeDelPezzo(Y, P2);
		if ispara then param := Expand(param*mi); end if;
	end if; end if; end if; end if; end if;
	
	vprint Classify: "---- Leaving ParametrizeProjectiveHypersurface ----";
	if ispara then
		return true, param;
	else
		return false, _;
	end if;
end intrinsic;


// try to parametrize surface
intrinsic ParametrizeProjectiveSurface(X::Srfc, P2::Prj)
-> BoolElt, MapSch
{
Given an ordinary projective surface X and a projective plane P2 over Q.
Return 'false' if the surface is not rational over Q, or 'true' and a
parametrization over Q.
}
	require IsOrdinaryProjective(X):
	  "X must be an ordinary projective surface";
	require IsOrdinaryProjective(P2) and Dimension(P2) eq 2:
	  "P2 must be an ordinary projective plane";
	require (Type(BaseRing(X)) cmpeq FldRat) and (Type(BaseRing(P2)) cmpeq FldRat):
	  "X and P2 must be both be defined over the rational numbers";

	A := AmbientSpace(X); P := CoordinateRing(A); Q := BaseRing(P);
	C := CoordinateRing(P2);
	
	// trivial situation?
	if Dimension(A) eq 2 then
		return true,
		    map<P2 -> X | [P.i : i in [1..3]], [C.i : i in [1..3]]>;
	end if;
	
	// are we already in hypersurface situation?
	if Dimension(A) eq 3 then
		return ParametrizeProjectiveHypersurface(X, P2);
	end if;
	
	// search for good projection
	P3 := ProjectiveSpace(Q, 3); LS := LinearSystem(A, 1);
	while true do
		// choose a projection
                // TO DO : using Random here is really stupid
                // (and it's not implemented over number fields)
		//sections := [Random(LS) : i in [1..4]];
		LS2 := LS; sections := [];
		for i in [1..4] do
			repeat sec := Random(LS2); until not sec eq 0;
			Append(~sections, sec);
			LS2 := Complement(LS2, LinearSystem(LS2,[sec]));
		end for;
		proj := map<X -> P3 | sections>;
		
		// test whether it is birational
		Y := Image(proj);
		proj := map<X -> Y | sections>;
		isbirat, inv := myInvertible(proj);
		if isbirat then break; end if;
	end while;
	
	// parametrize image
	ispara, param := ParametrizeProjectiveHypersurface(Y, P2);
	
	if ispara then
		return true, param*inv;
	else
		return false, _;
	end if;
end intrinsic;


// try to parametrize surface
intrinsic Solve(p::RngMPolElt, F::FldFunRat)
-> SeqEnum
{
Given a polynomial 'p' in three variables over 'Q' and a field 'F' of bivariate
rational functions over 'Q'. Return a sequence of triples '[X,Y,Z]' in 'F^3'
s.t. 'p(X,Y,Z) = 0' and s.t. the Jacobian of '[X,Y,Z]' has generically rank 2.
Moreover every other such parametrization is obtained by applying an
endomorphism of 'F'. (The function might also answer that the corresponding
surface type is not yet implemented. )
}
	P := Parent(p); Q := BaseRing(P);
	P1<x,y,z,w> := PolynomialRing(Q, 4);
	P2<U,V,W> := PolynomialRing(Q, 3);
	
	// factorize to split into finite number of subtasks
	facts := [f[1] : f in Factorization(p)];
	
	// try to parametrize each factor
	sols := [];
	for f in facts do
		// build projective surface
		ph := Homogenization(hom<P -> P1 | x, y, z>(f), w);
		X := Surface(ProjectiveSpace(P1), ph);
		
		// try to parametrize
		ispara, para := ParametrizeProjectiveHypersurface(X,
		    ProjectiveSpace(P2));
		if not ispara then continue; end if;
		
		// build solution
		dehom := [hom<P2 -> F | F.1, F.2, 1>(p) :
		          p in DefiningPolynomials(para)];
		Append(~sols, [dehom[i]/dehom[4] : i in [1..3]]);
	end for;
	
	return sols;
end intrinsic;
